//! Tree Node Module
//!
//! This module defines the Node type, which is the building block
//! for the internal tree structure of the persistent vector.
//!
//! # Overview
//!
//! The node module implements a relaxed radix balanced (RRB) tree structure
//! that forms the backbone of the persistent vector. Nodes can be either:
//!
//! - **Leaf nodes**: Store elements directly in chunks
//! - **Branch nodes**: Store references to child nodes
//!
//! The tree structure supports both regular nodes (with uniform child sizes)
//! and relaxed nodes (with a size table for non-uniform children).

use std::fmt::{self, Debug};
use std::sync::Arc;

use crate::pvec::chunk::{Chunk, CHUNK_BITS, CHUNK_SIZE};
use crate::pvec::memory::{ManagedRef, MemoryManager};
use crate::utils::error_utils::{error_with_context, AppError};

/// Standard error type for pvec node operations
pub(crate) type PVecError = AppError<String, String>;

/// The maximum number of children a node can have.
pub(crate) const NODE_SIZE: usize = CHUNK_SIZE;

/// Bit mask for extracting the index within a node.
pub(crate) const NODE_MASK: usize = NODE_SIZE - 1;

/// The number of bits needed to represent indices within a node.
pub(crate) const NODE_BITS: usize = CHUNK_BITS;

/// Type alias for the push operation result, which includes:
/// - A reference to the new node
/// - A boolean indicating if the node was split
/// - Optionally, a reference to the overflow node if a split occurred
pub(crate) type PushResult<T> = (ManagedRef<Node<T>>, bool, Option<ManagedRef<Node<T>>>);

/// Type alias for the result of a node pair operation
pub(crate) type NodePairResult<T> = Result<(ManagedRef<Node<T>>, ManagedRef<Node<T>>), PVecError>;

/// A node in the RRB tree.
///
/// Nodes can be either:
/// - Internal nodes (Branch): containing references to child nodes
/// - Leaf nodes: directly storing values in a chunk
///
/// The tree structure supports both regular nodes (with uniform child sizes)
/// and relaxed nodes (with a size table for non-uniform children).
#[derive(Clone)]
pub(crate) enum Node<T> {
    /// An internal node containing references to child nodes
    Branch {
        /// Child nodes, stored as optional references to allow for sparse trees
        children: Vec<Option<ManagedRef<Node<T>>>>,

        /// Optional size table for relaxed nodes
        /// - When Some: Contains cumulative sizes for efficient indexing in relaxed trees
        /// - When None: The node is a regular (non-relaxed) node with uniform children
        sizes: Option<Vec<usize>>,
    },

    /// A leaf node containing elements directly in a chunk
    Leaf {
        /// The elements in this leaf node, stored in a managed reference to a chunk
        elements: ManagedRef<Chunk<T>>,
    },
}

impl<T: PartialEq> PartialEq for Node<T> {
    #[inline(always)]
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (
                Node::Branch {
                    children: self_children,
                    sizes: self_sizes,
                },
                Node::Branch {
                    children: other_children,
                    sizes: other_sizes,
                },
            ) => self_children == other_children && self_sizes == other_sizes,
            (
                Node::Leaf {
                    elements: self_elements,
                },
                Node::Leaf {
                    elements: other_elements,
                },
            ) => {
                // Compare the chunks by dereferencing them to get at the inner values
                **self_elements.inner() == **other_elements.inner()
            },
            _ => false,
        }
    }
}

impl<T: Clone + Eq> Eq for Node<T> {}

impl<T: Clone> Default for Node<T> {
    #[inline(always)]
    fn default() -> Self {
        Self::new()
    }
}

impl<T: Clone> Node<T> {
    /// Create a new empty branch node.
    ///
    /// This creates a non-relaxed branch node with no children and a capacity
    /// for NODE_SIZE children. The node is initialized with an empty children
    /// vector and no size table.
    ///
    /// # Returns
    ///
    /// A new empty branch node
    #[inline(always)]
    #[must_use]
    pub(crate) fn new() -> Self {
        Node::Branch {
            children: Vec::with_capacity(NODE_SIZE),
            sizes: None,
        }
    }

    /// Create a new leaf node from a chunk of elements.
    ///
    /// This creates a leaf node that directly stores elements in the provided chunk.
    /// Leaf nodes are always at the bottom of the tree and contain the actual data.
    ///
    /// # Arguments
    ///
    /// * `chunk` - A managed reference to a chunk containing the elements
    ///
    /// # Returns
    ///
    /// A new leaf node containing the provided chunk
    #[inline(always)]
    #[must_use]
    pub(crate) fn leaf(chunk: ManagedRef<Chunk<T>>) -> Self {
        Node::Leaf { elements: chunk }
    }

    /// Get the total number of elements contained in this node and its descendants.
    ///
    /// For leaf nodes, this returns the number of elements in the chunk.
    /// For branch nodes with a size table (relaxed nodes), this returns the last
    /// cumulative size value.
    /// For regular branch nodes without a size table, this calculates the sum of
    /// all child node sizes.
    ///
    /// # Returns
    ///
    /// * `usize` - The total number of elements in this node and its descendants
    #[inline(always)]
    #[must_use]
    pub(crate) fn size(&self) -> usize {
        match self {
            Node::Leaf { elements } => elements.inner().len(),
            Node::Branch { children, sizes } => {
                // If we have a size table, use the last entry
                if let Some(sizes) = sizes {
                    return sizes.last().copied().unwrap_or(0);
                }

                // For regular nodes, calculate the size based on children
                children.iter().flatten().map(|child| child.size()).sum()
            },
        }
    }

    /// Find the child index and sub-index in a relaxed node's size table using binary search.
    ///
    /// This function performs a binary search on the size table to find which child
    /// contains the given index, and calculates the relative index within that child.
    ///
    /// # Parameters
    ///
    /// * `sizes` - The size table containing cumulative sizes of children
    /// * `index` - The absolute index to locate
    ///
    /// # Returns
    ///
    /// A tuple containing:
    /// * The index of the child that contains the target element
    /// * The relative index within that child
    #[inline(always)]
    #[must_use]
    fn find_index_in_size_table(&self, sizes: &[usize], index: usize) -> (usize, usize) {
        // Search the size table directly to find which child contains the index
        let mut child_idx = 0;
        let mut prev_size = 0;

        // Check the cumulative size of each child to determine which one contains the index
        for (i, &size) in sizes.iter().enumerate() {
            if index < size {
                child_idx = i;
                break;
            }
            prev_size = size;
        }

        // Handle the case where the index is in the last child
        if index >= *sizes.last().unwrap_or(&0) {
            child_idx = sizes.len() - 1;
            prev_size = if child_idx > 0 {
                sizes[child_idx - 1]
            } else {
                0
            };
        }

        let sub_index = index - prev_size;
        (child_idx, sub_index)
    }

    /// Find the child index and sub-index in a branch node using bit operations or size table.
    ///
    /// This function calculates the child index and sub-index based on the node type:
    /// - For relaxed nodes, it uses a size table for binary search.
    /// - For regular nodes, it uses bit operations to find the child and sub-index.
    ///
    /// # Parameters
    ///
    /// * `index` - The absolute index to locate
    /// * `shift` - The shift value for bit operations (only used for regular nodes)
    ///
    /// # Returns
    ///
    /// A tuple containing:
    /// * The index of the child that contains the target element
    /// * The relative index within that child
    ///
    /// # Errors
    ///
    /// Returns an error if called on a non-branch node.
    #[inline(always)]
    pub(crate) fn find_child_index(
        &self, index: usize, shift: usize,
    ) -> Result<(usize, usize), PVecError> {
        match self {
            Node::Branch { sizes, .. } => {
                if let Some(sizes) = sizes {
                    Ok(self.find_index_in_size_table(sizes, index))
                } else {
                    let mask = (1 << shift) - 1;
                    let child_index = (index >> shift) & NODE_MASK;
                    let sub_index = index & mask;
                    Ok((child_index, sub_index))
                }
            },
            _ => Err(error_with_context(
                "find_child_index called on a non-branch node".to_string(),
                format!("index: {}, shift: {}", index, shift),
            )),
        }
    }

    /// Create a new node with a custom initializer function.
    ///
    /// This helper function creates a new node and applies the provided creator function to initialize it.
    ///
    /// # Parameters
    ///
    /// * `creator` - A function that initializes the newly created node
    ///
    /// # Returns
    ///
    /// A managed reference to the newly created node
    #[inline(always)]
    #[must_use]
    pub(crate) fn create_node<F>(creator: F) -> ManagedRef<Node<T>>
    where
        F: FnOnce(&mut Node<T>),
    {
        // 1. Node<T> 기본 생성
        let mut node = Node::new();
        // 2. modifier 적용
        creator(&mut node);
        // 3. Arc로 감싸서 ManagedRef로 반환
        ManagedRef::new(Arc::new(node))
    }

    /// Create a new branch node with the given children and sizes.
    ///
    /// This function creates a new branch node by initializing it with the provided children and sizes.
    ///
    /// # Parameters
    ///
    /// * `children` - A vector of optional managed references to child nodes
    /// * `sizes` - An optional vector of cumulative sizes of children
    ///
    /// # Returns
    ///
    /// A managed reference to the newly created branch node
    #[inline(always)]
    #[must_use]
    pub(crate) fn create_branch_node(
        &self, children: Vec<Option<ManagedRef<Node<T>>>>, sizes: Option<Vec<usize>>,
    ) -> ManagedRef<Node<T>> {
        Self::create_node(|node| {
            *node = Node::Branch { children, sizes };
        })
    }

    /// Create a new leaf node with the given elements.
    ///
    /// This function creates a new leaf node by initializing it with the provided elements.
    ///
    /// # Parameters
    ///
    /// * `elements` - A managed reference to a chunk of elements
    ///
    /// # Returns
    ///
    /// A managed reference to the newly created leaf node
    #[inline(always)]
    #[must_use]
    pub(crate) fn create_leaf_node(elements: ManagedRef<Chunk<T>>) -> ManagedRef<Node<T>> {
        Self::create_node(|node| {
            *node = Node::Leaf { elements };
        })
    }

    /// Build a size table for the given children.
    ///
    /// This function creates a size table by iterating over the children and summing their sizes.
    ///
    /// # Parameters
    ///
    /// * `children` - A slice of optional managed references to child nodes
    ///
    /// # Returns
    ///
    /// A vector containing the cumulative sizes of the children
    #[inline(always)]
    #[must_use]
    fn build_size_table(children: &[Option<ManagedRef<Node<T>>>]) -> Vec<usize> {
        let mut size_table = Vec::with_capacity(children.len());
        let mut cumulative_size = 0;

        for child_option in children.iter() {
            if let Some(child) = child_option {
                cumulative_size += child.size();
            }

            // Only add to size_table if we have at least one child already
            // or if the current child exists
            if !size_table.is_empty() || child_option.is_some() {
                size_table.push(cumulative_size);
            }
        }

        size_table
    }

    /// Modify a chunk of elements in place.
    ///
    /// This function modifies a chunk of elements by cloning the chunk and applying the given modifier function.
    ///
    /// # Parameters
    ///
    /// * `chunk` - A managed reference to a chunk of elements
    /// * `modifier` - A function that takes a mutable reference to the chunk and applies modifications
    ///
    /// # Returns
    ///
    /// A managed reference to the modified chunk
    #[inline(always)]
    #[must_use]
    pub(crate) fn modify_chunk<F>(chunk: &ManagedRef<Chunk<T>>, modifier: F) -> ManagedRef<Chunk<T>>
    where
        F: FnOnce(&mut Chunk<T>),
    {
        // 1. Chunk 복제
        let mut cloned_chunk = (**chunk.inner()).clone();
        // 2. modifier 적용
        modifier(&mut cloned_chunk);
        // 3. Arc로 감싸서 ManagedRef로 반환
        ManagedRef::new(Arc::new(cloned_chunk))
    }

    /// Modify a branch node in place.
    ///
    /// This function modifies a branch node by creating a mutable reference
    /// and applying the given modifier function.
    ///
    /// # Parameters
    ///
    /// * `modifier` - A function that takes a mutable reference to the branch node and applies modifications
    ///
    /// # Returns
    ///
    /// A managed reference to the modified branch node
    ///
    /// # Errors
    ///
    /// Returns an error if called on a non-branch node.
    #[inline(always)]
    pub(crate) fn modify_branch<F>(&self, modifier: F) -> Result<ManagedRef<Node<T>>, PVecError>
    where
        F: FnOnce(&mut Vec<Option<ManagedRef<Node<T>>>>, &mut Option<Vec<usize>>),
    {
        match self {
            Node::Branch { children, sizes } => {
                // 복사본 생성
                let mut new_children = children.clone();
                let mut new_sizes = sizes.clone();
                // modifier 적용
                modifier(&mut new_children, &mut new_sizes);
                // Arc로 감싸서 ManagedRef로 반환
                Ok(ManagedRef::new(Arc::new(Node::Branch {
                    children: new_children,
                    sizes: new_sizes,
                })))
            },
            _ => Err(error_with_context(
                "modify_branch called on non-branch node".to_string(),
                String::new(),
            )),
        }
    }

    /// Replace a child node in the branch node.
    ///
    /// This function replaces a child node in the branch node by creating a mutable reference
    /// and applying the given modifier function.
    ///
    /// # Parameters
    ///
    /// * `child_index` - The index of the child node to replace
    /// * `new_child` - A managed reference to the new child node
    ///
    /// # Returns
    ///
    /// A managed reference to the modified branch node
    #[inline(always)]
    fn replace_child(
        &self, child_index: usize, new_child: ManagedRef<Node<T>>,
    ) -> Result<ManagedRef<Node<T>>, PVecError> {
        self.modify_branch(|children, sizes| {
            if child_index < children.len() {
                let old_size = children[child_index].as_ref().map_or(0, |child| child.size());
                let size_diff = new_child.size() as isize - old_size as isize;

                // Replace the child node
                children[child_index] = Some(new_child);

                // Update size table if it exists
                if let Some(size_table) = sizes {
                    for size in size_table.iter_mut().skip(child_index) {
                        *size = (*size as isize + size_diff) as usize;
                    }
                }
            }
        })
    }

    /// Get an element at the specified index.
    ///
    /// Returns a reference to the element if it exists, or `None` if the index is out of bounds.
    ///
    /// # Parameters
    ///
    /// * `index` - The index of the element to retrieve
    /// * `shift` - The level in the tree (shift amount in bits)
    #[inline(always)]
    pub(crate) fn get(&self, index: usize, shift: usize) -> Option<&T> {
        match self {
            Node::Leaf { elements } => elements.inner().get(index),
            Node::Branch { children, sizes: _ } => {
                let (child_index, sub_index) = self.find_child_index(index, shift).ok()?;

                if child_index < children.len() {
                    if let Some(child) = &children[child_index] {
                        return child.get(sub_index, shift.saturating_sub(NODE_BITS));
                    }
                }

                None
            },
        }
    }

    /// Update an element at the specified index, returning a new node.
    ///
    /// Returns None if the index is out of bounds.
    ///
    /// # Parameters
    ///
    /// * `index` - The index of the element to update
    /// * `value` - The new value for the element
    /// * `shift` - The level in the tree (shift amount in bits)
    #[inline(always)]
    pub(crate) fn update(
        &self, _manager: &MemoryManager<T>, index: usize, value: T, shift: usize,
    ) -> Option<ManagedRef<Node<T>>> {
        match self {
            Node::Leaf { elements } => {
                if index >= elements.inner().len() {
                    return None;
                }

                // Create a new chunk only if needed
                let new_elements = Self::modify_chunk(elements, |chunk| {
                    if let Some(elem) = chunk.get_mut(index) {
                        *elem = value;
                    }
                });

                Some(Self::create_leaf_node(new_elements))
            },
            Node::Branch { children, sizes: _ } => {
                let (child_index, sub_index) = self.find_child_index(index, shift).ok()?;

                if child_index >= children.len() || children[child_index].is_none() {
                    return None;
                }

                let child = &children[child_index].as_ref().unwrap();

                // Recursive update with reduced shift
                match child.update(_manager, sub_index, value, shift - NODE_BITS) {
                    Some(new_child) => {
                        // Only create a new branch if the child actually changed
                        if Arc::ptr_eq(child.inner(), new_child.inner()) {
                            Some(ManagedRef::new(std::sync::Arc::new(self.clone())))
                        } else {
                            self.replace_child(child_index, new_child).ok()
                        }
                    },
                    None => None,
                }
            },
        }
    }

    /// Push a new element to the end of this node.
    ///
    /// This method creates a new node with the element added to the end.
    /// If the node is already at capacity, it will split and create an overflow node.
    ///
    /// # Parameters
    ///
    /// * `value` - The value to add to the node
    /// * `shift` - The current tree level shift value
    ///
    /// # Returns
    ///
    /// A tuple containing:
    /// - A new node with the element added
    /// - A boolean indicating whether the node was split (true) or not (false)
    /// - The overflow node if a split occurred, otherwise None
    #[inline(always)]
    pub(crate) fn push_back(&self, value: T, _shift: usize) -> PushResult<T> {
        match self {
            Node::Leaf { elements } => {
                if elements.inner().len() < CHUNK_SIZE {
                    // There's space in the leaf node, add the element
                    let modified_elements = Self::modify_chunk(elements, |chunk| {
                        chunk.push_back(value);
                    });

                    let new_node = Self::create_leaf_node(modified_elements);
                    (new_node, false, None)
                } else {
                    // Leaf node is full, create overflow node with the new element
                    let mut new_chunk = Chunk::new();
                    new_chunk.push_back(value);
                    let overflow = Self::create_leaf_node(ManagedRef::new(Arc::new(new_chunk)));

                    // Clone the existing leaf node
                    let new_node = Self::create_leaf_node(elements.clone());

                    (new_node, true, Some(overflow))
                }
            },
            Node::Branch { children, sizes: _ } => {
                if children.is_empty() {
                    // Empty branch node, create a leaf node instead
                    let mut new_chunk = Chunk::new();
                    new_chunk.push_back(value);
                    let new_node = Self::create_leaf_node(ManagedRef::new(Arc::new(new_chunk)));
                    (new_node, false, None)
                } else {
                    // Find the last child to push into
                    let last_idx = children.len() - 1;

                    if let Some(last_child) = &children[last_idx] {
                        // Push to the last child
                        let (new_child, split, overflow) =
                            last_child.push_back(value, _shift - NODE_BITS);

                        // Replace the last child with the new one
                        let new_node = self.replace_child(last_idx, new_child);

                        if !split {
                            return (
                                new_node.expect("Failed to create new node during push_back"),
                                false,
                                None,
                            );
                        }

                        // Handle overflow by adding it as a new child if there's space
                        if children.len() < NODE_SIZE {
                            let new_node = new_node
                                .expect("Failed to create new node during push_back")
                                .modify_branch(|children, sizes| {
                                    children.push(overflow.clone());

                                    // Update size table if this is a relaxed node
                                    if let Some(size_table) = sizes {
                                        let overflow_size = overflow.as_ref().unwrap().size();
                                        size_table
                                            .push(size_table.last().unwrap_or(&0) + overflow_size);
                                    }
                                });
                            (
                                new_node.expect("Failed to create new node during push_back"),
                                false,
                                None,
                            )
                        } else {
                            // Branch node is full, split needed at this level too
                            (
                                new_node.expect("Failed to create new node during push_back"),
                                true,
                                overflow,
                            )
                        }
                    } else {
                        // Last child is None, replace with a new leaf node
                        let mut new_chunk = Chunk::new();
                        new_chunk.push_back(value);
                        let leaf_node =
                            Self::create_leaf_node(ManagedRef::new(Arc::new(new_chunk)));

                        let new_node = self.replace_child(last_idx, leaf_node);
                        (
                            new_node.expect("Failed to create new node during push_back"),
                            false,
                            None,
                        )
                    }
                }
            },
        }
    }

    /// Split this node at the given index, returning left and right parts.
    ///
    /// This method divides a node into two parts at the specified index.
    /// The left part contains elements with indices 0 to index-1, and
    /// the right part contains elements with indices index to the end.
    ///
    /// # Parameters
    ///
    /// * `index` - The index at which to split the node
    /// * `shift` - The current tree level shift value
    ///
    /// # Returns
    ///
    /// A tuple containing:
    /// - The left part of the node (elements before index)
    /// - The right part of the node (elements at and after index)
    ///
    /// # Errors
    ///
    /// Returns an error if the node is not a branch node or if the index is out of bounds.
    #[inline(always)]
    pub(crate) fn split(&self, index: usize, shift: usize) -> NodePairResult<T> {
        match self {
            Node::Branch { children, sizes } => {
                if index == 0 {
                    // Split before the first element (left is empty)
                    let empty = self.create_branch_node(Vec::new(), Some(Vec::new()));
                    let node = self.create_branch_node(children.clone(), sizes.clone());
                    Ok((empty, node))
                } else if index >= self.size() {
                    // Split after the last element (right is empty)
                    let node = self.create_branch_node(children.clone(), sizes.clone());
                    let empty = self.create_branch_node(Vec::new(), Some(Vec::new()));
                    Ok((node, empty))
                } else {
                    // Find the child node containing the split point
                    let (child_index, sub_index) = self.find_child_index(index, shift)?;

                    if child_index >= children.len() || children[child_index].is_none() {
                        return Err(error_with_context(
                            "Invalid tree structure in split operation".to_string(),
                            format!(
                                "child_index: {}, children.len(): {}",
                                child_index,
                                children.len()
                            ),
                        ));
                    }

                    let child = children[child_index].as_ref().unwrap();

                    // Split the child node
                    let (child_left, child_right) = child.split(sub_index, shift - NODE_BITS)?;

                    // Create left branch (children up to child_index + child_left)
                    let mut left_children = Vec::with_capacity(child_index + 1);
                    for child in children.iter().take(child_index) {
                        left_children.push(child.clone());
                    }
                    left_children.push(Some(child_left.clone()));

                    // Create size table for left node
                    let left_sizes = if let Some(sizes) = sizes {
                        // Use existing size table
                        let mut left_size_table = Vec::with_capacity(child_index + 1);

                        // Copy sizes of children before the split
                        left_size_table.extend_from_slice(&sizes[..child_index]);

                        // Add size of the left part of the split child
                        let prev_size = if child_index > 0 {
                            sizes[child_index - 1]
                        } else {
                            0
                        };
                        left_size_table.push(prev_size + child_left.size());

                        Some(left_size_table)
                    } else {
                        // Calculate new size table
                        Some(Self::build_size_table(&left_children))
                    };

                    // Create right branch (child_right + remaining children)
                    let mut right_children = Vec::with_capacity(children.len() - child_index);
                    right_children.push(Some(child_right.clone()));

                    for child in children.iter().skip(child_index + 1) {
                        right_children.push(child.clone());
                    }

                    // Create size table for right node
                    let right_sizes = Some(Self::build_size_table(&right_children));

                    // Create left and right branch nodes
                    let left_node = self.create_branch_node(left_children, left_sizes);
                    let right_node = self.create_branch_node(right_children, right_sizes);

                    Ok((left_node, right_node))
                }
            },
            _ => Err(error_with_context(
                "split called on non-branch node".to_string(),
                format!("index: {}, shift: {}", index, shift),
            )),
        }
    }
}

impl<T: Clone> Node<T> {}

impl<T: Clone + Debug> Debug for Node<T> {
    #[inline(always)]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Node::Leaf { elements } => f.debug_tuple("Leaf").field(elements).finish(),
            Node::Branch { children, sizes } => f
                .debug_struct("Branch")
                .field("children", children)
                .field("sizes", sizes)
                .finish(),
        }
    }
}
