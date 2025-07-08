//! Tree Node Module for PersistentVector
//!
//! Defines the Node type and related constants for the internal RRB-tree structure.
//!
use std::fmt::{self, Debug};
use std::sync::Arc;

// Only import what is needed for node.rs, now that memory-related types are defined in memory.rs
use crate::pvec::memory::{CHUNK_BITS, Chunk, DEFAULT_CHUNK_SIZE, ManagedRef, MemoryManager};
use crate::utils::error_utils::{AppError, error_with_context};

/// Standard error type for pvec node operations
pub(crate) type PVecError = AppError<String, String>;

/// The maximum number of children a node can have.
pub(crate) const NODE_SIZE: usize = DEFAULT_CHUNK_SIZE;
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

    /// Get an element at the specified index and record the path taken.
    ///
    /// Returns a reference to the element if it exists, and pushes the traversal path and ranges.
    pub(crate) fn get_with_path(
        &self, index: usize, shift: usize, path: &mut Vec<usize>,
        ranges: &mut Vec<std::ops::Range<usize>>,
    ) -> Option<&T> {
        match self {
            Node::Leaf { elements } => {
                path.push(index);
                ranges.push(0..elements.inner().len());
                elements.inner().get(index)
            },
            Node::Branch { children, sizes } => {
                let (child_index, sub_index) = self.find_child_index(index, shift).ok()?;
                path.push(child_index);
                if let Some(sizes) = sizes {
                    let start = if child_index == 0 {
                        0
                    } else {
                        sizes[child_index - 1]
                    };
                    let end = sizes[child_index];
                    ranges.push(start..end);
                } else {
                    let width = 1 << shift;
                    let start = child_index * width;
                    let end = start + width;
                    ranges.push(start..end);
                }
                if child_index < children.len() {
                    if let Some(child) = &children[child_index] {
                        return child.get_with_path(
                            sub_index,
                            shift.saturating_sub(NODE_BITS),
                            path,
                            ranges,
                        );
                    }
                }
                None
            },
        }
    }

    /// Get an element at the specified index using a pre-recorded path.
    ///
    /// This function uses a previously recorded path to directly navigate to an element,
    /// which can be more efficient than recalculating the path for repeated accesses.
    ///
    /// # Parameters
    ///
    /// * `index` - The absolute index to retrieve
    /// * `shift` - The current tree level shift value
    /// * `path` - Vector containing the path indices to follow
    /// * `ranges` - Vector containing ranges for validation
    ///
    /// # Returns
    ///
    /// A reference to the element if it exists
    pub(crate) fn get_by_path(
        &self, _index: usize, shift: usize, path: &[usize], _ranges: &[std::ops::Range<usize>],
    ) -> Option<&T> {
        if path.is_empty() {
            return None;
        }
        match self {
            Node::Leaf { elements } => elements.inner().get(path[0]),
            Node::Branch { children, .. } => {
                let child_index = path[0];
                if child_index < children.len() {
                    if let Some(child) = &children[child_index] {
                        if path.len() > 1 {
                            child.get_by_path(
                                _index,
                                shift.saturating_sub(NODE_BITS),
                                &path[1..],
                                if _ranges.len() > 1 {
                                    &_ranges[1..]
                                } else {
                                    &[]
                                },
                            )
                        } else {
                            None // Path too short
                        }
                    } else {
                        None // Child is None
                    }
                } else {
                    None // Child index out of bounds
                }
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
                format!("index: {index}, shift: {shift}"),
            )),
        }
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
                let mut new_children = Vec::with_capacity(children.len());
                for child in children.iter() {
                    new_children.push(child.clone());
                }
                let mut new_sizes = sizes.clone();
                modifier(&mut new_children, &mut new_sizes);
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
                let old_size = children[child_index]
                    .as_ref()
                    .map_or(0, |child| child.size());
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
        &self, manager: &MemoryManager<T>, index: usize, value: T, shift: usize,
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

                Some(manager.allocate_node(Node::Leaf {
                    elements: new_elements,
                }))
            },
            Node::Branch { children, sizes: _ } => {
                let (child_index, sub_index) = self.find_child_index(index, shift).ok()?;

                if child_index >= children.len() || children[child_index].is_none() {
                    return None;
                }

                let child = &children[child_index].as_ref().unwrap();

                // Recursive update with reduced shift
                match child.update(manager, sub_index, value, shift - NODE_BITS) {
                    Some(new_child) => {
                        // Only create a new branch if the child actually changed
                        if Arc::ptr_eq(child.inner(), new_child.inner()) {
                            Some(manager.allocate_node(self.clone()))
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
    /// * `chunk_size` - The size of the chunk to use for new nodes
    /// * `manager` - The MemoryManager to use for node and chunk allocations
    ///
    /// # Returns
    ///
    /// A tuple containing:
    /// - A new node with the element added
    /// - A boolean indicating whether the node was split (true) or not (false)
    /// - The overflow node if a split occurred, otherwise None
    #[inline(always)]
    pub(crate) fn push_back(
        &self, value: T, _shift: usize, chunk_size: usize, manager: &MemoryManager<T>,
    ) -> PushResult<T> {
        match self {
            Node::Leaf { elements } => {
                if elements.inner().len() < chunk_size {
                    let modified_elements = Self::modify_chunk(elements, |chunk| {
                        chunk.push_back(value);
                    });
                    let new_node = manager.allocate_node(Node::Leaf {
                        elements: modified_elements,
                    });
                    (new_node, false, None)
                } else {
                    let mut new_chunk = Chunk::new_with_size(chunk_size);
                    new_chunk.push_back(value);
                    let overflow = manager.allocate_node(Node::Leaf {
                        elements: manager.allocate_chunk(new_chunk),
                    });
                    let new_node = manager.allocate_node(Node::Leaf {
                        elements: elements.clone(),
                    });
                    (new_node, true, Some(overflow))
                }
            },
            Node::Branch { children, sizes: _ } => {
                if children.is_empty() {
                    let mut new_chunk = Chunk::new_with_size(chunk_size);
                    new_chunk.push_back(value);
                    let new_node = manager.allocate_node(Node::Leaf {
                        elements: manager.allocate_chunk(new_chunk),
                    });
                    (new_node, false, None)
                } else {
                    let last_idx = children.len() - 1;
                    if let Some(last_child) = &children[last_idx] {
                        let (new_child, split, overflow) =
                            last_child.push_back(value, _shift - NODE_BITS, chunk_size, manager);
                        let new_node = self.replace_child(last_idx, new_child);
                        if !split {
                            return (
                                new_node.expect("Failed to create new node during push_back"),
                                false,
                                None,
                            );
                        }
                        if children.len() < NODE_SIZE {
                            let new_node = new_node
                                .expect("Failed to create new node during push_back")
                                .modify_branch(|children, sizes| {
                                    children.push(overflow.clone());
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
                            (
                                new_node.expect("Failed to create new node during push_back"),
                                true,
                                overflow,
                            )
                        }
                    } else {
                        let mut new_chunk = Chunk::new_with_size(chunk_size);
                        new_chunk.push_back(value);
                        let leaf_node = manager.allocate_node(Node::Leaf {
                            elements: manager.allocate_chunk(new_chunk),
                        });
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
    /// * `manager` - The MemoryManager to use for node allocations
    ///
    /// # Returns
    ///
    /// A tuple containing:
    /// - The left part of the node (elements before index)
    /// - The right part of the node (elements from index onward)
    ///
    /// # Errors
    ///
    /// Returns an error if the split cannot be performed.
    pub(crate) fn split(
        &self, index: usize, shift: usize, manager: &MemoryManager<T>,
    ) -> NodePairResult<T> {
        match self {
            Node::Leaf { elements } => {
                let total = elements.inner().len();
                if index > total {
                    return Err(error_with_context(
                        format!("split index {index} out of bounds for leaf of size {total}"),
                        String::new(),
                    ));
                }
                // Defensive: if splitting at 0 or at total, return empty and full accordingly
                let left_chunk = manager.allocate_chunk({
                    let mut c = Chunk::new_with_size(elements.inner().len());
                    for i in 0..index {
                        if let Some(val) = elements.inner().get(i) {
                            c.push_back(val.clone());
                        }
                    }
                    c
                });
                let right_chunk = manager.allocate_chunk({
                    let mut c = Chunk::new_with_size(elements.inner().len());
                    for i in index..total {
                        if let Some(val) = elements.inner().get(i) {
                            c.push_back(val.clone());
                        }
                    }
                    c
                });
                let left_node = manager.allocate_node(Node::Leaf {
                    elements: left_chunk,
                });
                let right_node = manager.allocate_node(Node::Leaf {
                    elements: right_chunk,
                });
                Ok((left_node, right_node))
            },
            Node::Branch { children, sizes } => {
                // (existing branch splitting logic unchanged)
                if index == 0 {
                    let empty = manager.allocate_node(Node::Branch {
                        children: Vec::new(),
                        sizes: Some(Vec::new()),
                    });
                    let node = manager.allocate_node(Node::Branch {
                        children: children.clone(),
                        sizes: sizes.clone(),
                    });
                    return Ok((empty, node));
                } else if index >= self.size() {
                    let node = manager.allocate_node(Node::Branch {
                        children: children.clone(),
                        sizes: sizes.clone(),
                    });
                    let empty = manager.allocate_node(Node::Branch {
                        children: Vec::new(),
                        sizes: Some(Vec::new()),
                    });
                    return Ok((node, empty));
                }
                // (rest of branch splitting logic unchanged)
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
                let (child_left, child_right) =
                    child.split(sub_index, shift - NODE_BITS, manager)?;
                let mut left_children = Vec::with_capacity(child_index + 1);
                for child in children.iter().take(child_index) {
                    left_children.push(child.clone());
                }
                left_children.push(Some(child_left.clone()));
                let left_sizes = if let Some(sizes) = sizes {
                    let mut left_size_table = Vec::with_capacity(child_index + 1);
                    left_size_table.extend_from_slice(&sizes[..child_index]);
                    let prev_size = if child_index > 0 {
                        sizes[child_index - 1]
                    } else {
                        0
                    };
                    left_size_table.push(prev_size + child_left.size());
                    Some(left_size_table)
                } else {
                    Some(Self::build_size_table(&left_children))
                };
                let mut right_children = Vec::with_capacity(children.len() - child_index);
                right_children.push(Some(child_right.clone()));
                for child in children.iter().skip(child_index + 1) {
                    right_children.push(child.clone());
                }
                let right_sizes = Some(Self::build_size_table(&right_children));
                let left_node = manager.allocate_node(Node::Branch {
                    children: left_children,
                    sizes: left_sizes,
                });
                let right_node = manager.allocate_node(Node::Branch {
                    children: right_children,
                    sizes: right_sizes,
                });
                Ok((left_node, right_node))
            },
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
