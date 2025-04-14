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
//!
//! # Example
//!
//! ```
//! use rustica::pvec::node::Node;
//! use rustica::pvec::memory::MemoryManager;
//!
//! // Create a memory manager
//! let manager = MemoryManager::<i32>::default();
//!
//! // Create a leaf node with some elements
//! let mut chunk = manager.acquire_chunk();
//! chunk.get_mut().unwrap().push_back(10);
//! chunk.get_mut().unwrap().push_back(20);
//! let node = Node::leaf(chunk);
//!
//! // Access elements
//! assert_eq!(*node.get(0, 0).unwrap(), 10);
//! assert_eq!(*node.get(1, 0).unwrap(), 20);
//!
//! // Add an element
//! let (new_node, _, _) = node.push_back(&manager, 30, 0);
//! assert_eq!(new_node.size(), 3);
//! ```

use std::fmt::{self, Debug};
use std::sync::Arc;

use crate::pvec::chunk::{Chunk, CHUNK_BITS, CHUNK_SIZE};
use crate::pvec::memory::{ManagedRef, MemoryManager};

/// The maximum number of children a node can have.
pub const NODE_SIZE: usize = CHUNK_SIZE;

/// Bit mask for extracting the index within a node.
pub const NODE_MASK: usize = NODE_SIZE - 1;

/// The number of bits needed to represent indices within a node.
pub const NODE_BITS: usize = CHUNK_BITS;

/// Number of bits per level in the RRB tree
pub const NODE_BITS_LEVEL: usize = 5;

/// Maximum number of elements at each level of the tree
pub const NODE_SIZE_LEVEL: usize = 1 << NODE_BITS_LEVEL;

/// Mask for extracting the lowest NODE_BITS bits
pub const NODE_MASK_LEVEL: usize = NODE_SIZE_LEVEL - 1;

/// Type alias for the push operation result, which includes:
/// - A reference to the new node
/// - A boolean indicating if the node was split
/// - Optionally, a reference to the overflow node if a split occurred
pub type PushResult<T> = (ManagedRef<Node<T>>, bool, Option<ManagedRef<Node<T>>>);

/// Type alias for the pop operation result, which includes:
/// - A reference to the new node
/// - Optionally, the popped element
pub type PopResult<T> = (ManagedRef<Node<T>>, Option<T>);

/// A node in the RRB tree.
///
/// Nodes can be either:
/// - Internal nodes (Branch): containing references to child nodes
/// - Leaf nodes: directly storing values in a chunk
///
/// The tree structure supports both regular nodes (with uniform child sizes)
/// and relaxed nodes (with a size table for non-uniform children).
#[derive(Clone)]
pub enum Node<T: Clone> {
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

impl<T: Clone + Eq> Eq for Node<T> {}

impl<T: Clone + PartialEq> PartialEq for Node<T> {
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
                **self_elements == **other_elements
            },
            _ => false,
        }
    }
}

/// Operations for manipulating nodes in the persistent vector tree structure
trait NodeOps<T>
where
    T: Clone,
{
    /// Modifies a node by creating a new copy with the changes applied
    ///
    /// # Parameters
    ///
    /// * `manager` - The memory manager for allocating new nodes
    /// * `modifier` - A function that applies modifications to the node
    ///
    /// # Returns
    ///
    /// A managed reference to the modified node
    fn modify_node<F>(&self, manager: &MemoryManager<T>, modifier: F) -> ManagedRef<Node<T>>
    where
        F: FnOnce(&mut Node<T>);
}

impl<T: Clone> NodeOps<T> for Node<T> {
    #[inline]
    fn modify_node<F>(&self, manager: &MemoryManager<T>, modifier: F) -> ManagedRef<Node<T>>
    where
        F: FnOnce(&mut Node<T>),
    {
        // Get a new node from the memory manager
        let mut new_node = manager.acquire_node();

        // Clone the current node into the new one
        if let Some(node_mut) = new_node.get_mut() {
            *node_mut = self.clone();

            // Apply the modifier function
            modifier(node_mut);
        }

        new_node
    }
}

impl<T: Clone> Default for Node<T> {
    #[inline]
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
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::node::Node;
    ///
    /// let node = Node::<i32>::new();
    /// assert_eq!(node.size(), 0);
    /// assert!(!node.is_relaxed());
    /// ```
    #[inline]
    pub fn new() -> Self {
        Node::Branch {
            children: Vec::with_capacity(NODE_SIZE),
            sizes: None,
        }
    }

    /// Clone this node to create a new node with identical content.
    ///
    /// This method creates a deep copy of the node using the provided memory manager
    /// without modifying any of the content.
    ///
    /// # Parameters
    ///
    /// * `manager` - The memory manager for allocating the new node
    ///
    /// # Returns
    ///
    /// A managed reference to the cloned node
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::node::Node;
    /// use rustica::pvec::memory::MemoryManager;
    ///
    /// let manager = MemoryManager::<i32>::default();
    /// let mut chunk = manager.acquire_chunk();
    /// chunk.get_mut().unwrap().push_back(10);
    /// chunk.get_mut().unwrap().push_back(20);
    /// let node = Node::leaf(chunk);
    ///
    /// let cloned = node.clone_node(&manager);
    /// assert_eq!(node.size(), cloned.size());
    /// ```
    #[inline]
    pub fn clone_node(&self, manager: &MemoryManager<T>) -> ManagedRef<Node<T>> {
        self.modify_node(manager, |_| {}) // Clone the node without modifying its content
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
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::node::Node;
    /// use rustica::pvec::memory::MemoryManager;
    ///
    /// let manager = MemoryManager::<i32>::default();
    /// let mut chunk = manager.acquire_chunk();
    /// chunk.get_mut().unwrap().push_back(10);
    /// chunk.get_mut().unwrap().push_back(20);
    ///
    /// let node = Node::leaf(chunk);
    /// assert_eq!(node.size(), 2);
    /// assert_eq!(*node.get(0, 0).unwrap(), 10);
    /// assert_eq!(*node.get(1, 0).unwrap(), 20);
    /// ```
    #[inline]
    pub fn leaf(chunk: ManagedRef<Chunk<T>>) -> Self {
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
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::node::Node;
    /// use rustica::pvec::memory::MemoryManager;
    ///
    /// // A leaf node's size is its element count
    /// let manager = MemoryManager::<i32>::default();
    /// let mut chunk = manager.acquire_chunk();
    /// chunk.get_mut().unwrap().push_back(10);
    /// chunk.get_mut().unwrap().push_back(20);
    /// let leaf = Node::leaf(chunk);
    /// assert_eq!(leaf.size(), 2);
    ///
    /// // A branch node's size is the sum of its children's sizes
    /// let mut leaf_ref = manager.acquire_node();
    /// *leaf_ref.get_mut().unwrap() = leaf;
    /// let branch = Node::Branch {
    ///     children: vec![Some(leaf_ref)],
    ///     sizes: None
    /// };
    /// assert_eq!(branch.size(), 2);
    /// ```
    pub fn size(&self) -> usize {
        match self {
            Node::Leaf { elements } => elements.len(),
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

    /// Check if this node is empty (contains no elements).
    ///
    /// # Returns
    ///
    /// `true` if the node contains no elements, `false` otherwise.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::node::Node;
    /// use rustica::pvec::memory::MemoryManager;
    ///
    /// // A new branch node is empty
    /// let node = Node::<i32>::new();
    /// assert!(node.is_empty());
    ///
    /// // A leaf node with elements is not empty
    /// let manager = MemoryManager::<i32>::default();
    /// let mut chunk = manager.acquire_chunk();
    /// chunk.get_mut().unwrap().push_back(42);
    /// let leaf = Node::leaf(chunk);
    /// assert!(!leaf.is_empty());
    /// ```
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.size() == 0
    }

    /// Check if this node is a leaf node.
    ///
    /// # Returns
    ///
    /// `true` if the node is a leaf, `false` otherwise.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::node::Node;
    /// use rustica::pvec::memory::MemoryManager;
    ///
    /// // A new branch node is not a leaf
    /// let node = Node::<i32>::new();
    /// assert!(!node.is_leaf());
    ///
    /// // A leaf node is a leaf
    /// let manager = MemoryManager::<i32>::default();
    /// let mut chunk = manager.acquire_chunk();
    /// chunk.get_mut().unwrap().push_back(42);
    /// let leaf = Node::leaf(chunk);
    /// assert!(leaf.is_leaf());
    /// ```
    #[inline]
    pub fn is_leaf(&self) -> bool {
        matches!(self, Node::Leaf { .. })
    }

    /// Check if this node is a branch node.
    ///
    /// # Returns
    ///
    /// `true` if the node is a branch, `false` otherwise.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::node::Node;
    /// use rustica::pvec::memory::MemoryManager;
    ///
    /// // A new branch node is a branch
    /// let node = Node::<i32>::new();
    /// assert!(node.is_branch());
    ///
    /// // A leaf node is not a branch
    /// let manager = MemoryManager::<i32>::default();
    /// let mut chunk = manager.acquire_chunk();
    /// chunk.get_mut().unwrap().push_back(42);
    /// let leaf = Node::leaf(chunk);
    /// assert!(!leaf.is_branch());
    /// ```
    #[inline]
    pub fn is_branch(&self) -> bool {
        matches!(self, Node::Branch { .. })
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
    fn find_child_index(&self, index: usize, shift: usize) -> (usize, usize) {
        match self {
            Node::Branch { sizes, .. } => {
                if let Some(sizes) = sizes {
                    // Use the size table for relaxed nodes
                    self.find_index_in_size_table(sizes, index)
                } else {
                    // Use bit operations for regular nodes - more efficient
                    let mask = (1 << shift) - 1;
                    let child_index = (index >> shift) & NODE_MASK;
                    let sub_index = index & mask;
                    (child_index, sub_index)
                }
            },
            _ => panic!("find_child_index called on a non-branch node"),
        }
    }

    /// Create a new node with a custom initializer function.
    ///
    /// This helper function acquires a new node from the memory manager and
    /// applies the provided creator function to initialize it.
    ///
    /// # Parameters
    ///
    /// * `manager` - The memory manager for node allocation
    /// * `creator` - A function that initializes the newly created node
    ///
    /// # Returns
    ///
    /// A managed reference to the newly created node
    #[inline]
    fn create_node<F>(manager: &MemoryManager<T>, creator: F) -> ManagedRef<Node<T>>
    where
        F: FnOnce(&mut Node<T>),
    {
        let mut new_node = manager.acquire_node();
        creator(new_node.get_mut().unwrap());
        new_node
    }

    /// Create a new branch node with the given children and sizes.
    ///
    /// This function creates a new branch node by allocating a new node from the memory manager
    /// and initializing it with the provided children and sizes.
    ///
    /// # Parameters
    ///
    /// * `manager` - The memory manager for node allocation
    /// * `children` - A vector of optional managed references to child nodes
    /// * `sizes` - An optional vector of cumulative sizes of children
    ///
    /// # Returns
    ///
    /// A managed reference to the newly created branch node
    #[inline]
    fn create_branch_node(
        &self, manager: &MemoryManager<T>, children: Vec<Option<ManagedRef<Node<T>>>>,
        sizes: Option<Vec<usize>>,
    ) -> ManagedRef<Node<T>> {
        Self::create_node(manager, |node| {
            *node = Node::Branch { children, sizes };
        })
    }

    /// Create a new leaf node with the given elements.
    ///
    /// This function creates a new leaf node by allocating a new node from the memory manager
    /// and initializing it with the provided elements.
    ///
    /// # Parameters
    ///
    /// * `manager` - The memory manager for node allocation
    /// * `elements` - A managed reference to a chunk of elements
    ///
    /// # Returns
    ///
    /// A managed reference to the newly created leaf node
    #[inline]
    fn create_leaf_node(
        manager: &MemoryManager<T>, elements: ManagedRef<Chunk<T>>,
    ) -> ManagedRef<Node<T>> {
        Self::create_node(manager, |node| {
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
    #[inline]
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
    /// This function modifies a chunk of elements by creating a mutable reference
    /// and applying the given modifier function.
    ///
    /// # Parameters
    ///
    /// * `chunk` - A managed reference to a chunk of elements
    /// * `modifier` - A function that takes a mutable reference to the chunk and applies modifications
    ///
    /// # Returns
    ///
    /// A managed reference to the modified chunk
    #[inline]
    fn modify_chunk<F>(chunk: &ManagedRef<Chunk<T>>, modifier: F) -> ManagedRef<Chunk<T>>
    where
        F: FnOnce(&mut Chunk<T>),
    {
        // Clone the chunk reference
        let mut new_chunk = chunk.clone();

        // Check if we can get a mutable reference directly
        if let Some(chunk_mut) = new_chunk.get_mut() {
            // If we can, modify it in place
            modifier(chunk_mut);
            new_chunk
        } else {
            // Otherwise, we need to clone the chunk
            let mut cloned_chunk = Chunk::new();
            cloned_chunk.clone_from(&**chunk);

            // Get a mutable reference to our cloned chunk
            let mut managed_chunk = ManagedRef::new(Arc::new(cloned_chunk), chunk.pool());

            // Apply the modifier
            if let Some(chunk_mut) = managed_chunk.get_mut() {
                modifier(chunk_mut);
            }

            managed_chunk
        }
    }

    /// Modify a branch node in place.
    ///
    /// This function modifies a branch node by creating a mutable reference
    /// and applying the given modifier function.
    ///
    /// # Parameters
    ///
    /// * `manager` - The memory manager for node allocation
    /// * `modifier` - A function that takes a mutable reference to the branch node and applies modifications
    ///
    /// # Returns
    ///
    /// A managed reference to the modified branch node
    fn modify_branch<F>(&self, manager: &MemoryManager<T>, modifier: F) -> ManagedRef<Node<T>>
    where
        F: FnOnce(&mut Vec<Option<ManagedRef<Node<T>>>>, &mut Option<Vec<usize>>),
    {
        match self {
            Node::Branch { children, sizes } => {
                let mut new_node = manager.acquire_node();
                let node_mut = new_node.get_mut().unwrap();
                *node_mut = Node::Branch {
                    children: children.clone(),
                    sizes: sizes.clone(),
                };

                if let Node::Branch {
                    children: new_children,
                    sizes: new_sizes,
                } = node_mut
                {
                    modifier(new_children, new_sizes);
                }

                new_node
            },
            _ => panic!("Expected branch node"),
        }
    }

    /// Replace a child node in the branch node.
    ///
    /// This function replaces a child node in the branch node by creating a mutable reference
    /// and applying the given modifier function.
    ///
    /// # Parameters
    ///
    /// * `manager` - The memory manager for node allocation
    /// * `child_index` - The index of the child node to replace
    /// * `new_child` - A managed reference to the new child node
    ///
    /// # Returns
    ///
    /// A managed reference to the modified branch node
    fn replace_child(
        &self, manager: &MemoryManager<T>, child_index: usize, new_child: ManagedRef<Node<T>>,
    ) -> ManagedRef<Node<T>> {
        self.modify_branch(manager, |children, sizes| {
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

    /// Get the number of direct children this node has.
    ///
    /// # Returns
    ///
    /// The number of direct children this node has.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::node::Node;
    /// use rustica::pvec::memory::MemoryManager;
    ///
    /// // A new branch node has no children
    /// let node = Node::<i32>::new();
    /// assert_eq!(node.child_count(), 0);
    ///
    /// // A branch node with children has the correct count
    /// let manager = MemoryManager::<i32>::default();
    /// let mut chunk = manager.acquire_chunk();
    /// chunk.get_mut().unwrap().push_back(42);
    /// let leaf = Node::leaf(chunk);
    /// let mut leaf_ref = manager.acquire_node();
    /// *leaf_ref.get_mut().unwrap() = leaf;
    /// let branch = Node::Branch {
    ///     children: vec![Some(leaf_ref), None],
    ///     sizes: None
    /// };
    /// assert_eq!(branch.child_count(), 1);
    /// ```
    #[inline]
    pub fn child_count(&self) -> usize {
        match self {
            Node::Leaf { .. } => 0,
            Node::Branch { children, .. } => children.iter().flatten().count(),
        }
    }

    /// Check if this node is a relaxed node (has a size table).
    ///
    /// # Returns
    ///
    /// `true` if the node is a relaxed node, `false` otherwise.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::node::Node;
    ///
    /// // A new branch node is not relaxed
    /// let node = Node::<i32>::new();
    /// assert!(!node.is_relaxed());
    ///
    /// // A branch node with a size table is relaxed
    /// let branch: Node<i32> = Node::Branch {
    ///     children: vec![None, None],
    ///     sizes: Some(vec![0, 0])
    /// };
    /// assert!(branch.is_relaxed());
    /// ```
    #[inline]
    pub fn is_relaxed(&self) -> bool {
        if let Node::Branch { sizes, .. } = self {
            sizes.is_some()
        } else {
            false
        }
    }

    /// Convert this node to a relaxed node if it's not already.
    ///
    /// A relaxed node maintains a size table that allows for efficient indexing
    /// operations when the tree structure is not perfectly balanced.
    ///
    /// # Effects
    ///
    /// If the node is a branch node without a size table, this method will
    /// create one by accumulating the sizes of all children.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::node::Node;
    ///
    /// let mut node = Node::<i32>::new();
    /// assert!(!node.is_relaxed());
    ///
    /// node.ensure_relaxed();
    /// assert!(node.is_relaxed());
    /// ```
    #[inline]
    pub fn ensure_relaxed(&mut self) {
        match self {
            Node::Branch { children, sizes } if sizes.is_none() => {
                *sizes = Some(Self::build_size_table(children));
            },
            _ => {},
        }
    }

    /// Get an element at the specified index.
    ///
    /// Returns a reference to the element if it exists, or `None` if the index is out of bounds.
    ///
    /// # Parameters
    ///
    /// * `index` - The index of the element to retrieve
    /// * `shift` - The level in the tree (shift amount in bits)
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::node::Node;
    /// use rustica::pvec::memory::MemoryManager;
    /// use rustica::pvec::chunk::Chunk;
    ///
    /// let manager = MemoryManager::<i32>::default();
    /// let mut chunk = manager.acquire_chunk();
    /// chunk.get_mut().unwrap().push_back(10);
    /// chunk.get_mut().unwrap().push_back(20);
    /// chunk.get_mut().unwrap().push_back(30);
    /// let node = Node::leaf(chunk);
    /// assert_eq!(node.get(1, 0), Some(&20));
    /// assert_eq!(node.get(5, 0), None); // Out of bounds
    /// ```
    pub fn get(&self, index: usize, shift: usize) -> Option<&T> {
        match self {
            Node::Leaf { elements } => elements.get(index),
            Node::Branch { children, sizes: _ } => {
                let (child_index, sub_index) = self.find_child_index(index, shift);

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
    /// * `manager` - A reference to the memory manager
    /// * `index` - The index of the element to update
    /// * `value` - The new value for the element
    /// * `shift` - The level in the tree (shift amount in bits)
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::node::Node;
    /// use rustica::pvec::memory::MemoryManager;
    ///
    /// let manager = MemoryManager::<i32>::default();
    /// let mut chunk = manager.acquire_chunk();
    /// chunk.get_mut().unwrap().push_back(10);
    /// chunk.get_mut().unwrap().push_back(20);
    /// chunk.get_mut().unwrap().push_back(30);
    /// let node = Node::leaf(chunk);
    ///
    /// // Update an element
    /// let new_node = node.update(&manager, 1, 42, 0);
    /// assert_eq!(new_node.unwrap().get(1, 0), Some(&42));
    ///
    /// // Out of bounds
    /// assert!(node.update(&manager, 5, 42, 0).is_none());
    /// ```
    pub fn update(
        &self, manager: &MemoryManager<T>, index: usize, value: T, shift: usize,
    ) -> Option<ManagedRef<Node<T>>> {
        match self {
            Node::Leaf { elements } => {
                if index >= elements.len() {
                    return None;
                }

                // Create a new chunk only if needed
                let new_elements = Self::modify_chunk(elements, |chunk| {
                    if let Some(elem) = chunk.get_mut(index) {
                        *elem = value;
                    }
                });

                Some(Self::create_leaf_node(manager, new_elements))
            },
            Node::Branch { children, sizes: _ } => {
                let (child_index, sub_index) = self.find_child_index(index, shift);

                if child_index >= children.len() || children[child_index].is_none() {
                    return None;
                }

                let child = &children[child_index].as_ref().unwrap();

                // Recursive update with reduced shift
                match child.update(manager, sub_index, value, shift - NODE_BITS) {
                    Some(new_child) => {
                        // Only create a new branch if the child actually changed
                        if std::sync::Arc::ptr_eq(&child.to_arc(), &new_child.to_arc()) {
                            Some(ManagedRef::new(std::sync::Arc::new(self.clone()), None))
                        } else {
                            Some(self.replace_child(manager, child_index, new_child))
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
    /// * `manager` - The memory manager for allocating new nodes
    /// * `value` - The value to add to the node
    /// * `shift` - The current tree level shift value
    ///
    /// # Returns
    ///
    /// A tuple containing:
    /// - A new node with the element added
    /// - A boolean indicating whether the node was split (true) or not (false)
    /// - The overflow node if a split occurred, otherwise None
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::node::Node;
    /// use rustica::pvec::memory::MemoryManager;
    /// use rustica::pvec::chunk::Chunk;
    ///
    /// let manager = MemoryManager::<i32>::default();
    /// let mut chunk = manager.acquire_chunk();
    /// chunk.get_mut().unwrap().push_back(10);
    /// chunk.get_mut().unwrap().push_back(20);
    /// chunk.get_mut().unwrap().push_back(30);
    /// let node = Node::leaf(chunk);
    ///
    /// // Add an element to an empty node
    /// let (new_node, split, overflow) = node.push_back(&manager, 42, 5);
    /// assert_eq!(new_node.size(), 4);
    /// assert_eq!(*new_node.get(3, 0).unwrap(), 42);
    /// assert!(!split);
    /// assert!(overflow.is_none());
    /// ```
    pub fn push_back(&self, manager: &MemoryManager<T>, value: T, _shift: usize) -> PushResult<T> {
        match self {
            Node::Leaf { elements } => {
                if elements.len() < CHUNK_SIZE {
                    // There's space in the leaf node, add the element
                    let modified_elements = Self::modify_chunk(elements, |chunk| {
                        chunk.push_back(value);
                    });

                    let new_node = Self::create_leaf_node(manager, modified_elements);
                    (new_node, false, None)
                } else {
                    // Leaf node is full, create overflow node with the new element
                    let mut new_chunk = manager.acquire_chunk();
                    new_chunk.get_mut().unwrap().push_back(value);
                    let overflow = Self::create_leaf_node(manager, new_chunk);

                    // Clone the existing leaf node
                    let new_node = Self::create_leaf_node(manager, elements.clone());

                    (new_node, true, Some(overflow))
                }
            },
            Node::Branch { children, sizes: _ } => {
                if children.is_empty() {
                    // Empty branch node, create a leaf node instead
                    let new_chunk = Self::modify_chunk(&manager.acquire_chunk(), |chunk| {
                        chunk.push_back(value);
                    });
                    let new_node = Self::create_leaf_node(manager, new_chunk);
                    (new_node, false, None)
                } else {
                    // Find the last child to push into
                    let last_idx = children.len() - 1;

                    if let Some(last_child) = &children[last_idx] {
                        // Push to the last child
                        let (new_child, split, overflow) =
                            last_child.push_back(manager, value, _shift - NODE_BITS);

                        // Replace the last child with the new one
                        let new_node = self.replace_child(manager, last_idx, new_child);

                        if !split {
                            return (new_node, false, None);
                        }

                        // Handle overflow by adding it as a new child if there's space
                        if children.len() < NODE_SIZE {
                            let new_node = new_node.modify_branch(manager, |children, sizes| {
                                children.push(overflow.clone());

                                // Update size table if this is a relaxed node
                                if let Some(size_table) = sizes {
                                    let overflow_size = overflow.as_ref().unwrap().size();
                                    size_table
                                        .push(size_table.last().unwrap_or(&0) + overflow_size);
                                }
                            });
                            (new_node, false, None)
                        } else {
                            // Branch node is full, split needed at this level too
                            (new_node, true, overflow)
                        }
                    } else {
                        // Last child is None, replace with a new leaf node
                        let new_chunk = Self::modify_chunk(&manager.acquire_chunk(), |chunk| {
                            chunk.push_back(value);
                        });
                        let leaf_node = Self::create_leaf_node(manager, new_chunk);

                        let new_node = self.replace_child(manager, last_idx, leaf_node);
                        (new_node, false, None)
                    }
                }
            },
        }
    }

    /// Push a new element to the front of this node.
    ///
    /// This method creates a new node with the element added to the front.
    /// If the node is already at capacity, it will split and create an overflow node.
    ///
    /// # Parameters
    ///
    /// * `manager` - The memory manager for allocating new nodes
    /// * `value` - The value to add to the node
    /// * `shift` - The current tree level shift value
    ///
    /// # Returns
    ///
    /// A tuple containing:
    /// - A new node with the element added
    /// - A boolean indicating whether the node was split (true) or not (false)
    /// - The overflow node if a split occurred, otherwise None
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::node::Node;
    /// use rustica::pvec::memory::MemoryManager;
    ///
    /// let manager = MemoryManager::<i32>::default();
    /// let mut chunk = manager.acquire_chunk();
    /// chunk.get_mut().unwrap().push_back(10);
    /// chunk.get_mut().unwrap().push_back(20);
    /// let node = Node::leaf(chunk);
    ///
    /// // Add an element to the front
    /// let (new_node, split, overflow) = node.push_front(&manager, 5, 0);
    /// assert_eq!(new_node.size(), 3);
    /// assert_eq!(*new_node.get(0, 0).unwrap(), 5);
    /// assert!(!split);
    /// assert!(overflow.is_none());
    /// ```
    pub fn push_front(&self, manager: &MemoryManager<T>, value: T, _shift: usize) -> PushResult<T> {
        match self {
            Node::Leaf { elements } => {
                if elements.len() < CHUNK_SIZE {
                    // There's space in the leaf node, add the element
                    let modified_elements = Self::modify_chunk(elements, |chunk| {
                        chunk.push_front(value);
                    });

                    let new_node = Self::create_leaf_node(manager, modified_elements);
                    (new_node, false, None)
                } else {
                    // Leaf node is full, create overflow node with the new element
                    let mut new_chunk = manager.acquire_chunk();
                    new_chunk.get_mut().unwrap().push_back(value);
                    let overflow = Self::create_leaf_node(manager, new_chunk);

                    // Clone the existing leaf node
                    let new_node = Self::create_leaf_node(manager, elements.clone());

                    (new_node, true, Some(overflow))
                }
            },
            Node::Branch { children, sizes } => {
                if children.is_empty() {
                    // Empty branch node, create a new leaf node
                    let new_chunk = Self::modify_chunk(&manager.acquire_chunk(), |chunk| {
                        chunk.push_back(value);
                    });
                    let new_leaf = Self::create_leaf_node(manager, new_chunk);

                    // Create branch node with the leaf node
                    let new_node =
                        self.create_branch_node(manager, vec![Some(new_leaf)], Some(vec![1]));

                    (new_node, false, None)
                } else if let Some(first_child) = &children[0] {
                    // Try to add element to the first child node
                    let (new_child, was_split, overflow) =
                        first_child.push_front(manager, value, _shift - NODE_BITS);

                    // Clone child node array and update first child
                    let mut new_children = children.clone();
                    new_children[0] = Some(new_child.clone());

                    if was_split {
                        if children.len() < NODE_SIZE {
                            // Space available for overflow at beginning
                            let overflow_clone = overflow.clone();
                            new_children.insert(0, overflow_clone);

                            // Update size table
                            let new_sizes = if let Some(old_sizes) = sizes {
                                let overflow_size = overflow.unwrap().size();
                                let mut new_size_table = Vec::with_capacity(new_children.len());
                                new_size_table.push(overflow_size);

                                for &size in old_sizes.iter() {
                                    new_size_table.push(size + overflow_size);
                                }

                                Some(new_size_table)
                            } else {
                                Some(Self::build_size_table(&new_children))
                            };

                            let new_node =
                                self.create_branch_node(manager, new_children, new_sizes);
                            (new_node, false, None)
                        } else {
                            // Node is full, need to split
                            let new_node =
                                self.create_branch_node(manager, new_children, sizes.clone());

                            // Create overflow node
                            let overflow_clone = overflow.clone();
                            let overflow_node = self.create_branch_node(
                                manager,
                                vec![overflow_clone.clone()],
                                Some(vec![overflow_clone.unwrap().size()]),
                            );

                            (new_node, true, Some(overflow_node))
                        }
                    } else {
                        // No split, just update size table if needed
                        let new_sizes = if let Some(old_sizes) = sizes {
                            let mut new_size_table = old_sizes.clone();
                            let size_inc = new_child.size() - first_child.size();

                            if size_inc != 0 {
                                for size in new_size_table.iter_mut() {
                                    *size += size_inc;
                                }
                            }

                            Some(new_size_table)
                        } else {
                            None
                        };

                        let new_node = self.create_branch_node(manager, new_children, new_sizes);
                        (new_node, false, None)
                    }
                } else {
                    // First slot is empty, create new leaf node
                    let new_chunk = Self::modify_chunk(&manager.acquire_chunk(), |chunk| {
                        chunk.push_back(value);
                    });
                    let new_leaf = Self::create_leaf_node(manager, new_chunk);

                    // Clone child node array and update
                    let mut new_children = children.clone();
                    new_children[0] = Some(new_leaf.clone());

                    // Update size table
                    let new_sizes = if let Some(old_sizes) = sizes {
                        let mut new_size_table = old_sizes.clone();
                        let leaf_size = new_leaf.size();

                        for size in new_size_table.iter_mut() {
                            *size += leaf_size;
                        }

                        Some(new_size_table)
                    } else {
                        Some(Self::build_size_table(&new_children))
                    };

                    let new_node = self.create_branch_node(manager, new_children, new_sizes);
                    (new_node, false, None)
                }
            },
        }
    }

    /// Join two nodes at the same level to create a new node.
    ///
    /// This method combines two nodes into a single node, handling different node types
    /// and ensuring proper structure of the resulting tree. It's primarily used for
    /// concatenation operations.
    ///
    /// # Parameters
    ///
    /// * `manager` - The memory manager for allocating new nodes
    /// * `other` - The node to join with this node
    /// * `shift` - The current tree level shift value
    ///
    /// # Returns
    ///
    /// A new node containing all elements from both input nodes
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::node::Node;
    /// use rustica::pvec::memory::MemoryManager;
    ///
    /// let manager = MemoryManager::<i32>::default();
    ///
    /// // Create two leaf nodes
    /// let mut chunk1 = manager.acquire_chunk();
    /// chunk1.get_mut().unwrap().push_back(1);
    /// chunk1.get_mut().unwrap().push_back(2);
    /// let node1 = Node::leaf(chunk1);
    ///
    /// let mut chunk2 = manager.acquire_chunk();
    /// chunk2.get_mut().unwrap().push_back(3);
    /// chunk2.get_mut().unwrap().push_back(4);
    /// let node2 = Node::leaf(chunk2);
    ///
    /// // Join the nodes
    /// let joined = node1.join(&manager, &node2, 0);
    ///
    /// // Verify the result
    /// assert_eq!(joined.size(), 4);
    /// assert_eq!(*joined.get(0, 0).unwrap(), 1);
    /// assert_eq!(*joined.get(3, 0).unwrap(), 4);
    /// ```
    pub fn join(
        &self, manager: &MemoryManager<T>, other: &Node<T>, _shift: usize,
    ) -> ManagedRef<Node<T>> {
        match (self, other) {
            (Node::Leaf { elements: left }, Node::Leaf { elements: right }) => {
                let left_len = left.len();
                let right_len = right.len();
                let total_len = left_len + right_len;

                if total_len <= CHUNK_SIZE {
                    // Can store all elements in a single leaf node
                    let new_chunk = Self::modify_chunk(left, |chunk| {
                        // Add elements from the right chunk
                        for i in 0..right_len {
                            if let Some(value) = right.get(i) {
                                chunk.push_back(value.clone());
                            }
                        }
                    });

                    Self::create_leaf_node(manager, new_chunk)
                } else {
                    // Create a branch node with two leaf children
                    self.create_branch_node(
                        manager,
                        vec![
                            Some(Self::create_leaf_node(manager, left.clone())),
                            Some(Self::create_leaf_node(manager, right.clone())),
                        ],
                        Some(vec![left_len, total_len]),
                    )
                }
            },
            (
                Node::Branch {
                    children: left_children,
                    sizes: left_sizes,
                },
                Node::Branch {
                    children: right_children,
                    sizes: right_sizes,
                },
            ) => {
                let left_child_count = left_children.len();
                let right_child_count = right_children.len();
                let total_children = left_child_count + right_child_count;

                let left_size = self.size();
                let total_size = left_size + other.size();

                if total_children <= NODE_SIZE {
                    // Combine children into a single node
                    let mut new_children = Vec::with_capacity(total_children);
                    new_children.extend_from_slice(left_children);
                    new_children.extend_from_slice(right_children);

                    // Create size table based on relaxed/regular nodes
                    let new_sizes = match (left_sizes, right_sizes) {
                        (Some(left_sizes), Some(right_sizes)) => {
                            // Both nodes are relaxed
                            let mut size_table = Vec::with_capacity(total_children);
                            size_table.extend_from_slice(left_sizes);

                            // Add offset to right sizes
                            let right_sizes_offset: Vec<_> =
                                right_sizes.iter().map(|&size| left_size + size).collect();
                            size_table.extend_from_slice(&right_sizes_offset);

                            Some(size_table)
                        },
                        (Some(left_sizes), None) => {
                            // Only left node is relaxed
                            let mut size_table = Vec::with_capacity(total_children);
                            size_table.extend_from_slice(left_sizes);

                            let mut sum = left_size;
                            for child in right_children.iter().filter_map(Option::as_ref) {
                                sum += child.size();
                                size_table.push(sum);
                            }
                            Some(size_table)
                        },
                        (None, Some(right_sizes)) => {
                            // Only right node is relaxed
                            let mut size_table = Vec::with_capacity(total_children);

                            // Build size table for left children
                            let mut sum = 0;
                            for child in left_children.iter().filter_map(Option::as_ref) {
                                sum += child.size();
                                size_table.push(sum);
                            }

                            // Add offset to right sizes
                            let right_sizes_offset: Vec<_> =
                                right_sizes.iter().map(|&size| left_size + size).collect();
                            size_table.extend_from_slice(&right_sizes_offset);

                            Some(size_table)
                        },
                        (None, None) => Some(Self::build_size_table(&new_children)),
                    };

                    self.create_branch_node(manager, new_children, new_sizes)
                } else {
                    // Create higher level node
                    self.create_branch_node(
                        manager,
                        vec![
                            Some(self.create_branch_node(
                                manager,
                                left_children.clone(),
                                left_sizes.clone(),
                            )),
                            Some(self.create_branch_node(
                                manager,
                                right_children.clone(),
                                right_sizes.clone(),
                            )),
                        ],
                        Some(vec![left_size, total_size]),
                    )
                }
            },
            (leaf @ Node::Leaf { .. }, branch @ Node::Branch { .. }) => {
                // Convert leaf to branch and merge
                if let Node::Leaf { elements } = leaf {
                    let leaf_node = Self::create_leaf_node(manager, elements.clone());
                    let branch_node = self.create_branch_node(
                        manager,
                        vec![Some(leaf_node)],
                        Some(vec![leaf.size()]),
                    );
                    branch_node.join(manager, branch, _shift)
                } else {
                    unreachable!()
                }
            },
            (branch @ Node::Branch { .. }, leaf @ Node::Leaf { .. }) => {
                // Convert leaf to branch and merge
                if let Node::Leaf { elements } = leaf {
                    let leaf_node = Self::create_leaf_node(manager, elements.clone());
                    let branch_node = self.create_branch_node(
                        manager,
                        vec![Some(leaf_node)],
                        Some(vec![leaf.size()]),
                    );
                    branch.join(manager, &branch_node, _shift)
                } else {
                    unreachable!()
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
    /// * `manager` - The memory manager for allocating new nodes
    /// * `index` - The index at which to split the node
    /// * `shift` - The current tree level shift value
    ///
    /// # Returns
    ///
    /// A tuple containing:
    /// - The left part of the node (elements before index)
    /// - The right part of the node (elements at and after index)
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::node::Node;
    /// use rustica::pvec::memory::MemoryManager;
    ///
    /// let manager = MemoryManager::<i32>::default();
    /// let mut chunk = manager.acquire_chunk();
    /// chunk.get_mut().unwrap().push_back(10);
    /// chunk.get_mut().unwrap().push_back(20);
    /// chunk.get_mut().unwrap().push_back(30);
    /// let node = Node::leaf(chunk);
    ///
    /// // Split at index 1
    /// let (left, right) = node.split(&manager, 1, 0);
    ///
    /// // Verify the result
    /// assert_eq!(left.size(), 1);
    /// assert_eq!(right.size(), 2);
    /// assert_eq!(*left.get(0, 0).unwrap(), 10);
    /// assert_eq!(*right.get(0, 0).unwrap(), 20);
    /// assert_eq!(*right.get(1, 0).unwrap(), 30);
    /// ```
    pub fn split(
        &self, manager: &MemoryManager<T>, index: usize, shift: usize,
    ) -> (ManagedRef<Node<T>>, ManagedRef<Node<T>>) {
        match self {
            Node::Leaf { elements } => {
                if index == 0 {
                    // Split before the first element (left is empty)
                    let empty = Self::create_leaf_node(manager, manager.acquire_chunk());
                    let node = Self::create_leaf_node(manager, elements.clone());
                    (empty, node)
                } else if index >= elements.len() {
                    // Split after the last element (right is empty)
                    let node = Self::create_leaf_node(manager, elements.clone());
                    let empty = Self::create_leaf_node(manager, manager.acquire_chunk());
                    (node, empty)
                } else {
                    // Split in the middle
                    // Create left chunk (elements before index)
                    let left_chunk = Self::modify_chunk(elements, |chunk| {
                        // Remove elements after index
                        while chunk.len() > index {
                            chunk.pop_back();
                        }
                    });

                    // Create right chunk (elements at and after index)
                    let right_chunk = manager.acquire_chunk();
                    let right_chunk = Self::modify_chunk(&right_chunk, |chunk| {
                        for i in index..elements.len() {
                            if let Some(value) = elements.get(i) {
                                chunk.push_back(value.clone());
                            }
                        }
                    });

                    // Create left and right nodes
                    let left_node = Self::create_leaf_node(manager, left_chunk);
                    let right_node = Self::create_leaf_node(manager, right_chunk);

                    (left_node, right_node)
                }
            },
            Node::Branch { children, sizes } => {
                if index == 0 {
                    // Split before the first element (left is empty)
                    let empty = self.create_branch_node(manager, Vec::new(), Some(Vec::new()));
                    let node = self.create_branch_node(manager, children.clone(), sizes.clone());
                    (empty, node)
                } else if index >= self.size() {
                    // Split after the last element (right is empty)
                    let node = self.create_branch_node(manager, children.clone(), sizes.clone());
                    let empty = self.create_branch_node(manager, Vec::new(), Some(Vec::new()));
                    (node, empty)
                } else {
                    // Find the child node containing the split point
                    let (child_index, sub_index) = self.find_child_index(index, shift);

                    if child_index >= children.len() || children[child_index].is_none() {
                        panic!("Invalid tree structure in split operation");
                    }

                    let child = children[child_index].as_ref().unwrap();

                    // Split the child node
                    let (child_left, child_right) =
                        child.split(manager, sub_index, shift - NODE_BITS);

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
                    let left_node = self.create_branch_node(manager, left_children, left_sizes);
                    let right_node = self.create_branch_node(manager, right_children, right_sizes);

                    (left_node, right_node)
                }
            },
        }
    }

    /// Pop an element from the front of this node.
    ///
    /// This method removes the first element from the node and returns a new node
    /// along with the removed element. If the node is empty, returns the node unchanged
    /// and None for the element.
    ///
    /// # Parameters
    ///
    /// * `manager` - The memory manager for allocating new nodes
    /// * `shift` - The current tree level shift value
    ///
    /// # Returns
    ///
    /// A tuple containing:
    /// - A new node with the first element removed
    /// - The removed element, or None if the node was empty
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::node::Node;
    /// use rustica::pvec::memory::MemoryManager;
    ///
    /// let manager = MemoryManager::<i32>::default();
    /// let mut chunk = manager.acquire_chunk();
    /// chunk.get_mut().unwrap().push_back(10);
    /// chunk.get_mut().unwrap().push_back(20);
    /// let node = Node::leaf(chunk);
    ///
    /// // Pop the first element
    /// let (new_node, popped) = node.pop_front(&manager, 0);
    /// assert_eq!(popped, Some(10));
    /// assert_eq!(new_node.size(), 1);
    /// assert_eq!(*new_node.get(0, 0).unwrap(), 20);
    /// ```
    pub fn pop_front(&self, manager: &MemoryManager<T>, _shift: usize) -> PopResult<T> {
        match self {
            Node::Leaf { elements } => {
                if elements.is_empty() {
                    let mut new_node = manager.acquire_node();
                    *new_node.get_mut().unwrap() = self.clone();
                    return (new_node, None);
                }

                let mut result = None;
                let new_elements = Self::modify_chunk(elements, |chunk| {
                    result = chunk.pop_front();
                });

                let new_node = Self::create_leaf_node(manager, new_elements);
                (new_node, result)
            },
            Node::Branch {
                children,
                ref sizes,
            } => {
                if children.is_empty() {
                    let mut new_node = manager.acquire_node();
                    *new_node.get_mut().unwrap() = self.clone();
                    return (new_node, None);
                }

                if let Some(first_child) = &children[0] {
                    let (new_first_child, result) =
                        first_child.pop_front(manager, _shift - NODE_BITS);

                    if result.is_some() {
                        let new_node = self.modify_branch(manager, |node_children, node_sizes| {
                            node_children.clear();
                            node_children.push(Some(new_first_child.clone()));

                            node_children.extend(children.iter().skip(1).cloned());

                            if let Some(old_sizes) = sizes {
                                let size_diff = first_child.size() - new_first_child.size();
                                *node_sizes =
                                    Some(old_sizes.iter().map(|&size| size - size_diff).collect());
                            }
                        });

                        return (new_node, result);
                    }

                    if children.len() > 1 {
                        let mut new_children = Vec::with_capacity(children.len() - 1);
                        new_children.extend(children.iter().skip(1).cloned());

                        let new_sizes = sizes
                            .as_ref()
                            .map(|old_sizes| old_sizes.iter().skip(1).cloned().collect());

                        let new_node = self.create_branch_node(manager, new_children, new_sizes);
                        return new_node.pop_front(manager, _shift);
                    }
                }

                let empty_branch = self.create_branch_node(manager, Vec::new(), Some(Vec::new()));
                (empty_branch, None)
            },
        }
    }

    /// Pop an element from the back of this node.
    ///
    /// This method removes the last element from the node and returns a new node
    /// along with the removed element. If the node is empty, returns the node unchanged
    /// and None for the element.
    ///
    /// # Parameters
    ///
    /// * `manager` - The memory manager for allocating new nodes
    /// * `shift` - The current tree level shift value
    ///
    /// # Returns
    ///
    /// A tuple containing:
    /// - A new node with the last element removed
    /// - The removed element, or None if the node was empty
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::node::Node;
    /// use rustica::pvec::memory::MemoryManager;
    ///
    /// let manager = MemoryManager::<i32>::default();
    /// let mut chunk = manager.acquire_chunk();
    /// chunk.get_mut().unwrap().push_back(10);
    /// chunk.get_mut().unwrap().push_back(20);
    /// let node = Node::leaf(chunk);
    ///
    /// // Pop the last element
    /// let (new_node, popped) = node.pop_back(&manager, 0);
    /// assert_eq!(popped, Some(20));
    /// assert_eq!(new_node.size(), 1);
    /// assert_eq!(*new_node.get(0, 0).unwrap(), 10);
    /// ```
    pub fn pop_back(&self, manager: &MemoryManager<T>, _shift: usize) -> PopResult<T> {
        match self {
            Node::Leaf { elements } => {
                if elements.is_empty() {
                    let mut new_node = manager.acquire_node();
                    *new_node.get_mut().unwrap() = self.clone();
                    return (new_node, None);
                }

                let mut result = None;
                let new_elements = Self::modify_chunk(elements, |chunk| {
                    result = chunk.pop_back();
                });

                (Self::create_leaf_node(manager, new_elements), result)
            },
            Node::Branch { children, sizes } => {
                if children.is_empty() {
                    let mut new_node = manager.acquire_node();
                    *new_node.get_mut().unwrap() = self.clone();
                    return (new_node, None);
                }

                let last_idx = children.len() - 1;

                if let Some(last_child) = &children[last_idx] {
                    let (new_child, result) = last_child.pop_back(manager, _shift - NODE_BITS);

                    if result.is_none() {
                        if children.len() > 1 {
                            let mut new_children = Vec::with_capacity(last_idx);
                            new_children.extend(children.iter().take(last_idx).cloned());

                            let new_sizes = sizes.as_ref().map(|old_sizes| {
                                old_sizes.iter().take(last_idx).cloned().collect()
                            });

                            let new_node =
                                self.create_branch_node(manager, new_children, new_sizes);
                            return new_node.pop_back(manager, _shift);
                        } else {
                            return (
                                self.create_branch_node(manager, Vec::new(), Some(Vec::new())),
                                None,
                            );
                        }
                    }

                    let new_node = self.modify_branch(manager, |node_children, node_sizes| {
                        node_children.extend(children.iter().take(last_idx).cloned());
                        node_children.push(Some(new_child.clone()));

                        if let Some(old_sizes) = sizes {
                            let size_diff = last_child.size() - new_child.size();
                            let mut new_size_table = Vec::with_capacity(children.len());
                            new_size_table.extend(old_sizes.iter().take(last_idx).cloned());
                            new_size_table.push(old_sizes[last_idx] - size_diff);
                            *node_sizes = Some(new_size_table);
                        }
                    });

                    (new_node, result)
                } else {
                    let mut new_children = Vec::with_capacity(last_idx);
                    new_children.extend(children.iter().take(last_idx).cloned());

                    let new_sizes = sizes
                        .as_ref()
                        .map(|old_sizes| old_sizes.iter().take(last_idx).cloned().collect());

                    let new_node = self.create_branch_node(manager, new_children, new_sizes);

                    if new_node.child_count() > 0 {
                        new_node.pop_back(manager, _shift)
                    } else {
                        (new_node, None)
                    }
                }
            },
        }
    }
}

impl<T: Clone> Node<T> {}

impl<T: Clone + Debug> Debug for Node<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Node::Leaf { elements } => {
                // Use a debug struct to avoid dereferencing the ManagedRef directly
                let mut debug_struct = f.debug_struct("Leaf");
                debug_struct.field("size", &elements.len());

                // Print a representation of the elements without dereferencing directly
                let elements_str = format!("[{} items]", elements.len());
                debug_struct.field("elements", &elements_str);

                debug_struct.finish()
            },
            Node::Branch { children, sizes } => {
                let mut debug_struct = f.debug_struct("Branch");

                // Use methods to access size and child count to avoid direct dereference
                let size = self.size();
                let child_count = self.child_count();

                debug_struct.field("size", &size);
                debug_struct.field("child_count", &child_count);

                if let Some(sizes) = sizes {
                    debug_struct.field("relaxed", &true);
                    debug_struct.field("sizes", sizes);
                } else {
                    debug_struct.field("relaxed", &false);
                }

                // Print a representation of the children count without dereferencing
                let children_str = format!("[{} children]", children.len());
                debug_struct.field("children", &children_str);

                debug_struct.finish()
            },
        }
    }
}
