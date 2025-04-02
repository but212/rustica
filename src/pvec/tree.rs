//! RRB Tree Module
//!
//! This module defines the Tree type, which is the main data structure
//! for the persistent vector. It manages a root node and provides vector operations.
//!
//! The Tree type implements a Relaxed Radix Balanced (RRB) tree, which is a
//! persistent data structure optimized for both random access and structural
//! updates at the ends. It provides efficient index-based access, append, and
//! prepend operations.
//!
//! # Examples
//!
//! ```
//! use rustica::pvec::tree::Tree;
//!
//! // Create a new tree
//! let mut tree = Tree::<i32>::new();
//!
//! // Add elements to the tree
//! let tree = tree.push_back(10);
//! let tree = tree.push_back(20);
//! let tree = tree.push_back(30);
//!
//! // Access elements
//! assert_eq!(tree.get(1), Some(&20));
//! assert_eq!(tree.len(), 3);
//!
//! // Update an element
//! let updated_tree = tree.update(1, 25);
//! assert_eq!(updated_tree.get(1), Some(&25));
//!
//! // The original tree is unchanged
//! assert_eq!(tree.get(1), Some(&20));
//! ```

use std::fmt::{self, Debug};
use std::iter::FromIterator;
use std::sync::Arc;

use super::cache::IndexCache;
use super::memory::{AllocationStrategy, ManagedRef, MemoryManager};
use super::node::{Node, NODE_BITS, NODE_SIZE};

/// A persistent vector implemented as a Relaxed Radix Balanced (RRB) tree.
///
/// The tree provides efficient indexing, updating, and appending operations
/// with persistence guarantees. All operations create a new version of the
/// tree without modifying the original, allowing for efficient structural
/// sharing between different versions.
#[derive(Clone)]
pub struct Tree<T: Clone> {
    /// The root node of the tree.
    ///
    /// This is wrapped in a managed reference to enable efficient sharing
    /// between different versions of the tree.
    root: ManagedRef<Node<T>>,

    /// The number of elements in the tree.
    ///
    /// This is cached at the tree level to avoid traversing the entire
    /// tree structure when size information is needed.
    size: usize,

    /// The height of the tree (number of levels).
    ///
    /// A height of 0 means the tree consists only of a single leaf node.
    /// Each additional level adds a shift of NODE_BITS bits to the tree.
    height: usize,

    /// The memory manager used for allocating and recycling nodes.
    ///
    /// This handles memory management for nodes, chunks, and other
    /// data structures used by the tree.
    manager: MemoryManager<T>,

    /// Cache for accelerating repeated access operations.
    ///
    /// The cache stores information about the most recently accessed index,
    /// which can significantly speed up accesses to nearby indices.
    cache: IndexCache,
}

impl<T: Clone> Tree<T> {
    /// Create a new, empty tree.
    ///
    /// This initializes a tree with an empty root node and zero elements.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::tree::Tree;
    ///
    /// let tree: Tree<i32> = Tree::new();
    /// assert_eq!(tree.len(), 0);
    /// assert!(tree.is_empty());
    /// ```
    #[inline]
    pub fn new() -> Self {
        let manager = MemoryManager::new(AllocationStrategy::Direct);

        // Create an empty leaf node
        let chunk = manager.acquire_chunk();
        let mut root = manager.acquire_node();
        if let Some(node_ref) = root.get_mut() {
            *node_ref = Node::leaf(chunk);
        }

        Self {
            root,
            size: 0,
            height: 0,
            manager,
            cache: IndexCache::new(),
        }
    }

    /// Create a new tree with a single element.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::tree::Tree;
    ///
    /// let tree = Tree::unit(42);
    /// assert_eq!(tree.len(), 1);
    /// assert_eq!(tree.get(0), Some(&42));
    /// ```
    #[inline]
    pub fn unit(value: T) -> Self {
        let manager = MemoryManager::new(AllocationStrategy::Direct);
        let mut chunk = manager.acquire_chunk();
        chunk.get_mut().unwrap().push_back(value);

        let mut root = manager.acquire_node();
        *root.get_mut().unwrap() = Node::leaf(chunk);

        Self {
            root,
            size: 1,
            height: 0,
            manager,
            cache: IndexCache::new(),
        }
    }

    /// Create a new tree from a slice of elements.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::tree::Tree;
    ///
    /// let data = vec![1, 2, 3, 4, 5];
    /// let tree = Tree::from_slice(&data);
    /// assert_eq!(tree.len(), 5);
    /// assert_eq!(tree.get(2), Some(&3));
    /// ```
    pub fn from_slice(slice: &[T]) -> Self {
        if slice.is_empty() {
            return Self::new();
        }

        let manager = MemoryManager::new(AllocationStrategy::Direct);
        let mut result = Self {
            root: manager.acquire_node(),
            size: slice.len(),
            height: 0,
            manager,
            cache: IndexCache::new(),
        };

        // Create chunks directly from the slice
        let mut remaining = slice;
        let mut current_chunk = result.manager.acquire_chunk();

        while !remaining.is_empty() {
            let chunk_size = remaining.len().min(NODE_SIZE);
            let (to_add, rest) = remaining.split_at(chunk_size);

            let chunk_ref = current_chunk.get_mut().unwrap();
            for item in to_add {
                chunk_ref.push_back(item.clone());
            }

            remaining = rest;
        }

        // Set up the root node as a leaf
        *result.root.get_mut().unwrap() = Node::leaf(current_chunk);

        result
    }

    /// Get the number of elements in the tree.
    ///
    /// This operation is O(1) as the size is cached at the tree level.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::tree::Tree;
    ///
    /// let tree = Tree::from_slice(&[1, 2, 3]);
    /// assert_eq!(tree.len(), 3);
    /// ```
    #[inline]
    pub const fn len(&self) -> usize {
        self.size
    }

    /// Append an element to the end of the tree.
    ///
    /// This is a convenience method that clones the tree and calls `push_back`.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::tree::Tree;
    ///
    /// let tree = Tree::new();
    /// let tree = tree.append(10);
    /// let tree = tree.append(20);
    /// assert_eq!(tree.len(), 2);
    /// assert_eq!(tree.get(1), Some(&20));
    /// ```
    #[inline]
    pub fn append(&self, value: T) -> Self {
        let mut tree = self.clone();
        tree = tree.push_back(value);
        tree
    }

    /// Truncate the tree to the specified length.
    ///
    /// If the new length is greater than or equal to the current length,
    /// the tree is returned unchanged. Otherwise, the tree is truncated
    /// to contain exactly `new_len` elements.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::tree::Tree;
    ///
    /// let tree = Tree::from_slice(&[1, 2, 3, 4, 5]);
    /// let truncated = tree.truncate(3);
    /// assert_eq!(truncated.len(), 3);
    /// assert_eq!(truncated.get(2), Some(&3));
    /// assert_eq!(truncated.get(3), None);
    /// ```
    pub fn truncate(&self, new_len: usize) -> Self {
        let mut result = self.clone();
        result.size = new_len.min(self.size);
        result
    }

    /// Remove an element at the specified index from the tree.
    ///
    /// Returns a new tree with the element removed. If the index is out of bounds,
    /// returns a copy of the original tree unchanged.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::tree::Tree;
    ///
    /// let tree = Tree::from_slice(&[10, 20, 30, 40]);
    /// let new_tree = tree.remove(1);
    /// assert_eq!(new_tree.len(), 3);
    /// assert_eq!(new_tree.get(0), Some(&10));
    /// assert_eq!(new_tree.get(1), Some(&30));
    /// assert_eq!(new_tree.get(2), Some(&40));
    /// ```
    pub fn remove(&self, index: usize) -> Self {
        if index >= self.size {
            return self.clone();
        }

        let mut result = self.clone();
        result.size -= 1;

        // For elements after the removed index, shift them back by one
        for i in index..result.size {
            if let Some(next_value) = self.get(i + 1).cloned() {
                result = result.update(i, next_value);
            }
        }

        result
    }

    /// Check if the tree is empty (contains no elements).
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::tree::Tree;
    ///
    /// let tree: Tree<i32> = Tree::new();
    /// assert!(tree.is_empty());
    ///
    /// let tree = Tree::unit(42);
    /// assert!(!tree.is_empty());
    /// ```
    #[inline]
    pub const fn is_empty(&self) -> bool {
        self.size == 0
    }

    /// Get the shift value for accessing elements at the current tree height.
    ///
    /// The shift value is used for bit operations in the tree traversal algorithm.
    /// It depends on the height of the tree and the number of bits used for indexing
    /// at each level.
    #[inline]
    pub fn shift(&self) -> usize {
        if self.height == 0 {
            0
        } else {
            self.height * NODE_BITS
        }
    }

    /// Get a reference to the element at the specified index.
    ///
    /// Returns `None` if the index is out of bounds.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::tree::Tree;
    ///
    /// let tree = Tree::from_slice(&[10, 20, 30]);
    /// assert_eq!(tree.get(1), Some(&20));
    /// assert_eq!(tree.get(5), None); // Out of bounds
    /// ```
    #[inline]
    pub fn get(&self, index: usize) -> Option<&T> {
        // Check bounds first for early return
        if index >= self.size {
            return None;
        }

        // Fast path for leaf-only trees (height 0)
        if self.height == 0 {
            if let Node::Leaf { ref elements } = *self.root {
                return elements.get(index);
            }
            unreachable!("Leaf-only tree with height 0 contains a branch node");
        }

        // Cache-based path (currently unused but preserved for future implementation)
        if self.cache.has_index(index) {
            // Will be implemented in the future
        }

        // Traverse the tree for multi-level trees
        self.root.get(index, self.shift())
    }

    /// Update an element at the specified index, returning a new tree.
    ///
    /// Returns the original tree if the index is out of bounds.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::tree::Tree;
    ///
    /// let tree = Tree::from_slice(&[10, 20, 30]);
    /// let updated_tree = tree.update(1, 25);
    /// assert_eq!(updated_tree.get(1), Some(&25));
    /// assert_eq!(tree.get(1), Some(&20)); // Original unchanged
    /// ```
    #[inline]
    pub fn update(&self, index: usize, value: T) -> Self {
        if index >= self.size {
            return self.clone();
        }

        let shift = self.shift();
        match self.root.update(&self.manager, index, value, shift) {
            Some(new_root) => {
                let mut result = self.clone();
                result.root = new_root;
                result.cache.invalidate();
                result
            }
            None => self.clone(),
        }
    }

    /// Add an element to the end of the tree.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::tree::Tree;
    ///
    /// let tree = Tree::new();
    /// let tree = tree.push_back(10);
    /// let tree = tree.push_back(20);
    /// assert_eq!(tree.len(), 2);
    /// assert_eq!(tree.get(1), Some(&20));
    /// ```
    pub fn push_back(&self, value: T) -> Self {
        let shift = self.shift();
        let (new_root, split, overflow) = self.root.push_back(&self.manager, value, shift);

        let mut result = self.clone();
        result.size += 1;
        result.cache.invalidate();

        if split {
            // Create a new root to handle the overflow
            let mut root = self.manager.acquire_node();
            let mut children = Vec::with_capacity(2); // Only need space for 2 nodes
            children.push(Some(new_root.clone()));

            if let Some(overflow_node) = overflow.clone() {
                children.push(Some(overflow_node));
            }

            // Create a minimal size table
            let first_size = new_root.size();
            let mut size_table = Vec::with_capacity(2);
            size_table.push(first_size);

            if let Some(ref overflow_node) = overflow {
                size_table.push(first_size + overflow_node.size());
            }

            *root.get_mut().unwrap() = Node::Branch {
                children,
                sizes: Some(size_table),
            };

            result.root = root;
            result.height += 1;
        } else {
            result.root = new_root;
        }

        result
    }

    /// Remove the last element from the tree.
    ///
    /// Returns a tuple containing the new tree and the removed element,
    /// or `None` if the tree is empty.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::tree::Tree;
    ///
    /// let tree = Tree::from_slice(&[10, 20, 30, 40, 50]);
    /// let (new_tree, element) = tree.pop_back().unwrap();
    /// assert_eq!(element, 50);
    /// assert_eq!(new_tree.len(), 4);
    /// ```
    pub fn pop_back(&self) -> Option<(Self, T)> {
        if self.is_empty() {
            return None;
        }

        // Helper function to recursively pop an element
        fn pop_recursive<T: Clone>(
            node: &ManagedRef<Node<T>>,
            manager: &MemoryManager<T>,
            shift: usize,
        ) -> Option<(ManagedRef<Node<T>>, T)> {
            match **node {
                Node::Leaf { ref elements } => {
                    let mut new_elements = manager.acquire_chunk();
                    let element_count = elements.len();

                    if element_count == 0 {
                        return None;
                    }

                    // Copy all elements except the last one
                    for i in 0..(element_count - 1) {
                        new_elements
                            .get_mut()
                            .unwrap()
                            .push_back(elements.as_ref()[i].clone());
                    }

                    // Get the last element
                    let last_element = elements.as_ref()[element_count - 1].clone();

                    // Create a new leaf node
                    let new_node = Node::leaf(new_elements);
                    let mut new_node_ref = manager.acquire_node();
                    *new_node_ref.get_mut().unwrap() = new_node;

                    Some((new_node_ref, last_element))
                }
                Node::Branch {
                    ref children,
                    ref sizes,
                } => {
                    let last_child_idx = if let Some(ref sizes) = sizes {
                        // Find the last non-empty child using the size table
                        if sizes.is_empty() {
                            return None;
                        }
                        let mut idx = sizes.len() - 1;
                        while idx > 0 && sizes[idx] == sizes[idx - 1] {
                            idx -= 1;
                        }
                        idx
                    } else {
                        // For regular nodes, find the last non-empty child
                        let mut idx = children.len() - 1;
                        while idx > 0 && children[idx].is_none() {
                            idx -= 1;
                        }
                        idx
                    };

                    if last_child_idx >= children.len() || children[last_child_idx].is_none() {
                        return None;
                    }

                    let last_child = &children[last_child_idx];
                    let new_shift = shift.saturating_sub(NODE_BITS);

                    if let Some(ref child) = last_child {
                        let pop_result = pop_recursive(child, manager, new_shift);

                        if let Some((new_child, value)) = pop_result {
                            // Create a new branch node with the updated child
                            let mut new_children = Vec::with_capacity(children.len());
                            let mut new_sizes = None;

                            // Copy the size table if present
                            if let Some(ref sizes) = sizes {
                                let mut new_size_table = Vec::with_capacity(sizes.len());
                                for (i, &size) in sizes.iter().enumerate() {
                                    if i == last_child_idx {
                                        // Update the size for the last child
                                        let new_size = if i > 0 {
                                            sizes[i - 1] + new_child.size()
                                        } else {
                                            new_child.size()
                                        };
                                        new_size_table.push(new_size);
                                    } else {
                                        new_size_table.push(size);
                                    }
                                }
                                new_sizes = Some(new_size_table);
                            }

                            // Copy the children
                            for (i, child) in children.iter().enumerate() {
                                if i == last_child_idx {
                                    if new_child.is_empty() {
                                        new_children.push(None);
                                    } else {
                                        new_children.push(Some(new_child.clone()));
                                    }
                                } else {
                                    new_children.push(child.clone());
                                }
                            }

                            // Create the new branch node
                            let new_node = Node::Branch {
                                children: new_children,
                                sizes: new_sizes,
                            };

                            let mut new_node_ref = manager.acquire_node();
                            *new_node_ref.get_mut().unwrap() = new_node;

                            Some((new_node_ref, value))
                        } else {
                            None
                        }
                    } else {
                        None
                    }
                }
            }
        }

        // Attempt to pop the last element
        let result = pop_recursive(&self.root, &self.manager, self.shift());

        if let Some((new_root, value)) = result {
            let mut new_tree = self.clone();
            new_tree.root = new_root;
            new_tree.size -= 1;
            new_tree.cache.invalidate();

            // Check if we need to decrease the height of the tree
            if new_tree.height > 0 {
                if let Node::Branch { ref children, .. } = *new_tree.root {
                    let non_empty_children = children.iter().filter(|c| c.is_some()).count();

                    if non_empty_children == 1 {
                        // Only one child, we can decrease the height
                        if let Some(child) = children.iter().flatten().next() {
                            new_tree.root = child.clone();
                            new_tree.height -= 1;
                        }
                    }
                }
            }

            Some((new_tree, value))
        } else {
            None
        }
    }

    /// Set the memory manager for this tree.
    ///
    /// This can be used to customize how memory is allocated and recycled
    /// for tree operations.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::tree::Tree;
    /// use rustica::pvec::memory::{MemoryManager, AllocationStrategy};
    ///
    /// let mut tree: Tree<i32> = Tree::new();
    /// let manager = MemoryManager::new(AllocationStrategy::Direct);
    /// tree.set_memory_manager(manager);
    /// ```
    #[inline]
    pub fn set_memory_manager(&mut self, manager: MemoryManager<T>) {
        self.manager = manager;
    }

    /// Converts this tree to an `Arc<Tree<T>>`.
    ///
    /// This is useful when you want to share the tree across multiple
    /// threads or owners, while preserving its immutable nature.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::tree::Tree;
    /// use std::sync::Arc;
    ///
    /// let tree = Tree::from_slice(&[1, 2, 3]);
    /// let arc_tree = tree.to_arc();
    /// assert_eq!(arc_tree.len(), 3);
    /// ```
    #[inline]
    pub fn to_arc(self) -> Arc<Self> {
        Arc::new(self)
    }
}

impl<T: Clone> Default for Tree<T> {
    #[inline]
    fn default() -> Self {
        Self::new()
    }
}

impl<T: Clone + Debug> Debug for Tree<T> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Tree {{ size: {}, height: {} }}", self.size, self.height)
    }
}

impl<T: Clone> FromIterator<T> for Tree<T> {
    #[inline]
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        let mut tree = Self::new();
        for item in iter {
            tree = tree.push_back(item);
        }
        tree
    }
}
