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

    /// Create a new empty tree, discarding all elements from the current tree.
    ///
    /// This operation returns a completely new empty tree, preserving none of
    /// the elements from the original tree.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::tree::Tree;
    ///
    /// let tree = Tree::from_slice(&[1, 2, 3]);
    /// let empty_tree = tree.clear();
    /// assert_eq!(empty_tree.len(), 0);
    /// assert!(empty_tree.is_empty());
    /// ```
    #[inline]
    pub fn clear(&self) -> Self {
        Self::new()
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

    /// Creates a new tree containing elements from a range of the original tree.
    ///
    /// Returns a new tree containing elements from index `start` (inclusive) to
    /// index `end` (exclusive). If `start` is greater than or equal to `end`, or
    /// if `start` is greater than or equal to the tree's size, an empty tree
    /// is returned.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::tree::Tree;
    ///
    /// let tree = Tree::from_slice(&[1, 2, 3, 4, 5]);
    /// let sliced = tree.slice(1, 4);
    /// assert_eq!(sliced.len(), 3);
    /// assert_eq!(sliced.get(0), Some(&2));
    /// assert_eq!(sliced.get(2), Some(&4));
    /// assert_eq!(tree.len(), 5); // Original unchanged
    /// ```
    #[inline]
    pub fn slice(&self, start: usize, end: usize) -> Self {
        if start >= self.size || end > self.size || start > end {
            return Self::new();
        }

        let size = end - start;
        if size == 0 {
            return Self::new();
        }

        // Use split_at for more efficient slicing
        let (_, right) = self.split_at(start);
        let (result, _) = right.split_at(size);
        result
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

    /// Returns a new tree with elements in the specified range removed.
    ///
    /// This creates a new tree with all elements from the original tree except those in the range
    /// from `start` (inclusive) to `end` (exclusive). If the range is invalid (e.g., `start` > `end` or
    /// the range is out of bounds), the original tree is returned unchanged.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::tree::Tree;
    ///
    /// let tree = Tree::from_slice(&[1, 2, 3, 4, 5]);
    /// let new_tree = tree.drain(1, 3);
    /// assert_eq!(new_tree.len(), 3);
    /// assert_eq!(new_tree.get(0), Some(&1));
    /// assert_eq!(new_tree.get(1), Some(&4));
    /// assert_eq!(new_tree.get(2), Some(&5));
    /// assert_eq!(tree.len(), 5); // Original unchanged
    /// ```
    pub fn drain(&self, start: usize, end: usize) -> Self {
        if start >= end || start >= self.size {
            return self.clone();
        }

        if end >= self.size {
            return self.slice(0, start);
        }

        // Use split_at for more efficient range operations
        let (prefix, suffix_with_middle) = self.split_at(start);
        let (_, suffix) = suffix_with_middle.split_at(end - start);

        // More efficiently combine the prefix and suffix
        if prefix.is_empty() {
            return suffix;
        }

        if suffix.is_empty() {
            return prefix;
        }

        // For larger trees, use more efficient concatenation
        prefix.concat(&suffix)
    }

    /// Resize the tree to contain exactly `new_len` elements.
    ///
    /// If the new length is greater than the current length, the tree is
    /// extended with copies of the provided value. If the new length is less
    /// than the current length, the tree is truncated.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::tree::Tree;
    ///
    /// let tree = Tree::from_slice(&[1, 2, 3]);
    ///
    /// // Extend the tree
    /// let extended = tree.resize(5, 0);
    /// assert_eq!(extended.len(), 5);
    /// assert_eq!(extended.get(3), Some(&0));
    ///
    /// // Truncate the tree
    /// let truncated = tree.resize(2, 0);
    /// assert_eq!(truncated.len(), 2);
    /// assert_eq!(truncated.get(2), None);
    /// ```
    pub fn resize(&self, new_len: usize, value: T) -> Self {
        let mut result = self.clone();

        match new_len.cmp(&self.size) {
            std::cmp::Ordering::Greater => {
                for _ in 0..(new_len - self.size) {
                    result = result.push_back(value.clone());
                }
            },
            std::cmp::Ordering::Less => {
                result = result.slice(0, new_len);
            },
            _ => {},
        }

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

    /// Returns a new tree with all elements from `self` and `other` appended to the end.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::tree::Tree;
    ///
    /// let tree1 = Tree::from_slice(&[1, 2, 3]);
    /// let tree2 = Tree::from_slice(&[4, 5, 6]);
    /// let tree3 = tree1.concat(&tree2);
    /// assert_eq!(tree3.len(), 6);
    /// assert_eq!(tree3.get(0), Some(&1));
    /// assert_eq!(tree3.get(5), Some(&6));
    /// ```
    pub fn concat(&self, other: &Self) -> Self {
        let mut result = self.clone();
        for i in 0..other.size {
            if let Some(value) = other.get(i) {
                result = result.push_back(value.clone());
            }
        }
        result
    }

    /// Returns a new tree with all elements from the provided iterator appended to the end.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::tree::Tree;
    ///
    /// let tree = Tree::from_slice(&[1, 2, 3]);
    /// let extended = tree.extend(vec![4, 5, 6]);
    /// assert_eq!(extended.len(), 6);
    /// assert_eq!(extended.get(5), Some(&6));
    /// assert_eq!(tree.len(), 3); // Original unchanged
    /// ```
    pub fn extend(&self, values: impl IntoIterator<Item = T>) -> Self {
        let mut tree = self.clone();
        for value in values {
            tree = tree.push_back(value);
        }
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
    #[inline]
    pub fn truncate(&self, new_len: usize) -> Self {
        if new_len >= self.size {
            return self.clone();
        }

        if new_len == 0 {
            return Self::new();
        }

        // Use split_at for more efficient implementation
        let (result, _) = self.split_at(new_len);
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

        // Split at the position where we want to remove the element
        let (left, right) = self.split_at(index);

        // Get the remaining right part excluding the first element
        let remaining_right = right.slice(1, right.len());

        // Merge the left part with the remaining right part
        left.concat(&remaining_right)
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

    /// Returns a new tree with all elements in reverse order.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::tree::Tree;
    ///
    /// let tree = Tree::from_slice(&[1, 2, 3, 4]);
    /// let reversed = tree.reverse();
    /// assert_eq!(reversed.len(), 4);
    /// assert_eq!(reversed.get(0), Some(&4));
    /// assert_eq!(reversed.get(1), Some(&3));
    /// assert_eq!(reversed.get(2), Some(&2));
    /// assert_eq!(reversed.get(3), Some(&1));
    /// ```
    pub fn reverse(&self) -> Self {
        let mut result = Self::new();

        // Process elements in reverse order
        for i in (0..self.size).rev() {
            if let Some(value) = self.get(i) {
                result = result.push_back(value.clone());
            }
        }

        result
    }

    /// Rotate the tree to the left by one position.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::tree::Tree;
    ///
    /// let tree = Tree::from_slice(&[1, 2, 3, 4]);
    /// let rotated = tree.rotate_left();
    /// assert_eq!(rotated.len(), 4);
    /// assert_eq!(rotated.get(0), Some(&2));
    /// assert_eq!(rotated.get(1), Some(&3));
    /// assert_eq!(rotated.get(2), Some(&4));
    /// assert_eq!(rotated.get(3), Some(&1));
    /// ```
    pub fn rotate_left(&self) -> Self {
        if self.size <= 1 {
            return self.clone();
        }

        let mut result = Self::new();

        // First add elements from index 1 to end
        for i in 1..self.size {
            if let Some(value) = self.get(i) {
                result = result.push_back(value.clone());
            }
        }

        // Then add the first element at the end
        if let Some(first) = self.get(0) {
            result = result.push_back(first.clone());
        }

        result
    }

    /// Rotate the tree to the right by one position.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::tree::Tree;
    ///
    /// let tree = Tree::from_slice(&[1, 2, 3, 4]);
    /// let rotated = tree.rotate_right();
    /// assert_eq!(rotated.len(), 4);
    /// assert_eq!(rotated.get(0), Some(&4));
    /// assert_eq!(rotated.get(1), Some(&1));
    /// assert_eq!(rotated.get(2), Some(&2));
    /// assert_eq!(rotated.get(3), Some(&3));
    /// ```
    #[inline]
    pub fn rotate_right(&self) -> Self {
        self.reverse().rotate_left().reverse()
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
    pub fn get(&self, index: usize) -> Option<&T> {
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

        // Check if the index is in cache and the cache is valid
        if self.cache.valid && self.cache.has_index(index) {
            // Use cached path for fast access
            let mut current = &self.root;
            let mut current_index = index;
            let mut shift = self.shift();

            for level in 0..self.height {
                if let Some(path_idx) = self.cache.get_path_index(level) {
                    if level < self.cache.ranges.len() {
                        // Get the range at the current level
                        let range = &self.cache.ranges[level];

                        // Calculate relative index
                        current_index = index - range.start;

                        if let Node::Branch { children, .. } = &**current {
                            if path_idx < children.len() {
                                if let Some(child) = &children[path_idx] {
                                    current = child;
                                    shift -= NODE_BITS;
                                    continue;
                                }
                            }
                        }
                    }
                }
                // Fall back to normal traversal if we can't follow the cache path
                return self.root.get(index, self.shift());
            }

            // Find the element in the last subtree (using adjusted index)
            return current.get(current_index, shift);
        }

        // Normal tree traversal without cache
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
            },
            None => self.clone(),
        }
    }

    /// Splits the tree into two parts at the given index.
    ///
    /// Returns a tuple containing two trees: the first with elements from `0..index`,
    /// and the second with elements from `index..len`.
    ///
    /// If `index` is greater than the length, the first tree will contain
    /// all elements and the second will be empty. If `index` is equal to the length,
    /// the first tree will contain all elements and the second will be empty.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::tree::Tree;
    ///
    /// let tree = Tree::from_slice(&[1, 2, 3, 4, 5]);
    /// let (left, right) = tree.split_at(2);
    ///
    /// assert_eq!(left.len(), 2);
    /// assert_eq!(right.len(), 3);
    /// assert_eq!(left.get(0), Some(&1));
    /// assert_eq!(right.get(0), Some(&3));
    /// ```
    pub fn split_at(&self, index: usize) -> (Self, Self) {
        if index > self.size {
            return (self.clone(), Self::new());
        }

        if index == self.size {
            return (self.clone(), Self::new());
        }

        let (left, right) = self.root.split(&self.manager, index, self.shift());

        (
            Self {
                root: left,
                size: index,
                height: self.height,
                manager: self.manager.clone(),
                cache: IndexCache::new(),
            },
            Self {
                root: right,
                size: self.size - index,
                height: self.height,
                manager: self.manager.clone(),
                cache: IndexCache::new(),
            },
        )
    }

    /// Insert a value at the specified index in the tree.
    ///
    /// Returns a new tree with the value inserted. If the index is greater than
    /// the size of the tree, returns a clone of the original tree.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::tree::Tree;
    ///
    /// let tree = Tree::from_slice(&[1, 2, 4]);
    /// let tree = tree.insert(2, 3);
    /// assert_eq!(tree.len(), 4);
    /// assert_eq!(tree.get(2), Some(&3));
    /// ```
    pub fn insert(&self, index: usize, value: T) -> Self {
        if index > self.size {
            return self.clone();
        }

        if index == self.size {
            return self.push_back(value);
        }

        // For all insertions (including at index 0)
        let (left, right) = self.split_at(index);
        left.push_back(value).concat(&right)
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

        let last_idx = self.size - 1;
        let last_element = self.get(last_idx)?.clone();

        // Create new tree without the last element
        let (new_tree, _) = self.split_at(last_idx);

        Some((new_tree, last_element))
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
        let iter = iter.into_iter();

        // Optimize by pre-allocating chunks when possible
        if let Some(size_hint) = iter.size_hint().1 {
            tree.manager.reserve_chunks(size_hint / NODE_SIZE + 1);
        }

        for item in iter {
            tree = tree.push_back(item);
            // Avoid cache invalidation on each push for better performance
            tree.cache.valid = true;
        }

        // Final cache invalidation to ensure consistent state
        tree.cache.invalidate();
        tree
    }
}
