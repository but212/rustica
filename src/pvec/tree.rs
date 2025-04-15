//! Persistent Vector Tree Module
//!
//! This module implements the core tree structure for the persistent vector.
//!
//! This module defines the Tree type, which is the main data structure
//! for the persistent vector. It manages a root node and provides vector operations.
//!
//! The Tree type implements a Relaxed Radix Balanced (RRB) tree, which is a
//! persistent data structure optimized for both random access and structural
//! updates at the ends. It provides efficient index-based access, append, and
//! prepend operations.

use std::fmt::{self, Debug};
use std::iter::FromIterator;
use std::sync::Arc;

use crate::pvec::cache::IndexCache;
use crate::pvec::chunk::Chunk;
use crate::pvec::memory::{AllocationStrategy, ManagedRef, MemoryManager};
use crate::pvec::node::{Node, NODE_BITS};

/// A persistent vector implemented as a Relaxed Radix Balanced (RRB) tree.
///
/// The tree provides efficient indexing, updating, and appending operations
/// with persistence guarantees. All operations create a new version of the
/// tree without modifying the original, allowing for efficient structural
/// sharing between different versions.
#[derive(Clone)]
pub(crate) struct Tree<T> {
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
    #[inline(always)]
    #[must_use]
    pub fn new() -> Self {
        let manager = MemoryManager::new(AllocationStrategy::Direct);
        let chunk = Chunk::new();
        let root = Node::leaf(ManagedRef::new(Arc::new(chunk)));
        Self {
            root: ManagedRef::new(Arc::new(root)),
            size: 0,
            height: 0,
            manager,
            cache: IndexCache::new(),
        }
    }

    /// Create a new tree from a slice of elements.
    #[inline(always)]
    #[must_use]
    pub fn from_slice(slice: &[T]) -> Self
    where
        T: Clone,
    {
        if slice.is_empty() {
            return Self::new();
        }
        let manager = MemoryManager::new(AllocationStrategy::Direct);
        let mut result = Self {
            root: ManagedRef::new(Arc::new(Node::leaf(ManagedRef::new(
                Arc::new(Chunk::new()),
            )))),
            size: 0,
            height: 0,
            manager,
            cache: IndexCache::default(),
        };
        // Efficiently push elements in chunks
        for chunk in slice.chunks(crate::pvec::chunk::CHUNK_SIZE) {
            for item in chunk {
                result = result.push_back(item.clone());
            }
        }
        result
    }

    /// Get the number of elements in the tree.
    ///
    /// This operation is O(1) as the size is cached at the tree level.
    #[inline(always)]
    #[must_use]
    pub const fn len(&self) -> usize {
        self.size
    }

    /// Check if the tree is empty (contains no elements).
    #[inline(always)]
    #[must_use]
    pub const fn is_empty(&self) -> bool {
        self.size == 0
    }

    /// Get the shift value for accessing elements at the current tree height.
    #[inline(always)]
    #[must_use]
    pub fn shift(&self) -> usize {
        self.height * NODE_BITS
    }

    /// Get a reference to the element at the specified index.
    ///
    /// Returns `None` if the index is out of bounds.
    #[inline(always)]
    pub fn get(&self, index: usize) -> Option<&T> {
        if index >= self.size {
            return None;
        }
        self.root.get(index, self.shift())
    }

    /// Update an element at the specified index, returning a new tree.
    ///
    /// Returns the original tree if the index is out of bounds.
    #[inline(always)]
    #[must_use]
    pub fn update(&self, index: usize, value: T) -> Self {
        if index >= self.size {
            return self.clone();
        }
        if let Some(new_root) = self.root.update(&self.manager, index, value, self.shift()) {
            Self {
                root: new_root,
                size: self.size,
                height: self.height,
                manager: self.manager.clone(),
                cache: IndexCache::new(),
            }
        } else {
            self.clone()
        }
    }

    /// Splits the tree into two parts at the given index.
    ///
    /// Returns a tuple containing two trees: the first with elements from `0..index`,
    /// and the second with elements from `index..len`.
    #[inline(always)]
    #[must_use]
    pub fn split_at(&self, index: usize) -> (Self, Self) {
        if index >= self.size {
            return (self.clone(), Self::new());
        }
        if index == 0 {
            return (Self::new(), self.clone());
        }
        let (left, right) = self.root.split(index, self.shift());
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

    /// Add an element to the end of the tree.
    #[inline(always)]
    #[must_use]
    pub fn push_back(&self, value: T) -> Self {
        let shift = self.shift();
        let (new_root, split, overflow) = self.root.push_back(value, shift);

        let mut result = self.clone();
        result.size += 1;
        result.cache.invalidate();

        if split {
            // Create a new root to handle the overflow
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

            let new_branch = Node::Branch {
                children,
                sizes: Some(size_table),
            };

            result.root = ManagedRef::new(Arc::new(new_branch));
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
    #[inline(always)]
    #[must_use]
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

    /// Collect all elements in the tree into a Vec
    #[inline(always)]
    #[must_use]
    pub fn to_vec(&self) -> Vec<T> {
        let mut out = Vec::with_capacity(self.size);
        for i in 0..self.size {
            if let Some(val) = self.get(i) {
                out.push(val.clone());
            }
        }
        out
    }
}

impl<T: PartialEq> PartialEq for Tree<T> {
    #[inline(always)]
    fn eq(&self, other: &Self) -> bool {
        self.size == other.size && self.height == other.height && *self.root == *other.root
    }
}

impl<T: Eq> Eq for Tree<T> {}

impl<T: Clone> Default for Tree<T> {
    #[inline(always)]
    fn default() -> Self {
        Self::new()
    }
}

impl<T: Clone + Debug> Debug for Tree<T> {
    #[inline(always)]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Tree")
            .field("size", &self.size)
            .field("height", &self.height)
            .field("root", &self.root)
            .finish()
    }
}

impl<T: Clone> FromIterator<T> for Tree<T> {
    #[inline(always)]
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        let mut tree = Self::new();
        for item in iter {
            tree = tree.push_back(item);
        }
        tree
    }
}
