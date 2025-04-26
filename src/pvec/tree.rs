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

use crate::pvec::memory::IndexCache;
use crate::pvec::memory::{AllocationStrategy, BoxedCachePolicy, Chunk, ManagedRef, MemoryManager};
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

    /// Policy for controlling when to use the cache.
    ///
    /// This policy determines when the cache should be used for operations.
    /// It can be set to control caching behavior dynamically.
    cache_policy: BoxedCachePolicy,

    /// The chunk size used for allocating chunks.
    chunk_size: usize,
}

impl<T: Clone> Tree<T> {
    /// Create a new, empty tree with the given chunk size.
    #[inline(always)]
    #[must_use]
    pub fn new_with_chunk_size(chunk_size: usize) -> Self {
        let manager = MemoryManager::new(AllocationStrategy::Direct);
        let chunk = manager.allocate_chunk(Chunk::new_with_size(chunk_size));
        let root = manager.allocate_node(Node::leaf(chunk));
        Self {
            root,
            size: 0,
            height: 0,
            manager,
            cache: IndexCache::new(),
            cache_policy: Box::new(crate::pvec::memory::AlwaysCache),
            chunk_size,
        }
    }

    /// Create a new, empty tree with the default chunk size.
    #[inline(always)]
    #[must_use]
    pub fn new() -> Self {
        Self::new_with_chunk_size(crate::pvec::memory::DEFAULT_CHUNK_SIZE)
    }

    /// Create a new tree from a slice of elements, with the given chunk size.
    #[inline(always)]
    #[must_use]
    pub fn from_slice_with_chunk_size(slice: &[T], chunk_size: usize) -> Self {
        use crate::pvec::memory::Chunk;
        use crate::pvec::node::{Node, NODE_SIZE};

        if slice.is_empty() {
            return Self::new_with_chunk_size(chunk_size);
        }

        // Step 1: Create leaf nodes from chunks
        let mut leaf_nodes = Vec::new();
        let mut size = 0;
        let manager = MemoryManager::new(AllocationStrategy::Direct);
        for chunk in slice.chunks(chunk_size) {
            let mut c = Chunk::new_with_size(chunk_size);
            for item in chunk {
                c.push_back(item.clone());
            }
            size += c.len();
            let chunk_ref = manager.allocate_chunk(c);
            leaf_nodes.push(manager.allocate_node(Node::leaf(chunk_ref)));
        }

        // Step 2: Build tree from leaves upward
        let mut current_level = leaf_nodes;
        let mut height = 0;
        while current_level.len() > 1 {
            let mut next_level = Vec::new();
            for children in current_level.chunks(NODE_SIZE) {
                let mut child_vec = Vec::with_capacity(children.len());
                let mut sizes = Vec::with_capacity(children.len());
                let mut acc = 0;
                for child in children {
                    let node_size = child.size();
                    acc += node_size;
                    sizes.push(acc);
                    child_vec.push(Some(child.clone()));
                }
                let branch = manager.allocate_node(Node::Branch {
                    children: child_vec,
                    sizes: Some(sizes),
                });
                next_level.push(branch);
            }
            current_level = next_level;
            height += 1;
        }

        let root = current_level.into_iter().next().unwrap();
        Self {
            root,
            size,
            height,
            manager,
            cache: IndexCache::default(),
            cache_policy: Box::new(crate::pvec::memory::AlwaysCache),
            chunk_size,
        }
    }

    /// Create a new tree from a slice of elements, with the default chunk size.
    #[inline(always)]
    #[must_use]
    pub fn from_slice(slice: &[T]) -> Self {
        Self::from_slice_with_chunk_size(slice, crate::pvec::memory::DEFAULT_CHUNK_SIZE)
    }

    /// Set the cache policy for this tree.
    pub fn with_cache_policy(mut self, policy: BoxedCachePolicy) -> Self {
        self.cache_policy = policy;
        self
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
        // NOTE: This immutable get does not use the cache for now.
        self.root.get(index, self.shift())
    }

    /// Get a reference to the element at the specified index, using the index cache if policy allows.
    pub fn get_with_cache(&mut self, index: usize) -> Option<&T> {
        if !(self.cache_policy.should_cache(index)) {
            // Policy says not to use cache: standard access
            return self.root.get(index, self.shift());
        }
        if index >= self.size {
            return None;
        }
        // Fast path: cache hit
        if self.cache.is_valid() && self.cache.index == index {
            self.cache.record_hit();
            // In a full implementation, we would use cached path/ranges to avoid traversal.
            // For now, just count as a hit and fall through to standard access.
        } else {
            self.cache.record_miss();
        }
        // Standard access (traverse tree)
        let result = self.root.get(index, self.shift());
        // Update cache with the accessed index (stub: not storing real path/ranges yet)
        // In a real implementation, path/ranges would be computed during traversal.
        self.cache
            .update(index, &[0; 32], &core::array::from_fn::<_, 32, _>(|_| 0..0));
        result
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
                cache_policy: self.cache_policy.clone(),
                chunk_size: self.chunk_size,
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
        let (left, right) = match self.height {
            0 => {
                // Handle split for leaf node directly
                let chunk = match self.root.as_ref() {
                    crate::pvec::node::Node::Leaf { elements } => elements,
                    _ => panic!("Expected leaf node at height 0"),
                };
                let total = chunk.len();
                if index > total {
                    panic!(
                        "Split index {} out of bounds for leaf of size {}",
                        index, total
                    );
                }
                let left_chunk = self.manager.allocate_chunk({
                    let mut c = crate::pvec::memory::Chunk::new_with_size(chunk.len());
                    for i in 0..index {
                        if let Some(val) = chunk.get(i) {
                            c.push_back(val.clone());
                        }
                    }
                    c
                });
                let right_chunk = self.manager.allocate_chunk({
                    let mut c = crate::pvec::memory::Chunk::new_with_size(chunk.len());
                    for i in index..total {
                        if let Some(val) = chunk.get(i) {
                            c.push_back(val.clone());
                        }
                    }
                    c
                });
                let left_node = self.manager.allocate_node(crate::pvec::node::Node::Leaf {
                    elements: left_chunk,
                });
                let right_node = self.manager.allocate_node(crate::pvec::node::Node::Leaf {
                    elements: right_chunk,
                });
                (left_node, right_node)
            },
            _ => match self.root.split(index, self.shift(), &self.manager) {
                Ok((l, r)) => (l, r),
                Err(e) => panic!("Failed to split tree: {}", e),
            },
        };
        (
            Self {
                root: left,
                size: index,
                height: self.height,
                manager: self.manager.clone(),
                cache: IndexCache::new(),
                cache_policy: self.cache_policy.clone(),
                chunk_size: self.chunk_size,
            },
            Self {
                root: right,
                size: self.size - index,
                height: self.height,
                manager: self.manager.clone(),
                cache: IndexCache::new(),
                cache_policy: self.cache_policy.clone(),
                chunk_size: self.chunk_size,
            },
        )
    }

    /// Add an element to the end of the tree.
    #[inline(always)]
    #[must_use]
    pub fn push_back(&self, value: T) -> Self {
        let shift = self.shift();
        let (new_root, split, overflow) =
            self.root
                .push_back(value, shift, self.chunk_size, &self.manager);

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

            let new_branch = self.manager.allocate_node(Node::Branch {
                children,
                sizes: Some(size_table),
            });

            result.root = new_branch;
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
        let (mut new_tree, _) = self.split_at(last_idx);
        // If after pop the tree is empty, reset height to 0 and root to a new empty leaf
        if new_tree.size == 0 {
            let chunk = self
                .manager
                .allocate_chunk(crate::pvec::memory::Chunk::new_with_size(self.chunk_size));
            let root = self
                .manager
                .allocate_node(crate::pvec::node::Node::leaf(chunk));
            new_tree.root = root;
            new_tree.height = 0;
        }

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

    /// Returns the cache hit/miss statistics as a tuple (hits, misses).
    pub fn cache_stats(&self) -> (usize, usize) {
        (self.cache.hits, self.cache.misses)
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
        let vec: Vec<T> = iter.into_iter().collect();
        // Use the default chunk size for consistency
        Self::from_slice_with_chunk_size(&vec, crate::pvec::memory::DEFAULT_CHUNK_SIZE)
    }
}
