//! Index Caching Module
//!
//! This module provides caching functionality for improved performance when
//! accessing vector elements. It keeps track of the path taken to reach
//! a specific index, allowing for faster access to nearby indices.
//!
//! The caching system works by storing:
//! - The most recently accessed index
//! - The path through the tree structure used to reach that index
//! - The range of indices covered at each level of the tree
//!
//! This approach significantly improves performance for sequential or
//! localized access patterns, reducing tree traversal from O(log n) to
//! nearly O(1) for many common operations.

use std::ops::Range;

/// Maximum number of levels in the tree structure to cache
pub(super) const MAX_CACHE_LEVELS: usize = 10;

/// A cache for optimizing repeated index operations in the vector.
///
/// This cache remembers the path to the most recently accessed index,
/// which can significantly speed up access to nearby indices.
///
/// The cache stores:
/// - The index that was last accessed
/// - The path through the tree to reach that index
/// - The range of indices covered at each level of the path
///
/// When accessing elements sequentially or in nearby locations,
/// this cache can reduce tree traversal time from O(log n) to O(1)
/// in many cases.
#[derive(Clone, Debug)]
pub(super) struct IndexCache {
    /// The currently cached index
    pub index: usize,

    /// The path from the root to the cached index (indices at each level)
    pub path: Vec<usize>,

    /// The ranges covered by each level in the path
    pub ranges: Vec<Range<usize>>,

    /// Whether the cache is currently valid
    pub valid: bool,
}

impl IndexCache {
    /// Create a new, empty index cache.
    ///
    /// This creates a cache with no valid path or index.
    #[inline]
    pub fn new() -> Self {
        Self {
            index: 0,
            path: Vec::with_capacity(MAX_CACHE_LEVELS),
            ranges: Vec::with_capacity(MAX_CACHE_LEVELS),
            valid: false,
        }
    }

    /// Clear the cache, marking it as invalid.
    ///
    /// This removes any cached path and index information.
    #[inline]
    pub fn invalidate(&mut self) {
        self.valid = false;
    }

    /// Check if the cache contains information for the given index.
    #[inline]
    pub fn has_index(&self, index: usize) -> bool {
        self.valid && self.index == index
    }

    /// Get the cached path index for a specific level.
    #[inline]
    pub fn get_path_index(&self, level: usize) -> Option<usize> {
        if self.valid && level < self.path.len() {
            Some(self.path[level])
        } else {
            None
        }
    }
}

impl PartialEq for IndexCache {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        // Check only the cached index and validity state
        // Path and ranges are implementation details that don't affect equality
        self.index == other.index && self.valid == other.valid
    }
}

impl Eq for IndexCache {}

impl Default for IndexCache {
    #[inline]
    fn default() -> Self {
        Self::new()
    }
}
