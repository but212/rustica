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
    pub path: [usize; MAX_CACHE_LEVELS],

    /// The ranges covered by each level in the path
    pub ranges: [Range<usize>; MAX_CACHE_LEVELS],

    /// The number of valid levels in the path/ranges arrays
    pub len: usize,

    /// Cache hit counter (for profiling)
    pub hits: usize,
    /// Cache miss counter (for profiling)
    pub misses: usize,
}

impl IndexCache {
    /// Creates a new, invalid cache
    pub fn new() -> Self {
        Self {
            index: 0,
            path: [0; MAX_CACHE_LEVELS],
            ranges: core::array::from_fn(|_| 0..0),
            len: 0,
            hits: 0,
            misses: 0,
        }
    }

    /// Returns true if the cache is valid
    pub fn is_valid(&self) -> bool {
        self.len > 0
    }

    /// Invalidates the cache
    pub fn invalidate(&mut self) {
        self.len = 0;
    }

    /// Updates the cache with a new index, path, and ranges
    pub fn update(&mut self, index: usize, path: &[usize], ranges: &[Range<usize>]) {
        self.index = index;
        self.len = path.len().min(MAX_CACHE_LEVELS);
        self.path[..self.len].copy_from_slice(&path[..self.len]);
        self.ranges[..self.len].clone_from_slice(&ranges[..self.len]);
    }

    /// Record a cache hit (for profiling)
    pub fn record_hit(&mut self) {
        self.hits += 1;
    }

    /// Record a cache miss (for profiling)
    pub fn record_miss(&mut self) {
        self.misses += 1;
    }
}

impl PartialEq for IndexCache {
    #[inline(always)]
    fn eq(&self, other: &Self) -> bool {
        // Check only the cached index and validity state
        // Path and ranges are implementation details that don't affect equality
        self.index == other.index && (self.len > 0) == (other.len > 0)
    }
}

impl Eq for IndexCache {}

impl Default for IndexCache {
    #[inline(always)]
    fn default() -> Self {
        Self::new()
    }
}

pub trait CachePolicy: Send + Sync {
    /// Decide whether to use the cache for a given index.
    fn should_cache(&self, index: usize) -> bool;
    fn clone_box(&self) -> Box<dyn CachePolicy>;
}

impl Clone for Box<dyn CachePolicy> {
    fn clone(&self) -> Box<dyn CachePolicy> {
        self.clone_box()
    }
}

/// Always cache accesses (default policy).
#[derive(Clone)]
pub struct AlwaysCache;
impl CachePolicy for AlwaysCache {
    fn should_cache(&self, _index: usize) -> bool {
        true
    }
    fn clone_box(&self) -> Box<dyn CachePolicy> {
        Box::new(self.clone())
    }
}

/// Never use the cache.
#[derive(Clone)]
pub struct NeverCache;
impl CachePolicy for NeverCache {
    fn should_cache(&self, _index: usize) -> bool {
        false
    }
    fn clone_box(&self) -> Box<dyn CachePolicy> {
        Box::new(self.clone())
    }
}

/// Cache only even indices (example of custom logic).
#[derive(Clone)]
pub struct EvenIndexCache;
impl CachePolicy for EvenIndexCache {
    fn should_cache(&self, index: usize) -> bool {
        index % 2 == 0
    }
    fn clone_box(&self) -> Box<dyn CachePolicy> {
        Box::new(self.clone())
    }
}
