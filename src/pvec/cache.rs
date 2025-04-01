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
//!
//! # Examples
//!
//! ```
//! use rustica::pvec::cache::IndexCache;
//!
//! // Create a new cache
//! let mut cache = IndexCache::new();
//! assert!(!cache.valid);
//!
//! // Update the cache with path information
//! cache.update(10, vec![2, 1], vec![0..64, 32..48]);
//! assert!(cache.valid);
//!
//! // Check path information at different levels
//! assert!(cache.has_path_to(40, 0)); // Within first level range
//! assert!(cache.has_path_to(35, 1)); // Within second level range
//! assert!(!cache.has_path_to(50, 1)); // Outside second level range
//!
//! // Get path indices
//! assert_eq!(cache.get_path_index(0), Some(2));
//! assert_eq!(cache.get_path_index(1), Some(1));
//!
//! // Add a new level to the path
//! cache.push_level(3, 32..36);
//! assert_eq!(cache.get_path().collect::<Vec<_>>(), vec![(2, &(0..64)), (1, &(32..48)), (3, &(32..36))]);
//!
//! // Invalidate when done
//! cache.invalidate();
//! assert!(!cache.valid);
//! ```

use std::ops::Range;

/// Maximum number of levels in the tree structure to cache
pub const MAX_CACHE_LEVELS: usize = 10;

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
pub struct IndexCache {
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
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::cache::IndexCache;
    ///
    /// let cache = IndexCache::new();
    /// assert!(!cache.valid);
    /// ```
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
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::cache::IndexCache;
    ///
    /// let mut cache = IndexCache::new();
    /// cache.invalidate();
    /// assert!(!cache.valid);
    /// ```
    #[inline]
    pub fn invalidate(&mut self) {
        self.valid = false;
    }

    /// Check if the cache contains information for the given index.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::cache::IndexCache;
    ///
    /// let mut cache = IndexCache::new();
    /// cache.invalidate();
    /// assert!(!cache.has_index(0));
    /// ```
    #[inline]
    pub fn has_index(&self, index: usize) -> bool {
        self.valid && self.index == index
    }

    /// Check if the cache contains path information for a level containing the given index.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::cache::IndexCache;
    ///
    /// let mut cache = IndexCache::new();
    /// cache.invalidate();
    /// assert!(!cache.has_path_to(0, 0));
    /// ```
    #[inline]
    pub fn has_path_to(&self, index: usize, level: usize) -> bool {
        self.valid
            && level < self.ranges.len()
            && self.ranges[level].start <= index
            && index < self.ranges[level].end
    }

    /// Get the cached path index for a specific level.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::cache::IndexCache;
    ///
    /// let mut cache = IndexCache::new();
    /// cache.invalidate();
    /// assert!(cache.get_path_index(0).is_none());
    /// ```
    #[inline]
    pub fn get_path_index(&self, level: usize) -> Option<usize> {
        if self.valid && level < self.path.len() {
            Some(self.path[level])
        } else {
            None
        }
    }

    /// Update the cache with a new path to an index.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::cache::IndexCache;
    ///
    /// let mut cache = IndexCache::new();
    /// cache.invalidate();
    /// cache.update(0, vec![0], vec![0..1]);
    /// assert!(cache.valid);
    /// ```
    #[inline]
    pub fn update(&mut self, index: usize, path: Vec<usize>, ranges: Vec<Range<usize>>) {
        self.index = index;
        self.path = path;
        self.ranges = ranges;
        self.valid = true;
    }

    /// Add a level to the cached path.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::cache::IndexCache;
    ///
    /// let mut cache = IndexCache::new();
    /// // Must update the cache first to make it valid
    /// cache.update(0, vec![], vec![]);
    /// cache.push_level(0, 0..1);
    /// assert!(cache.valid);
    /// ```
    #[inline]
    pub fn push_level(&mut self, index: usize, range: Range<usize>) {
        if self.valid && self.path.len() < MAX_CACHE_LEVELS {
            self.path.push(index);
            self.ranges.push(range);
        }
    }

    /// Check if an index is near the cached index.
    ///
    /// "Near" is defined as being within the same leaf node at the lowest
    /// level of the cache.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::cache::IndexCache;
    ///
    /// let mut cache = IndexCache::new();
    /// cache.invalidate();
    /// cache.update(0, vec![0], vec![0..1]);
    /// assert!(cache.is_near(0));
    /// assert!(!cache.is_near(1));
    /// ```
    #[inline]
    pub fn is_near(&self, index: usize) -> bool {
        self.valid
            && !self.ranges.is_empty()
            && self.ranges.last().unwrap().start <= index
            && index < self.ranges.last().unwrap().end
    }

    /// Get all the path indices and their corresponding ranges.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::cache::IndexCache;
    ///
    /// let mut cache = IndexCache::new();
    /// cache.invalidate();
    /// cache.update(0, vec![0], vec![0..1]);
    /// assert_eq!(cache.get_path().collect::<Vec<_>>(), vec![(0, &(0..1))]);
    /// ```
    #[inline]
    pub fn get_path(&self) -> impl Iterator<Item = (usize, &Range<usize>)> {
        self.path.iter().copied().zip(self.ranges.iter())
    }
}

impl Default for IndexCache {
    fn default() -> Self {
        Self::new()
    }
}
