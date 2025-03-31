//! Index Caching Module
//!
//! This module provides caching functionality for improved performance when 
//! accessing vector elements. It keeps track of the path taken to reach
//! a specific index, allowing for faster access to nearby indices.

use std::ops::Range;

/// Maximum number of levels in the tree structure to cache
pub const MAX_CACHE_LEVELS: usize = 10;

/// A cache for optimizing repeated index operations in the vector.
///
/// This cache remembers the path to the most recently accessed index,
/// which can significantly speed up access to nearby indices.
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
    pub fn new() -> Self {
        Self {
            index: 0,
            path: Vec::with_capacity(MAX_CACHE_LEVELS),
            ranges: Vec::with_capacity(MAX_CACHE_LEVELS),
            valid: false,
        }
    }
    
    /// Clear the cache, marking it as invalid.
    pub fn invalidate(&mut self) {
        self.valid = false;
    }
    
    /// Check if the cache contains information for the given index.
    pub fn has_index(&self, index: usize) -> bool {
        self.valid && self.index == index
    }
    
    /// Check if the cache contains path information for a level containing the given index.
    pub fn has_path_to(&self, index: usize, level: usize) -> bool {
        self.valid && 
        level < self.ranges.len() && 
        self.ranges[level].start <= index && 
        index < self.ranges[level].end
    }
    
    /// Get the cached path index for a specific level.
    pub fn get_path_index(&self, level: usize) -> Option<usize> {
        if self.valid && level < self.path.len() {
            Some(self.path[level])
        } else {
            None
        }
    }
    
    /// Update the cache with a new path to an index.
    pub fn update(&mut self, index: usize, path: Vec<usize>, ranges: Vec<Range<usize>>) {
        self.index = index;
        self.path = path;
        self.ranges = ranges;
        self.valid = true;
    }
    
    /// Add a level to the cached path.
    pub fn push_level(&mut self, index: usize, range: Range<usize>) {
        if self.path.len() < MAX_CACHE_LEVELS {
            self.path.push(index);
            self.ranges.push(range);
        }
    }
    
    /// Check if an index is near the cached index.
    ///
    /// "Near" is defined as being within the same leaf node at the lowest
    /// level of the cache.
    pub fn is_near(&self, index: usize) -> bool {
        self.valid && 
        !self.ranges.is_empty() && 
        self.ranges.last().unwrap().start <= index && 
        index < self.ranges.last().unwrap().end
    }
    
    /// Get all the path indices and their corresponding ranges.
    pub fn get_path(&self) -> impl Iterator<Item = (usize, &Range<usize>)> {
        self.path.iter().copied().zip(self.ranges.iter())
    }
}

impl Default for IndexCache {
    fn default() -> Self {
        Self::new()
    }
}