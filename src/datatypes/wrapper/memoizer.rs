//! Thread-safe memoization utility for pure functions.
//!
//! Provides a unified, ergonomic API for caching expensive computations with automatic concurrency support.
//!
//! # Example (Single-threaded)
//!
//! ```rust
//! use rustica::datatypes::wrapper::memoizer::Memoizer;
//! use std::sync::Arc;
//!
//! let memo: Arc<Memoizer<u32, u32>> = Arc::new(Memoizer::new());
//! let result = memo.get_or_compute(10, |x| x * x);
//! assert_eq!(result, 100);
//! // Cached value is reused
//! let again = memo.get_or_compute(10, |x| unreachable!());
//! assert_eq!(again, 100);
//! ```
//!
//! # Example (Multi-threaded)
//!
//! ```rust
//! use rustica::datatypes::wrapper::memoizer::Memoizer;
//! use std::sync::Arc;
//! use std::thread;
//!
//! let memo: Arc<Memoizer<u32, u32>> = Arc::new(Memoizer::new());
//! let handles: Vec<_> = (0..4).map(|i| {
//!     let memo = memo.clone();
//!     thread::spawn(move || {
//!         memo.get_or_compute(i % 2, |x| x * 10)
//!     })
//! }).collect();
//! let results: Vec<_> = handles.into_iter().map(|h| h.join().unwrap()).collect();
//! assert!(results.contains(&0));
//! assert!(results.contains(&10));
//! ```
//!
//! # Performance Characteristics
//!
//! - Memory Usage: O(n) where n is the number of cached key-value pairs
//! - Thread Safety: Uses `RwLock` for concurrent read access with exclusive write locking
//! - Cache Lookups: O(1) average case for hash lookups (amortized)
//! - Get or Compute: O(f) where f is the complexity of the computation function

use std::collections::HashMap;
use std::hash::Hash;
use std::sync::RwLock;

/// Thread-safe memoizer for pure functions.
///
/// Stores computed values in a cache protected by a read-write lock.
/// Values are cloned on retrieval.
///
/// # Performance Characteristics
///
/// - Space complexity: O(n) where n is the number of cached key-value pairs
/// - Time complexity: O(1) for cache hits, O(f) for cache misses where f is the computation cost
pub struct Memoizer<K, V> {
    cache: RwLock<HashMap<K, V>>,
}

impl<K, V> Default for Memoizer<K, V>
where
    K: Eq + Hash + Clone,
    V: Clone,
{
    fn default() -> Self {
        Self::new()
    }
}

impl<K, V> Memoizer<K, V>
where
    K: Eq + Hash + Clone,
    V: Clone,
{
    /// Creates a new, empty memoizer.
    ///
    /// # Example
    ///
    /// ```rust
    /// use rustica::datatypes::wrapper::memoizer::Memoizer;
    ///
    /// let memo: Memoizer<String, Vec<i32>> = Memoizer::new();
    /// ```
    ///
    /// # Performance
    ///
    /// - Time complexity: O(1)
    /// - Space complexity: O(1) - initial empty HashMap allocation
    pub fn new() -> Self {
        Memoizer {
            cache: RwLock::new(HashMap::new()),
        }
    }

    /// Returns the cached value for `key`, or computes and stores it using `f`.
    ///
    /// # Arguments
    /// * `key` - The key to look up or compute.
    /// * `f` - Function to compute the value if not cached.
    ///
    /// # Returns
    /// The cached or newly computed value (cloned).
    ///
    /// # Example
    ///
    /// ```rust
    /// use rustica::datatypes::wrapper::memoizer::Memoizer;
    ///
    /// let memo = Memoizer::new();
    ///
    /// // First call computes the value
    /// let value1 = memo.get_or_compute("hello", |s| s.len());
    /// assert_eq!(value1, 5);
    ///
    /// // Second call returns cached value
    /// let value2 = memo.get_or_compute("hello", |_| panic!("Should not be called"));
    /// assert_eq!(value2, 5);
    /// ```
    ///
    /// # Performance
    ///
    /// - Time complexity: O(1) for cache hits, O(f) for cache misses where f is the computation cost
    /// - Space complexity: O(1) additional space per cache entry
    pub fn get_or_compute<F>(&self, key: K, f: F) -> V
    where
        F: FnOnce(&K) -> V,
    {
        // Try to read from cache first
        {
            let cache = self.cache.read().unwrap();
            if let Some(v) = cache.get(&key) {
                return v.clone();
            }
        }
        // Not found, compute and insert
        let mut cache = self.cache.write().unwrap();
        // Double-check in case another thread inserted
        if let Some(v) = cache.get(&key) {
            return v.clone();
        }
        let value = f(&key);
        cache.insert(key.clone(), value.clone());
        value
    }

    /// Clears all cached values.
    ///
    /// # Example
    ///
    /// ```rust
    /// use rustica::datatypes::wrapper::memoizer::Memoizer;
    ///
    /// let memo = Memoizer::new();
    ///
    /// // Cache a value
    /// memo.get_or_compute(42, |n| n * 2);
    ///
    /// // Clear the cache
    /// memo.clear();
    ///
    /// // Value will be recomputed
    /// let value = memo.get_or_compute(42, |n| n * 3);
    /// assert_eq!(value, 126);
    /// ```
    ///
    /// # Performance
    ///
    /// - Time complexity: O(n) where n is the number of cached entries
    /// - Space complexity: O(1) - no additional allocation
    pub fn clear(&self) {
        let mut cache = self.cache.write().unwrap();
        cache.clear();
    }
}
