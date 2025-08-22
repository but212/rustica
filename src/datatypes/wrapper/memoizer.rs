//! # Memoizer
//!
//! Thread-safe memoization utility for pure functions.
//!
//! Provides a unified, ergonomic API for caching expensive computations with automatic concurrency support.
//! The `Memoizer` implements thread-safe memoization using a reader-writer lock pattern to optimize
//! for concurrent reads while ensuring exclusive access during writes.
//!
//! ## Key Features
//!
//! - Thread-safe caching with optimized read concurrency
//! - Protection against redundant calculations (race condition handling)
//! - Automatic computation of missing values
//! - Support for any hashable key and cloneable value types
//! - Cache management via explicit clearing
//!
//! ## Functional Programming Context
//!
//! The `Memoizer` aligns with functional programming principles by:
//!
//! - Promoting pure functions (same inputs always yield same outputs)
//! - Preserving referential transparency (cached results are equivalent to direct computation)
//! - Supporting idempotent operations (repeated calls with same input return identical results)
//! - Enabling transparent performance optimization without changing semantics
//!
//! ## Type Class Laws
//!
//! While `Memoizer` doesn't directly implement algebraic type classes like `Functor` or `Monad`,
//! it follows these important laws:
//!
//! - **Idempotence Law**: `memo.get_or_compute(k, f) == memo.get_or_compute(k, f)` for all `k` and `f`
//!   - Multiple calls with the same key and function will always yield the same result.
//!
//! - **Transparency Law**: `memo.get_or_compute(k, f) == f(k)` for the first call with key `k`
//!   - The first computation is equivalent to directly applying the function to the key.
//!
//! - **Consistency Law**: Once computed, a value for key `k` remains the same until `clear()` is called
//!   - The cached value is stable across multiple accesses until explicitly cleared.
//!
//! - **Commutativity Law**: For any two distinct keys `j` and `k`, the order of evaluation does not matter
//!   - `memo.get_or_compute(j, f); memo.get_or_compute(k, g)` is equivalent to
//!     `memo.get_or_compute(k, g); memo.get_or_compute(j, f)`
//!
//! ## Performance Characteristics
//!
//! - **Time Complexity**:
//!   - Creation: O(1) - Constant time initialization
//!   - Cache Hit: O(1) average case for hash lookup
//!   - Cache Miss: O(f) where f is the complexity of the compute function
//! - **Space Complexity**: O(n) where n is the number of cached key-value pairs
//! - **Concurrency**:
//!   - Multiple readers can access the cache simultaneously
//!   - Writers get exclusive access, blocking all other operations
//!   - Double-checked locking pattern prevents redundant computations
//! - **Cache Lookups**: O(1) average case for hash lookups (amortized)
//! - **Get or Compute**: O(f) where f is the complexity of the computation function
//!
//! ## Type Class Implementations
//!
//! `Memoizer<K, V>` implements:
//!
//! - `Default`: Creates an empty memoizer via `Memoizer::new()`
//!
//! ## Quick Start
//!
//! ```rust
//! use rustica::datatypes::wrapper::memoizer::Memoizer;
//!
//! // Create a memoizer for caching expensive computations
//! let memo = Memoizer::new();
//!
//! // Define an expensive function (factorial)
//! fn factorial(n: &u32) -> u64 {
//!     match *n {
//!         0 | 1 => 1,
//!         _ => (*n as u64) * factorial(&(n - 1)),
//!     }
//! }
//!
//! // First call computes and caches result
//! let result1 = memo.get_or_compute(5, factorial);
//! assert_eq!(result1, 120);
//!
//! // Second call returns cached result instantly
//! let result2 = memo.get_or_compute(5, factorial);
//! assert_eq!(result2, 120); // Same result, no recomputation
//!
//! // Different inputs are computed and cached separately
//! let result3 = memo.get_or_compute(4, factorial);
//! assert_eq!(result3, 24);
//! ```
//!
//! ## Documentation Notes
//!
//! For detailed practical examples demonstrating the type class laws, usage patterns, and
//! performance characteristics, please refer to the function-level documentation of the
//! relevant methods such as `new`, `get_or_compute`, and `clear`.

use std::collections::HashMap;
use std::hash::Hash;
use std::sync::RwLock;

/// Thread-safe memoizer for pure functions.
///
/// The `Memoizer` provides an efficient, thread-safe caching mechanism for pure functions.
/// It stores computed values in a cache protected by a read-write lock (`RwLock`),
/// optimizing for concurrent read access while ensuring thread safety.
///
/// This data structure is particularly useful for:
/// - Caching expensive computations
/// - Preventing redundant calculations in multi-threaded environments
/// - Implementing pure functional memoization patterns
///
/// # Type Parameters
///
/// * `K`: The key type, must implement `Eq`, `Hash`, and `Clone`
/// * `V`: The value type, must implement `Clone`
///
/// # Thread Safety
///
/// The memoizer is fully thread-safe with the following guarantees:
/// - Multiple threads can read from the cache concurrently
/// - Write operations (cache misses) obtain an exclusive lock
/// - Double-checked locking pattern prevents redundant computations for the same key
/// - Cache coherence ensures all threads see the most recent values
///
/// # Performance Characteristics
///
/// - **Space Complexity**: O(n) where n is the number of cached key-value pairs
/// - **Time Complexity**:
///   - Cache Hit: O(1) average case (hash lookup) + small locking overhead
///   - Cache Miss: O(f) where f is the computation cost + locking overhead
/// - **Concurrency**:
///   - Multiple concurrent readers cause minimal contention
///   - Writers block each other and all readers
///   - Reader-biased for optimal performance with high hit rates
/// - **Memory Usage**:
///   - HashMap backing store with standard Rust hasher
///   - Each entry stores both K and V (cloned)
///   - Additional small overhead for the RwLock synchronization primitive
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
    /// Initializes an empty memoizer with a fresh HashMap and RwLock. The memoizer starts with
    /// zero memory footprint for cached values, and will only allocate memory as values are added.
    ///
    /// # Performance
    ///
    /// - **Time Complexity**: O(1) - Constant time initialization
    /// - **Space Complexity**: O(1) - Minimal allocation for the empty HashMap and RwLock structures
    /// - **Thread Safety**: Creates a fresh RwLock with no contention
    /// - **Memory Usage**: Initial capacity is HashMap default (small, typically a few buckets)
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::wrapper::memoizer::Memoizer;
    ///
    /// // Create a memoizer for string keys and integer values
    /// let memo: Memoizer<String, i32> = Memoizer::new();
    /// ```
    pub fn new() -> Self {
        Memoizer {
            cache: RwLock::new(HashMap::new()),
        }
    }

    /// Returns the cached value for `key`, or computes and stores it using `f`.
    ///
    /// This is the core method of the `Memoizer`. It first checks if a value for the given key
    /// is already cached. If present, it returns the cached value. Otherwise, it computes the value
    /// using the provided function `f`, stores it in the cache for future use, and then returns it.
    ///
    /// The method is thread-safe and uses a double-checked locking pattern to ensure that even if multiple
    /// threads request the same uncached key simultaneously, the computation will only happen once.
    ///
    /// # Arguments
    ///
    /// * `key` - The key to look up or compute a value for
    /// * `f` - Function to compute the value if not already in the cache
    ///
    /// # Returns
    ///
    /// The cached or newly computed value (cloned)
    ///
    /// # Performance
    ///
    /// - **Time Complexity**:
    ///   - Cache Hit: O(1) average case for hash lookup + small lock acquisition overhead
    ///   - Cache Miss: O(f) where f is the complexity of the compute function
    /// - **Space Complexity**: O(1) additional space per cache entry (key and value)
    /// - **Thread Safety**:
    ///   - Uses read lock for lookups (multiple readers allowed)
    ///   - Uses write lock for insertion (exclusive access)
    ///   - Implements double-checked locking to prevent duplicate computations
    /// - **Memory Consideration**:
    ///   - Both key and value are cloned and stored
    ///   - Return value is also cloned from cache
    ///
    /// # Examples
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
    /// This method removes all entries from the cache, freeing the associated memory.
    /// After calling this method, any subsequent calls to `get_or_compute` will need to
    /// recompute values for all keys, as if the memoizer was newly created.
    ///
    /// This is useful for scenarios where:
    /// - The cache has grown too large and memory needs to be reclaimed
    /// - The underlying data has changed, invalidating all cached results
    /// - A different computation strategy is needed for all keys
    ///
    /// # Performance
    ///
    /// - **Time Complexity**: O(n) where n is the number of cached entries
    /// - **Space Complexity**: O(1) - no additional memory allocation, memory is reclaimed
    /// - **Thread Safety**: Acquires an exclusive write lock, blocking all other operations
    /// - **Memory Impact**: Releases all memory used by cached keys and values
    ///
    /// # Examples
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
    pub fn clear(&self) {
        let mut cache = self.cache.write().unwrap();
        cache.clear();
    }
}
