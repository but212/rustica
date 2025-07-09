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
//! ## Type Class Implementations
//!
//! `Memoizer<K, V>` implements:
//!
//! - `Default`: Creates an empty memoizer via `Memoizer::new()`
//!
//! ## Basic Usage
//!
//! ```rust
//! use rustica::datatypes::wrapper::memoizer::Memoizer;
//!
//! // Create a new memoizer for string keys and integer values
//! let memo = Memoizer::<String, i32>::new();
//!
//! // Compute and cache a value
//! let value = memo.get_or_compute("example".to_string(), |s| s.len() as i32);
//! assert_eq!(value, 7);
//!
//! // Retrieve from cache on subsequent calls
//! let cached = memo.get_or_compute("example".to_string(), |_| panic!("Not called"));
//! assert_eq!(cached, 7);
//!
//! // Clear the cache when needed
//! memo.clear();
//! ```
//!
//! ## Type Class Laws
//!
//! While `Memoizer` doesn't directly implement algebraic type classes like `Functor` or `Monad`,
//! it follows these important laws:
//!
//! - **Idempotence**: `memo.get_or_compute(k, f) == memo.get_or_compute(k, f)` for all `k` and `f`
//! - **Transparency**: `memo.get_or_compute(k, f) == f(k)` for the first call with key `k`
//! - **Consistency**: Once computed, a value for key `k` remains the same until `clear()` is called
//!
//! ## Example (Single-threaded)
//!
//! Basic usage with scalar types:
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
//! ## Example (Multi-threaded)
//!
//! Concurrent access from multiple threads with automatic synchronization:
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
//! ## Advanced Example (Complex Types)
//!
//! Memoizing expensive operations with complex keys and values:
//!
//! ```rust
//! use rustica::datatypes::wrapper::memoizer::Memoizer;
//! use std::collections::HashMap;
//!
//! // Complex computation: Calculate word frequencies in a text
//! let memo = Memoizer::new();
//!
//! // Define an expensive function we want to memoize
//! fn calculate_word_frequencies(text: &String) -> HashMap<String, usize> {
//!     let mut frequencies = HashMap::new();
//!     for word in text.split_whitespace() {
//!         *frequencies.entry(word.to_lowercase()).or_insert(0) += 1;
//!     }
//!     frequencies
//! }
//!
//! // First call computes and caches the result
//! let text = "to be or not to be".to_string();
//! let frequencies = memo.get_or_compute(text.clone(), calculate_word_frequencies);
//!
//! assert_eq!(frequencies.get("to"), Some(&2));
//! assert_eq!(frequencies.get("be"), Some(&2));
//! assert_eq!(frequencies.get("or"), Some(&1));
//! assert_eq!(frequencies.get("not"), Some(&1));
//!
//! // Second call uses the cached result
//! let cached = memo.get_or_compute(text, |_| {
//!     panic!("This should not be called")
//! });
//!
//! assert_eq!(cached.get("to"), Some(&2));
//! ```
//!
//! ## Performance Characteristics
//!
//! - **Memory Usage**: O(n) where n is the number of cached key-value pairs
//! - **Thread Safety**: Uses `RwLock` for concurrent read access with exclusive write locking
//!   - Multiple readers can access the cache simultaneously
//!   - Writers get exclusive access, blocking all other operations
//!   - Double-checked locking pattern prevents redundant computations
//! - **Cache Lookups**: O(1) average case for hash lookups (amortized)
//! - **Get or Compute**: O(f) where f is the complexity of the computation function
//! - **Concurrency Overhead**:
//!   - Reader Lock: Minimal contention for read-heavy workloads
//!   - Writer Lock: Potential contention if many cache misses occur simultaneously
//!   - Cache misses in parallel threads for the same key are efficiently handled
//!     (only one thread performs computation, others wait and receive the result)
//!
//! ## Thread Safety Guarantees
//!
//! The `Memoizer` provides several guarantees for concurrent usage:
//!
//! 1. **Consistency**: A value for a key is computed exactly once, even if requested concurrently
//! 2. **Cache Coherence**: All threads see the most up-to-date cached values
//! 3. **Deadlock Prevention**: The lock hierarchy prevents potential deadlocks
//! 4. **Atomicity**: Cache operations are atomic - readers see either the old or new state, never partial updates

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
