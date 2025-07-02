//! Thread-safe memoization utility for pure functions.
//!
//! Provides a unified, ergonomic API for caching expensive computations with automatic concurrency support.
//! The `Memoizer` implements thread-safe memoization using a reader-writer lock pattern to optimize
//! for concurrent reads while ensuring exclusive access during writes.
//!
//! # Key Features
//!
//! - Thread-safe caching with optimized read concurrency
//! - Protection against redundant calculations (race condition handling)
//! - Automatic computation of missing values
//! - Support for any hashable key and cloneable value types
//! - Cache management via explicit clearing
//!
//! # Example (Single-threaded)
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
//! # Example (Multi-threaded)
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
//! # Advanced Example (Complex Types)
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
//! # Performance Characteristics
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
//! # Thread Safety Guarantees
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
    /// Basic creation with simple types:
    ///
    /// ```rust
    /// use rustica::datatypes::wrapper::memoizer::Memoizer;
    ///
    /// // Create a memoizer for string keys and integer values
    /// let memo: Memoizer<String, i32> = Memoizer::new();
    /// ```
    ///
    /// Creating with complex types:
    ///
    /// ```rust
    /// use rustica::datatypes::wrapper::memoizer::Memoizer;
    /// use std::collections::HashMap;
    ///
    /// // A memoizer that can cache expensive computations resulting in collections
    /// let memo: Memoizer<String, Vec<i32>> = Memoizer::new();
    ///
    /// // A memoizer for complex key/value pairs
    /// let complex_memo: Memoizer<(String, i32), HashMap<String, f64>> = Memoizer::new();
    /// ```
    ///
    /// Creating in a multi-threaded context:
    ///
    /// ```rust
    /// use rustica::datatypes::wrapper::memoizer::Memoizer;
    /// use std::sync::Arc;
    ///
    /// // Create a thread-safe memoizer reference
    /// let memo: Arc<Memoizer<u64, String>> = Arc::new(Memoizer::new());
    ///
    /// // Now it can be safely cloned and shared across threads
    /// let memo_clone = memo.clone();
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
    /// Basic usage with simple types:
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
    /// Memoizing expensive computations:
    ///
    /// ```rust
    /// use rustica::datatypes::wrapper::memoizer::Memoizer;
    /// use std::time::{Duration, Instant};
    ///
    /// let memo = Memoizer::new();
    ///
    /// // Define an expensive function (fibonacci)
    /// fn fibonacci(n: &u32) -> u64 {
    ///     match n {
    ///         0 => 0,
    ///         1 => 1,
    ///         n => fibonacci(&(n-1)) + fibonacci(&(n-2))
    ///     }
    /// }
    ///
    /// // First call is expensive
    /// let result1 = memo.get_or_compute(20, fibonacci);
    ///
    /// // Second call is fast (uses cache)
    /// let result2 = memo.get_or_compute(20, fibonacci);
    ///
    /// assert_eq!(result1, result2);
    /// assert_eq!(result1, 6765);
    /// ```
    ///
    /// Handling concurrent access (race condition prevention):
    ///
    /// ```rust
    /// use rustica::datatypes::wrapper::memoizer::Memoizer;
    /// use std::sync::{Arc, atomic::{AtomicUsize, Ordering}};
    /// use std::thread;
    ///
    /// // Create a memoizer and a counter to track function calls
    /// let memo = Arc::new(Memoizer::new());
    /// let compute_count = Arc::new(AtomicUsize::new(0));
    ///
    /// // Spawn multiple threads that all compute the same key
    /// let handles: Vec<_> = (0..5).map(|_| {
    ///     let memo = memo.clone();
    ///     let counter = compute_count.clone();
    ///     
    ///     thread::spawn(move || {
    ///         memo.get_or_compute("key", |_| {
    ///             // Increment counter and simulate work
    ///             counter.fetch_add(1, Ordering::SeqCst);
    ///             thread::sleep(std::time::Duration::from_millis(10));
    ///             "computed value".to_string()
    ///         })
    ///     })
    /// }).collect();
    ///
    /// // Join all threads
    /// for handle in handles {
    ///     let _ = handle.join();
    /// }
    ///
    /// // The function should only have been computed once, despite 5 threads
    /// assert_eq!(compute_count.load(Ordering::SeqCst), 1);
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
    /// Basic usage:
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
    /// Clearing after environment changes:
    ///
    /// ```rust
    /// use rustica::datatypes::wrapper::memoizer::Memoizer;
    /// use std::cell::Cell;
    ///
    /// // Set up a memoizer and an external state that affects computation
    /// let memo = Memoizer::new();
    /// let multiplier = Cell::new(10);
    ///
    /// // First computation with multiplier = 10
    /// let value1 = memo.get_or_compute(5, |n| n * multiplier.get());
    /// assert_eq!(value1, 50);
    ///
    /// // Change the external state
    /// multiplier.set(20);
    ///
    /// // Without clearing, we would still get the old cached value
    /// let cached = memo.get_or_compute(5, |n| n * multiplier.get());
    /// assert_eq!(cached, 50); // Still returns 50, not 100!
    ///
    /// // Clear the cache to force recomputation with new multiplier
    /// memo.clear();
    /// let new_value = memo.get_or_compute(5, |n| n * multiplier.get());
    /// assert_eq!(new_value, 100); // Now returns updated value
    /// ```
    ///
    /// In a multi-threaded context:
    ///
    /// ```rust
    /// use rustica::datatypes::wrapper::memoizer::Memoizer;
    /// use std::sync::Arc;
    /// use std::thread;
    ///
    /// let memo = Arc::new(Memoizer::new());
    ///
    /// // Populate with some values from multiple threads
    /// let handles: Vec<_> = (0..5).map(|i| {
    ///     let memo = memo.clone();
    ///     thread::spawn(move || {
    ///         memo.get_or_compute(i, |x| x * 10);
    ///     })
    /// }).collect();
    ///
    /// for h in handles {
    ///     h.join().unwrap();
    /// }
    ///
    /// // Now clear from main thread
    /// memo.clear();
    ///
    /// // And verify values need recomputation
    /// for i in 0..5 {
    ///     let recomputed = memo.get_or_compute(i, |x| x * 20);
    ///     assert_eq!(recomputed, i * 20); // New computation used
    /// }
    /// ```
    pub fn clear(&self) {
        let mut cache = self.cache.write().unwrap();
        cache.clear();
    }
}
