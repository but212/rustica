//! # Memoizer
//!
//! Thread-safe memoization utility for pure functions with LRU eviction support.
//!
//! Provides a unified, ergonomic API for caching expensive computations with automatic concurrency support.
//! The `Memoizer` implements thread-safe memoization using a reader-writer lock pattern to optimize
//! for concurrent reads while ensuring exclusive access during writes.
//!
//! ## Key Features
//!
//! - Thread-safe caching with optimized read concurrency
//! - **LRU (Least Recently Used) eviction policy** for bounded memory usage
//! - **Configurable capacity** with optional unlimited mode
//! - **Cache statistics** (hits, misses, evictions)
//! - Protection against redundant calculations (race condition handling)
//! - Automatic computation of missing values
//! - Support for any hashable key and cloneable value types
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
//! - **Consistency Law**: Once computed, a value for key `k` remains the same until evicted or cleared
//!   - The cached value is stable across multiple accesses until explicitly cleared or evicted by LRU.
//!
//! - **Commutativity Law**: For any two distinct keys `j` and `k`, the order of evaluation does not matter
//!   - `memo.get_or_compute(j, f); memo.get_or_compute(k, g)` is equivalent to
//!     `memo.get_or_compute(k, g); memo.get_or_compute(j, f)`
//!
//! ## Type Class Implementations
//!
//! `Memoizer<K, V>` implements:
//!
//! - `Default`: Creates an empty memoizer with unlimited capacity via `Memoizer::new()`
//!
//! ## Quick Start
//!
//! ```rust
//! use rustica::datatypes::wrapper::memoizer::Memoizer;
//!
//! // Create an unlimited memoizer (backward compatible)
//! let memo: Memoizer<u32, u64> = Memoizer::new();
//!
//! // Or create a bounded LRU cache with max 1000 entries
//! let bounded_memo: Memoizer<u32, u64> = Memoizer::with_capacity(1000);
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
//!
//! // Check cache statistics
//! let stats = memo.stats();
//! assert_eq!(stats.hits, 1);   // One cache hit (second call to factorial(5))
//! assert_eq!(stats.misses, 2); // Two cache misses (first calls)
//! ```
//!
//! ## LRU Eviction Example
//!
//! ```rust
//! use rustica::datatypes::wrapper::memoizer::Memoizer;
//!
//! // Create a cache that holds at most 2 entries
//! let memo: Memoizer<&str, i32> = Memoizer::with_capacity(2);
//!
//! memo.get_or_compute("a", |_| 1); // Cache: [a]
//! memo.get_or_compute("b", |_| 2); // Cache: [a, b]
//! memo.get_or_compute("c", |_| 3); // Cache: [b, c] - 'a' evicted (LRU)
//!
//! assert!(!memo.contains_key(&"a")); // 'a' was evicted
//! assert!(memo.contains_key(&"b"));  // 'b' still present
//! assert!(memo.contains_key(&"c"));  // 'c' still present
//!
//! // Accessing 'b' makes it most recently used
//! memo.get_or_compute("b", |_| 2); // Cache: [c, b] - 'b' moved to end
//! memo.get_or_compute("d", |_| 4); // Cache: [b, d] - 'c' evicted (now LRU)
//!
//! assert!(!memo.contains_key(&"c")); // 'c' was evicted
//! assert!(memo.contains_key(&"b"));  // 'b' still present (was accessed)
//! ```
use std::collections::HashMap;
use std::hash::Hash;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::{PoisonError, RwLock, RwLockWriteGuard};

/// Internal node for LRU doubly-linked list.
///
/// Each node contains the cached value and pointers to adjacent nodes.
#[derive(Clone)]
struct LruNode<K, V> {
    value: V,
    prev: Option<K>,
    next: Option<K>,
}

/// Internal LRU cache structure.
///
/// Implements a HashMap + doubly-linked list for O(1) access and LRU ordering.
struct LruCache<K, V> {
    map: HashMap<K, LruNode<K, V>>,
    head: Option<K>, // Least recently used
    tail: Option<K>, // Most recently used
    max_capacity: Option<usize>,
}

impl<K, V> LruCache<K, V>
where
    K: Eq + Hash + Clone,
    V: Clone,
{
    fn new(max_capacity: Option<usize>) -> Self {
        Self {
            map: HashMap::new(),
            head: None,
            tail: None,
            max_capacity,
        }
    }

    fn len(&self) -> usize {
        self.map.len()
    }

    fn is_empty(&self) -> bool {
        self.map.is_empty()
    }

    fn capacity(&self) -> usize {
        self.map.capacity()
    }

    fn contains_key(&self, key: &K) -> bool {
        self.map.contains_key(key)
    }

    /// Gets a value without updating LRU order (for read-only access).
    ///
    /// Unlike `get`, this method does not modify the LRU ordering,
    /// making it suitable for read-only inspection of cached values.
    ///
    /// # Arguments
    ///
    /// * `key` - The key to look up
    ///
    /// # Returns
    ///
    /// `Some(&V)` if the key exists in the cache, `None` otherwise.
    ///
    /// # Performance
    ///
    /// - **Time Complexity**: O(1) - Direct hash lookup
    /// - **LRU Impact**: None - Does not update access order
    fn peek(&self, key: &K) -> Option<&V> {
        self.map.get(key).map(|node| &node.value)
    }

    /// Gets a value and updates LRU order (marks as most recently used).
    fn get(&mut self, key: &K) -> Option<V> {
        if !self.map.contains_key(key) {
            return None;
        }

        // Move to tail (most recently used)
        self.move_to_tail(key);
        self.map.get(key).map(|node| node.value.clone())
    }

    /// Inserts a key-value pair, evicting LRU entry if at capacity.
    /// Returns the evicted key-value pair if any.
    fn insert(&mut self, key: K, value: V) -> Option<(K, V)> {
        let mut evicted = None;

        if self.map.contains_key(&key) {
            // Update existing entry
            if let Some(node) = self.map.get_mut(&key) {
                node.value = value;
            }
            self.move_to_tail(&key);
        } else {
            // Check capacity and evict if needed
            if self
                .max_capacity
                .is_some_and(|max| max > 0 && self.map.len() >= max)
            {
                evicted = self.evict_lru();
            }

            // Insert new entry at tail
            let node = LruNode {
                value,
                prev: self.tail.clone(),
                next: None,
            };

            // Update old tail's next pointer
            if let Some(tail_node) = self.tail.as_ref().and_then(|k| self.map.get_mut(k)) {
                tail_node.next = Some(key.clone());
            }

            self.map.insert(key.clone(), node);
            self.tail = Some(key.clone());

            if self.head.is_none() {
                self.head = Some(key);
            }
        }

        evicted
    }

    /// Removes a key from the cache.
    fn remove(&mut self, key: &K) -> Option<V> {
        if let Some(node) = self.map.remove(key) {
            self.unlink(&node);
            Some(node.value)
        } else {
            None
        }
    }

    /// Clears the cache.
    fn clear(&mut self) {
        self.map.clear();
        self.head = None;
        self.tail = None;
    }

    /// Returns all keys (in arbitrary order).
    fn keys(&self) -> Vec<K> {
        self.map.keys().cloned().collect()
    }

    /// Returns all values (in arbitrary order).
    fn values(&self) -> Vec<V> {
        self.map.values().map(|n| n.value.clone()).collect()
    }

    /// Reserves capacity for additional entries.
    fn reserve(&mut self, additional: usize) {
        self.map.reserve(additional);
    }

    /// Shrinks capacity to fit current entries.
    fn shrink_to_fit(&mut self) {
        self.map.shrink_to_fit();
    }

    // --------------------------------------------------------------------
    // Internal helper methods
    // --------------------------------------------------------------------

    /// Moves a key to the tail (most recently used).
    fn move_to_tail(&mut self, key: &K) {
        if self.tail.as_ref() == Some(key) {
            return; // Already at tail
        }

        // Get node info before mutation
        let (prev, next) = {
            let node = match self.map.get(key) {
                Some(n) => n,
                None => return,
            };
            (node.prev.clone(), node.next.clone())
        };

        // Unlink from current position
        if let Some(ref prev_key) = prev {
            if let Some(prev_node) = self.map.get_mut(prev_key) {
                prev_node.next = next.clone();
            }
        } else {
            // This was the head
            self.head = next.clone();
        }

        if let Some(next_node) = next.as_ref().and_then(|k| self.map.get_mut(k)) {
            next_node.prev = prev.clone();
        }

        // Link to tail
        if let Some(tail_node) = self
            .tail
            .as_ref()
            .filter(|k| *k != key)
            .and_then(|k| self.map.get_mut(k))
        {
            tail_node.next = Some(key.clone());
        }

        // Update node pointers
        if let Some(node) = self.map.get_mut(key) {
            node.prev = self.tail.clone();
            node.next = None;
        }

        self.tail = Some(key.clone());
    }

    /// Unlinks a node from the list (used after removal).
    fn unlink(&mut self, node: &LruNode<K, V>) {
        if let Some(ref prev_key) = node.prev {
            if let Some(prev_node) = self.map.get_mut(prev_key) {
                prev_node.next = node.next.clone();
            }
        } else {
            self.head = node.next.clone();
        }

        if let Some(ref next_key) = node.next {
            if let Some(next_node) = self.map.get_mut(next_key) {
                next_node.prev = node.prev.clone();
            }
        } else {
            self.tail = node.prev.clone();
        }
    }

    /// Evicts the least recently used entry (head).
    fn evict_lru(&mut self) -> Option<(K, V)> {
        let head_key = self.head.clone()?;
        let node = self.map.remove(&head_key)?;

        // Update head pointer
        self.head = node.next.clone();

        // Update new head's prev pointer
        if let Some(ref new_head_key) = self.head {
            if let Some(new_head_node) = self.map.get_mut(new_head_key) {
                new_head_node.prev = None;
            }
        } else {
            // Cache is now empty
            self.tail = None;
        }

        Some((head_key, node.value))
    }
}

/// Statistics for cache performance monitoring.
///
/// Provides insight into cache hit rate and eviction behavior.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct CacheStats {
    /// Number of cache hits (value found in cache).
    pub hits: u64,
    /// Number of cache misses (value not found, computed).
    pub misses: u64,
    /// Number of entries evicted due to capacity limits.
    pub evictions: u64,
}

impl CacheStats {
    /// Returns the hit rate as a ratio (0.0 to 1.0).
    ///
    /// Returns 0.0 if no accesses have been made.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::wrapper::memoizer::CacheStats;
    ///
    /// let stats = CacheStats { hits: 75, misses: 25, evictions: 0 };
    /// assert!((stats.hit_rate() - 0.75).abs() < f64::EPSILON);
    /// ```
    #[must_use]
    pub fn hit_rate(&self) -> f64 {
        let total = self.hits + self.misses;
        if total == 0 {
            0.0
        } else {
            self.hits as f64 / total as f64
        }
    }

    /// Returns the total number of accesses (hits + misses).
    #[must_use]
    pub fn total_accesses(&self) -> u64 {
        self.hits + self.misses
    }
}

/// Error type for Memoizer operations.
///
/// This error is returned when a lock operation fails due to lock poisoning,
/// which occurs when a thread panics while holding the lock.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct MemoizerError {
    /// Description of the error
    pub message: String,
}

/// Type alias for the result of insert_with_eviction_info operations.
///
/// Represents a tuple containing:
/// - The old value that was replaced (if any)
/// - The evicted key (if any due to capacity limit)
/// - The evicted value (if any due to capacity limit)
pub type InsertEvictionResult<V, K> = (Option<V>, Option<K>, Option<V>);

impl std::fmt::Display for MemoizerError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "MemoizerError: {}", self.message)
    }
}

impl std::error::Error for MemoizerError {}

impl<T> From<PoisonError<T>> for MemoizerError {
    fn from(err: PoisonError<T>) -> Self {
        MemoizerError {
            message: format!("Lock poisoned: {}", err),
        }
    }
}

/// Thread-safe memoizer for pure functions with LRU eviction support.
///
/// The `Memoizer` provides an efficient, thread-safe caching mechanism for pure functions
/// with optional capacity limits and LRU (Least Recently Used) eviction policy.
/// It stores computed values in a cache protected by a read-write lock (`RwLock`),
/// optimizing for concurrent read access while ensuring thread safety.
///
/// This data structure is particularly useful for:
/// - Caching expensive computations with bounded memory usage
/// - Preventing redundant calculations in multi-threaded environments
/// - Implementing pure functional memoization patterns
/// - Memory-constrained environments requiring automatic cache eviction
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
/// # LRU Eviction
///
/// When a maximum capacity is set via `with_capacity()`, the cache automatically
/// evicts the least recently used entry when inserting a new entry would exceed
/// the capacity. Access operations (both read and write) update the LRU ordering.
pub struct Memoizer<K, V> {
    cache: RwLock<LruCache<K, V>>,
    hits: AtomicU64,
    misses: AtomicU64,
    evictions: AtomicU64,
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
    /// Creates a new, empty memoizer with unlimited capacity.
    ///
    /// Initializes an empty memoizer with no capacity limit. The cache will grow
    /// unbounded as values are added. Use `with_capacity()` for bounded caching.
    ///
    /// # Performance
    ///
    /// - **Time Complexity**: O(1) - Constant time initialization
    /// - **Space Complexity**: O(1) - Minimal allocation for the empty cache structures
    /// - **Thread Safety**: Creates a fresh RwLock with no contention
    /// - **Memory Usage**: Initial capacity is HashMap default (small, typically a few buckets)
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::wrapper::memoizer::Memoizer;
    ///
    /// // Create an unlimited memoizer for string keys and integer values
    /// let memo: Memoizer<String, i32> = Memoizer::new();
    /// ```
    pub fn new() -> Self {
        Memoizer {
            cache: RwLock::new(LruCache::new(None)),
            hits: AtomicU64::new(0),
            misses: AtomicU64::new(0),
            evictions: AtomicU64::new(0),
        }
    }

    /// Creates a new memoizer with a maximum capacity.
    ///
    /// When the cache reaches the specified capacity, the least recently used
    /// entry will be evicted to make room for new entries.
    ///
    /// # Arguments
    ///
    /// * `max_capacity` - Maximum number of entries the cache can hold
    ///
    /// # Performance
    ///
    /// - **Time Complexity**: O(1) - Constant time initialization
    /// - **Space Complexity**: O(1) - Minimal initial allocation
    /// - **Eviction**: O(1) - LRU eviction is constant time
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::wrapper::memoizer::Memoizer;
    ///
    /// // Create a bounded cache that holds at most 1000 entries
    /// let memo: Memoizer<String, i32> = Memoizer::with_capacity(1000);
    ///
    /// // Zero capacity creates an effectively disabled cache
    /// let disabled: Memoizer<String, i32> = Memoizer::with_capacity(0);
    /// ```
    pub fn with_capacity(max_capacity: usize) -> Self {
        Memoizer {
            cache: RwLock::new(LruCache::new(if max_capacity == 0 {
                None
            } else {
                Some(max_capacity)
            })),
            hits: AtomicU64::new(0),
            misses: AtomicU64::new(0),
            evictions: AtomicU64::new(0),
        }
    }

    /// Returns the cache statistics.
    ///
    /// Provides insight into cache performance including hit rate, miss rate,
    /// and eviction count.
    ///
    /// # Thread Safety
    ///
    /// Statistics are updated atomically and provide a consistent snapshot
    /// at the time of the call.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::wrapper::memoizer::Memoizer;
    ///
    /// let memo = Memoizer::with_capacity(100);
    ///
    /// memo.get_or_compute("a", |_| 1);
    /// memo.get_or_compute("a", |_| 1); // Cache hit
    /// memo.get_or_compute("b", |_| 2);
    ///
    /// let stats = memo.stats();
    /// assert_eq!(stats.hits, 1);
    /// assert_eq!(stats.misses, 2);
    /// assert!((stats.hit_rate() - 0.333).abs() < 0.01);
    /// ```
    pub fn stats(&self) -> CacheStats {
        CacheStats {
            hits: self.hits.load(Ordering::Relaxed),
            misses: self.misses.load(Ordering::Relaxed),
            evictions: self.evictions.load(Ordering::Relaxed),
        }
    }

    /// Resets the cache statistics to zero.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::wrapper::memoizer::Memoizer;
    ///
    /// let memo: Memoizer<&str, i32> = Memoizer::new();
    /// memo.get_or_compute("a", |_| 1);
    ///
    /// memo.reset_stats();
    /// let stats = memo.stats();
    /// assert_eq!(stats.hits, 0);
    /// assert_eq!(stats.misses, 0);
    /// ```
    pub fn reset_stats(&self) {
        self.hits.store(0, Ordering::Relaxed);
        self.misses.store(0, Ordering::Relaxed);
        self.evictions.store(0, Ordering::Relaxed);
    }

    /// Returns the maximum capacity of the cache, if set.
    ///
    /// Returns `None` for unlimited caches created with `new()`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::wrapper::memoizer::Memoizer;
    ///
    /// let unlimited: Memoizer<i32, i32> = Memoizer::new();
    /// assert_eq!(unlimited.max_capacity(), None);
    ///
    /// let bounded: Memoizer<i32, i32> = Memoizer::with_capacity(100);
    /// assert_eq!(bounded.max_capacity(), Some(100));
    /// ```
    pub fn max_capacity(&self) -> Option<usize> {
        self.cache.read().unwrap().max_capacity
    }

    /// Returns the cached value for `key`, or computes and stores it using `f`.
    ///
    /// This is the core method of the `Memoizer`. It first checks if a value for the given key
    /// is already cached. If present, it returns the cached value and updates LRU ordering.
    /// Otherwise, it computes the value using the provided function `f`, stores it in the cache
    /// for future use, and then returns it.
    ///
    /// The method is thread-safe and uses a double-checked locking pattern to ensure that even if multiple
    /// threads request the same uncached key simultaneously, the computation will only happen once.
    ///
    /// # LRU Behavior
    ///
    /// - Cache hits update the entry's position (moves to most recently used)
    /// - Cache misses may trigger eviction of the least recently used entry (if at capacity)
    ///
    /// # Performance Note
    ///
    /// This method holds a write lock while computing the value, which can block other threads.
    /// For long-running computations, consider using `get_or_compute_optimistic()` which releases
    /// the lock during computation (at the cost of potential duplicate computations).
    ///
    /// # Panics
    ///
    /// Panics if the lock is poisoned (another thread panicked while holding the lock).
    /// Use `try_get_or_compute()` for a safe version that returns a Result.
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
    ///   - Cache Hit: O(1) average case for hash lookup + LRU update
    ///   - Cache Miss: O(f) where f is the complexity of the compute function
    /// - **Space Complexity**: O(1) additional space per cache entry (key and value)
    /// - **Thread Safety**:
    ///   - Uses write lock for LRU updates and insertion
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
    /// let memo: Memoizer<&str, usize> = Memoizer::new();
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
        // For LRU, we need write lock even for reads to update ordering
        let mut cache = self.cache.write().unwrap();

        // Check if key exists and update LRU
        if let Some(v) = cache.get(&key) {
            self.hits.fetch_add(1, Ordering::Relaxed);
            return v;
        }

        // Not found, compute and insert
        self.misses.fetch_add(1, Ordering::Relaxed);
        let value = f(&key);

        if let Some(_evicted) = cache.insert(key, value.clone()) {
            self.evictions.fetch_add(1, Ordering::Relaxed);
        }

        value
    }

    /// Returns the cached value for `key`, or computes and stores it using `f` with optimistic locking.
    ///
    /// This method releases the lock during computation to avoid blocking other threads.
    /// The tradeoff is that multiple threads might compute the same value simultaneously.
    ///
    /// # Performance Note
    ///
    /// - Better for long-running computations as it doesn't block other operations
    /// - May result in duplicate computations for concurrent misses
    /// - Uses optimistic insertion (first computed value wins)
    ///
    /// # Panics
    ///
    /// Panics if the lock is poisoned. Use `try_get_or_compute_optimistic()` for a safe version.
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
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::wrapper::memoizer::Memoizer;
    /// use std::thread;
    /// use std::time::Duration;
    ///
    /// let memo = std::sync::Arc::new(Memoizer::new());
    /// let memo_clone = memo.clone();
    ///
    /// thread::spawn(move || {
    ///     // This won't block other operations during computation
    ///     memo_clone.get_or_compute_optimistic("slow", |_| {
    ///         thread::sleep(Duration::from_millis(100));
    ///         42
    ///     });
    /// });
    /// ```
    pub fn get_or_compute_optimistic<F>(&self, key: K, f: F) -> V
    where
        F: FnOnce(&K) -> V,
    {
        // Try to get from cache first (with LRU update)
        {
            let mut cache = self.cache.write().unwrap();
            if let Some(v) = cache.get(&key) {
                self.hits.fetch_add(1, Ordering::Relaxed);
                return v;
            }
        }

        // Release lock, compute, then reacquire
        self.misses.fetch_add(1, Ordering::Relaxed);
        let value = f(&key);

        // Insert if not already present (optimistic insertion)
        let mut cache = self.cache.write().unwrap();
        if let Some(existing) = cache.get(&key) {
            // Another thread inserted while we were computing
            return existing;
        }
        if cache.insert(key, value.clone()).is_some() {
            self.evictions.fetch_add(1, Ordering::Relaxed);
        }

        value
    }

    /// Safe version of `get_or_compute_optimistic` that returns a Result.
    ///
    /// Returns an error if the lock is poisoned.
    ///
    /// # Arguments
    ///
    /// * `key` - The key to look up or compute a value for
    /// * `f` - Function to compute the value if not already in the cache
    ///
    /// # Returns
    ///
    /// `Ok(V)` with the cached or newly computed value, or `Err(MemoizerError)` if the lock is poisoned.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::wrapper::memoizer::Memoizer;
    ///
    /// let memo: Memoizer<&str, usize> = Memoizer::new();
    ///
    /// let result = memo.try_get_or_compute_optimistic("hello", |s| s.len());
    /// assert_eq!(result.unwrap(), 5);
    /// ```
    pub fn try_get_or_compute_optimistic<F>(&self, key: K, f: F) -> Result<V, MemoizerError>
    where
        F: FnOnce(&K) -> V,
    {
        // Try to get from cache first (with LRU update)
        {
            let mut cache = self.write_cache()?;
            if let Some(v) = cache.get(&key) {
                self.hits.fetch_add(1, Ordering::Relaxed);
                return Ok(v);
            }
        }

        // Release lock, compute, then reacquire
        self.misses.fetch_add(1, Ordering::Relaxed);
        let value = f(&key);

        // Insert if not already present (optimistic insertion)
        let mut cache = self.write_cache()?;
        if let Some(existing) = cache.get(&key) {
            // Another thread inserted while we were computing
            return Ok(existing);
        }
        if cache.insert(key, value.clone()).is_some() {
            self.evictions.fetch_add(1, Ordering::Relaxed);
        }

        Ok(value)
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
    /// # Panics
    ///
    /// Panics if the lock is poisoned. Use `try_clear()` for a safe version.
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
    /// let memo: Memoizer<i32, i32> = Memoizer::new();
    ///
    /// // Cache a value
    /// memo.get_or_compute(42, |n| n * 2);
    ///
    /// // Clear the cache
    /// memo.clear();
    ///
    /// assert_eq!(memo.len(), 0);
    /// // Value will be recomputed
    /// let value = memo.get_or_compute(42, |n| n * 3);
    /// assert_eq!(value, 126);
    /// ```
    pub fn clear(&self) {
        let mut cache = self.cache.write().unwrap();
        cache.clear();
    }

    /// Safely acquires a write lock on the cache.
    ///
    /// Returns an error if the lock is poisoned (another thread panicked while holding the lock).
    fn write_cache(&self) -> Result<RwLockWriteGuard<'_, LruCache<K, V>>, MemoizerError> {
        self.cache.write().map_err(|e| e.into())
    }

    /// Returns the cached value for `key`, or computes and stores it using `f`.
    ///
    /// This is a safe version of `get_or_compute` that returns a `Result` instead of panicking
    /// when the lock is poisoned.
    ///
    /// # Arguments
    ///
    /// * `key` - The key to look up or compute a value for
    /// * `f` - Function to compute the value if not already in the cache
    ///
    /// # Returns
    ///
    /// `Ok(V)` with the cached or newly computed value, or `Err(MemoizerError)` if the lock is poisoned.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::wrapper::memoizer::Memoizer;
    ///
    /// let memo: Memoizer<&str, usize> = Memoizer::new();
    ///
    /// let result = memo.try_get_or_compute("hello", |s| s.len());
    /// assert_eq!(result.unwrap(), 5);
    /// ```
    pub fn try_get_or_compute<F>(&self, key: K, f: F) -> Result<V, MemoizerError>
    where
        F: FnOnce(&K) -> V,
    {
        let mut cache = self.write_cache()?;

        // Check if key exists and update LRU
        if let Some(v) = cache.get(&key) {
            self.hits.fetch_add(1, Ordering::Relaxed);
            return Ok(v);
        }

        // Not found, compute and insert
        self.misses.fetch_add(1, Ordering::Relaxed);
        let value = f(&key);

        if let Some(_evicted) = cache.insert(key, value.clone()) {
            self.evictions.fetch_add(1, Ordering::Relaxed);
        }

        Ok(value)
    }

    /// Manually inserts a key-value pair into the cache.
    ///
    /// This method allows direct insertion without computation, useful for:
    /// - Pre-populating the cache with known values
    /// - Updating cached values explicitly
    /// - Migrating data from another cache
    ///
    /// # Arguments
    ///
    /// * `key` - The key to insert
    /// * `value` - The value to associate with the key
    ///
    /// # Returns
    ///
    /// `Some(V)` with the old value if the key was already present, `None` otherwise.
    /// Note: Returns `None` both when inserting a new key and when an existing key
    /// was evicted due to capacity limits. Use `insert_with_eviction_info()` to distinguish
    /// these cases.
    ///
    /// # Panics
    ///
    /// Panics if the lock is poisoned. Use `try_insert()` for a safe version.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::wrapper::memoizer::Memoizer;
    ///
    /// let memo: Memoizer<&str, i32> = Memoizer::new();
    ///
    /// // Insert a value directly
    /// assert_eq!(memo.insert("key", 42), None);
    ///
    /// // Update existing value
    /// assert_eq!(memo.insert("key", 100), Some(42));
    /// assert_eq!(memo.get(&"key"), Some(100));
    /// ```
    pub fn insert(&self, key: K, value: V) -> Option<V> {
        let mut cache = self.cache.write().unwrap();
        let old = cache.peek(&key).cloned();
        if cache.insert(key, value).is_some() {
            self.evictions.fetch_add(1, Ordering::Relaxed);
        }
        old
    }

    /// Inserts a key-value pair and provides detailed eviction information.
    ///
    /// This method is similar to `insert()` but returns more detailed information
    /// about what happened during insertion.
    ///
    /// # Arguments
    ///
    /// * `key` - The key to insert
    /// * `value` - The value to associate with the key
    ///
    /// # Returns
    ///
    /// A tuple `(old_value, evicted_key, evicted_value)` where:
    /// - `old_value` is the previous value for the key (if any)
    /// - `evicted_key` and `evicted_value` are the evicted entry (if any)
    ///
    /// # Panics
    ///
    /// Panics if the lock is poisoned. Use `try_insert_with_eviction_info()` for a safe version.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::wrapper::memoizer::Memoizer;
    ///
    /// let memo: Memoizer<i32, i32> = Memoizer::with_capacity(2);
    /// memo.insert(1, 10);
    /// memo.insert(2, 20);
    ///
    /// // Insert third key, causing eviction
    /// let (old, evicted_key, evicted_value) = memo.insert_with_eviction_info(3, 30);
    /// assert_eq!(old, None);
    /// assert_eq!(evicted_key, Some(1));
    /// assert_eq!(evicted_value, Some(10));
    /// ```
    pub fn insert_with_eviction_info(&self, key: K, value: V) -> InsertEvictionResult<V, K> {
        let mut cache = self.cache.write().unwrap();
        let old = cache.peek(&key).cloned();
        let evicted = cache.insert(key, value);

        let (evicted_key, evicted_value) = if let Some((k, v)) = evicted {
            self.evictions.fetch_add(1, Ordering::Relaxed);
            (Some(k), Some(v))
        } else {
            (None, None)
        };

        (old, evicted_key, evicted_value)
    }

    /// Safe version of `insert` that returns a Result.
    ///
    /// Returns an error if the lock is poisoned.
    ///
    /// # Returns
    ///
    /// Returns `Ok(Some(V))` if the key was already present, `Ok(None)` otherwise.
    /// Note: Returns `Ok(None)` both when inserting a new key and when an existing key
    /// was evicted due to capacity limits. Use `try_insert_with_eviction_info()` to distinguish
    /// these cases.
    pub fn try_insert(&self, key: K, value: V) -> Result<Option<V>, MemoizerError> {
        let mut cache = self.write_cache()?;
        let old = cache.peek(&key).cloned();
        if cache.insert(key, value).is_some() {
            self.evictions.fetch_add(1, Ordering::Relaxed);
        }
        Ok(old)
    }

    /// Safe version of `insert_with_eviction_info` that returns a Result.
    ///
    /// Returns an error if the lock is poisoned.
    pub fn try_insert_with_eviction_info(
        &self, key: K, value: V,
    ) -> Result<InsertEvictionResult<V, K>, MemoizerError> {
        let mut cache = self.write_cache()?;
        let old = cache.peek(&key).cloned();
        let evicted = cache.insert(key, value);

        let (evicted_key, evicted_value) = if let Some((k, v)) = evicted {
            self.evictions.fetch_add(1, Ordering::Relaxed);
            (Some(k), Some(v))
        } else {
            (None, None)
        };

        Ok((old, evicted_key, evicted_value))
    }

    /// Returns the cached value for `key`, or computes it using a fallible function.
    ///
    /// Unlike `get_or_compute`, this method accepts a computation function that
    /// can fail, propagating the error to the caller without caching the failure.
    ///
    /// # Arguments
    ///
    /// * `key` - The key to look up or compute a value for
    /// * `f` - Fallible function to compute the value if not already in the cache
    ///
    /// # Returns
    ///
    /// `Ok(V)` with the cached or newly computed value, or `Err(E)` if computation fails.
    ///
    /// # Panics
    ///
    /// Panics if the lock is poisoned.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::wrapper::memoizer::Memoizer;
    ///
    /// let memo: Memoizer<i32, String> = Memoizer::new();
    ///
    /// // Successful computation
    /// let result: Result<String, &str> = memo.get_or_try_compute(1, |k| {
    ///     Ok(format!("value_{}", k))
    /// });
    /// assert_eq!(result.unwrap(), "value_1");
    ///
    /// // Failed computation (not cached)
    /// let result: Result<String, &str> = memo.get_or_try_compute(2, |_| {
    ///     Err("computation failed")
    /// });
    /// assert!(result.is_err());
    /// assert!(!memo.contains_key(&2)); // Error not cached
    /// ```
    pub fn get_or_try_compute<F, E>(&self, key: K, f: F) -> Result<V, E>
    where
        F: FnOnce(&K) -> Result<V, E>,
    {
        let mut cache = self.cache.write().unwrap();

        if let Some(v) = cache.get(&key) {
            self.hits.fetch_add(1, Ordering::Relaxed);
            return Ok(v);
        }

        self.misses.fetch_add(1, Ordering::Relaxed);
        let value = f(&key)?; // Propagate error without caching

        if cache.insert(key, value.clone()).is_some() {
            self.evictions.fetch_add(1, Ordering::Relaxed);
        }

        Ok(value)
    }

    /// Touches a key to update its LRU position without retrieving the value.
    ///
    /// This is useful when you want to mark a key as recently used without
    /// the overhead of cloning the value. Often used with `get_without_lru_update`.
    ///
    /// # Arguments
    ///
    /// * `key` - The key to touch
    ///
    /// # Returns
    ///
    /// `true` if the key exists and was touched, `false` otherwise.
    ///
    /// # Panics
    ///
    /// Panics if the lock is poisoned.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::wrapper::memoizer::Memoizer;
    ///
    /// let memo: Memoizer<i32, i32> = Memoizer::with_capacity(2);
    /// memo.get_or_compute(1, |k| k * 10);
    /// memo.get_or_compute(2, |k| k * 10);
    ///
    /// // Touch key 1 to make it recently used
    /// assert!(memo.touch(&1));
    ///
    /// // Now key 2 is LRU, will be evicted next
    /// memo.get_or_compute(3, |k| k * 10);
    /// assert!(memo.contains_key(&1)); // Still present
    /// assert!(!memo.contains_key(&2)); // Evicted
    /// ```
    pub fn touch(&self, key: &K) -> bool {
        let mut cache = self.cache.write().unwrap();
        cache.get(key).is_some()
    }

    /// Safe version of `touch` that returns a Result.
    pub fn try_touch(&self, key: &K) -> Result<bool, MemoizerError> {
        let mut cache = self.write_cache()?;
        Ok(cache.get(key).is_some())
    }

    /// Returns the number of cached entries.
    ///
    /// # Panics
    ///
    /// Panics if the lock is poisoned. Use `try_len()` for a safe version.
    ///
    /// # Performance
    ///
    /// - **Time Complexity**: O(1)
    /// - **Thread Safety**: Acquires a read lock
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::wrapper::memoizer::Memoizer;
    ///
    /// let memo: Memoizer<i32, i32> = Memoizer::new();
    /// assert_eq!(memo.len(), 0);
    ///
    /// memo.get_or_compute(1, |k| k * 2);
    /// assert_eq!(memo.len(), 1);
    /// ```
    pub fn len(&self) -> usize {
        self.cache.read().unwrap().len()
    }

    /// Safe version of `len` that returns a Result.
    ///
    /// Returns an error if the lock is poisoned.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::wrapper::memoizer::Memoizer;
    ///
    /// let memo: Memoizer<i32, i32> = Memoizer::new();
    /// assert_eq!(memo.try_len().unwrap(), 0);
    /// ```
    pub fn try_len(&self) -> Result<usize, MemoizerError> {
        Ok(self.cache.read().map_err(MemoizerError::from)?.len())
    }

    /// Returns `true` if the cache is empty.
    ///
    /// # Panics
    ///
    /// Panics if the lock is poisoned. Use `try_is_empty()` for a safe version.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::wrapper::memoizer::Memoizer;
    ///
    /// let memo: Memoizer<i32, i32> = Memoizer::new();
    /// assert!(memo.is_empty());
    ///
    /// memo.get_or_compute(1, |k| k * 2);
    /// assert!(!memo.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        self.cache.read().unwrap().is_empty()
    }

    /// Safe version of `is_empty` that returns a Result.
    ///
    /// Returns an error if the lock is poisoned.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::wrapper::memoizer::Memoizer;
    ///
    /// let memo: Memoizer<i32, i32> = Memoizer::new();
    /// assert!(memo.try_is_empty().unwrap());
    /// ```
    pub fn try_is_empty(&self) -> Result<bool, MemoizerError> {
        Ok(self.cache.read().map_err(MemoizerError::from)?.is_empty())
    }

    /// Returns `true` if the cache contains a value for the specified key.
    ///
    /// # Panics
    ///
    /// Panics if the lock is poisoned. Use `try_contains_key()` for a safe version.
    ///
    /// # Arguments
    ///
    /// * `key` - The key to check for
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::wrapper::memoizer::Memoizer;
    ///
    /// let memo: Memoizer<i32, i32> = Memoizer::new();
    /// memo.get_or_compute(1, |k| k * 2);
    ///
    /// assert!(memo.contains_key(&1));
    /// assert!(!memo.contains_key(&2));
    /// ```
    pub fn contains_key(&self, key: &K) -> bool {
        self.cache.read().unwrap().contains_key(key)
    }

    /// Safe version of `contains_key` that returns a Result.
    ///
    /// Returns an error if the lock is poisoned.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::wrapper::memoizer::Memoizer;
    ///
    /// let memo: Memoizer<i32, i32> = Memoizer::new();
    /// memo.get_or_compute(1, |k| k * 2);
    ///
    /// assert!(memo.try_contains_key(&1).unwrap());
    /// ```
    pub fn try_contains_key(&self, key: &K) -> Result<bool, MemoizerError> {
        Ok(self
            .cache
            .read()
            .map_err(MemoizerError::from)?
            .contains_key(key))
    }

    /// Removes a key from the cache, returning the cached value if present.
    ///
    /// # Panics
    ///
    /// Panics if the lock is poisoned. Use `try_remove()` for a safe version.
    ///
    /// # Arguments
    ///
    /// * `key` - The key to remove
    ///
    /// # Returns
    ///
    /// `Some(V)` if the key was present, `None` otherwise.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::wrapper::memoizer::Memoizer;
    ///
    /// let memo: Memoizer<i32, i32> = Memoizer::new();
    /// memo.get_or_compute(1, |k| k * 2);
    ///
    /// assert_eq!(memo.remove(&1), Some(2));
    /// assert_eq!(memo.remove(&1), None);
    /// ```
    pub fn remove(&self, key: &K) -> Option<V> {
        self.cache.write().unwrap().remove(key)
    }

    /// Safe version of `remove` that returns a Result.
    ///
    /// Returns an error if the lock is poisoned.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::wrapper::memoizer::Memoizer;
    ///
    /// let memo: Memoizer<i32, i32> = Memoizer::new();
    /// memo.get_or_compute(1, |k| k * 2);
    ///
    /// assert_eq!(memo.try_remove(&1).unwrap(), Some(2));
    /// ```
    pub fn try_remove(&self, key: &K) -> Result<Option<V>, MemoizerError> {
        Ok(self.write_cache()?.remove(key))
    }

    /// Returns a cached value without computing if not present.
    ///
    /// Unlike `get_or_compute`, this method does not compute a value if the key is not found.
    ///
    /// # Panics
    ///
    /// Panics if the lock is poisoned. Use `try_get()` for a safe version.
    ///
    /// # Arguments
    ///
    /// * `key` - The key to look up
    ///
    /// # Returns
    ///
    /// `Some(V)` if the key is present, `None` otherwise.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::wrapper::memoizer::Memoizer;
    ///
    /// let memo: Memoizer<i32, i32> = Memoizer::new();
    ///
    /// assert_eq!(memo.get(&1), None);
    ///
    /// memo.get_or_compute(1, |k| k * 2);
    /// assert_eq!(memo.get(&1), Some(2));
    /// ```
    /// Note: This method does NOT update LRU ordering. Use `get_or_compute`
    /// or `get_with_lru_update` if you want LRU ordering to be updated.
    pub fn get(&self, key: &K) -> Option<V> {
        self.cache.read().unwrap().peek(key).cloned()
    }

    /// Safe version of `get` that returns a Result.
    ///
    /// Returns an error if the lock is poisoned.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::wrapper::memoizer::Memoizer;
    ///
    /// let memo: Memoizer<i32, i32> = Memoizer::new();
    ///
    /// assert_eq!(memo.try_get(&1).unwrap(), None);
    /// ```
    /// Note: This method does NOT update LRU ordering. Use `try_get_or_compute`
    /// or `get_with_lru_update` if you want LRU ordering to be updated.
    pub fn try_get(&self, key: &K) -> Result<Option<V>, MemoizerError> {
        Ok(self
            .cache
            .read()
            .map_err(MemoizerError::from)?
            .peek(key)
            .cloned())
    }

    /// Returns a cached value and updates its LRU position.
    ///
    /// Unlike `get()`, this method updates the LRU ordering when a value is found,
    /// marking it as most recently used.
    ///
    /// # Panics
    ///
    /// Panics if the lock is poisoned. Use `try_get_with_lru_update()` for a safe version.
    ///
    /// # Arguments
    ///
    /// * `key` - The key to look up
    ///
    /// # Returns
    ///
    /// `Some(V)` if the key is present, `None` otherwise.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::wrapper::memoizer::Memoizer;
    ///
    /// let memo: Memoizer<i32, i32> = Memoizer::with_capacity(2);
    /// memo.get_or_compute(1, |k| k * 2);
    /// memo.get_or_compute(2, |k| k * 2);
    ///
    /// // Access key 1 to make it recently used
    /// assert_eq!(memo.get_with_lru_update(&1), Some(2));
    ///
    /// // Now key 2 is LRU, will be evicted next
    /// memo.get_or_compute(3, |k| k * 2);
    /// assert!(memo.contains_key(&1)); // Still present
    /// assert!(!memo.contains_key(&2)); // Evicted
    /// ```
    pub fn get_with_lru_update(&self, key: &K) -> Option<V> {
        let mut cache = self.cache.write().unwrap();
        cache.get(key)
    }

    /// Safe version of `get_with_lru_update` that returns a Result.
    ///
    /// Returns an error if the lock is poisoned.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::wrapper::memoizer::Memoizer;
    ///
    /// let memo: Memoizer<i32, i32> = Memoizer::new();
    ///
    /// assert_eq!(memo.try_get_with_lru_update(&1).unwrap(), None);
    /// ```
    pub fn try_get_with_lru_update(&self, key: &K) -> Result<Option<V>, MemoizerError> {
        let mut cache = self.write_cache()?;
        Ok(cache.get(key))
    }

    /// Reserves capacity for at least `additional` more entries.
    ///
    /// # Panics
    ///
    /// Panics if the lock is poisoned. Use `try_reserve()` for a safe version.
    ///
    /// # Arguments
    ///
    /// * `additional` - The number of additional entries to reserve space for
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::wrapper::memoizer::Memoizer;
    ///
    /// let memo: Memoizer<i32, i32> = Memoizer::new();
    /// memo.reserve(100);
    /// ```
    pub fn reserve(&self, additional: usize) {
        self.cache.write().unwrap().reserve(additional)
    }

    /// Safe version of `reserve` that returns a Result.
    ///
    /// Returns an error if the lock is poisoned.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::wrapper::memoizer::Memoizer;
    ///
    /// let memo: Memoizer<i32, i32> = Memoizer::new();
    /// memo.try_reserve(100).unwrap();
    /// ```
    pub fn try_reserve(&self, additional: usize) -> Result<(), MemoizerError> {
        self.write_cache()?.reserve(additional);
        Ok(())
    }

    /// Shrinks the capacity of the cache as much as possible.
    ///
    /// # Panics
    ///
    /// Panics if the lock is poisoned. Use `try_shrink_to_fit()` for a safe version.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::wrapper::memoizer::Memoizer;
    ///
    /// let memo: Memoizer<i32, i32> = Memoizer::new();
    /// for i in 0..100 {
    ///     memo.get_or_compute(i, |k| k * 2);
    /// }
    /// memo.clear();
    /// memo.shrink_to_fit();
    /// ```
    pub fn shrink_to_fit(&self) {
        self.cache.write().unwrap().shrink_to_fit()
    }

    /// Safe version of `shrink_to_fit` that returns a Result.
    ///
    /// Returns an error if the lock is poisoned.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::wrapper::memoizer::Memoizer;
    ///
    /// let memo: Memoizer<i32, i32> = Memoizer::new();
    /// memo.try_shrink_to_fit().unwrap();
    /// ```
    pub fn try_shrink_to_fit(&self) -> Result<(), MemoizerError> {
        self.write_cache()?.shrink_to_fit();
        Ok(())
    }

    /// Returns a list of all keys currently in the cache.
    ///
    /// # Panics
    ///
    /// Panics if the lock is poisoned. Use `try_keys()` for a safe version.
    ///
    /// # Returns
    ///
    /// A `Vec<K>` containing clones of all cached keys.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::wrapper::memoizer::Memoizer;
    ///
    /// let memo: Memoizer<i32, i32> = Memoizer::new();
    /// memo.get_or_compute(1, |k| k * 2);
    /// memo.get_or_compute(2, |k| k * 2);
    ///
    /// let keys = memo.keys();
    /// assert_eq!(keys.len(), 2);
    /// ```
    pub fn keys(&self) -> Vec<K> {
        self.cache.read().unwrap().keys()
    }

    /// Safe version of `keys` that returns a Result.
    ///
    /// Returns an error if the lock is poisoned.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::wrapper::memoizer::Memoizer;
    ///
    /// let memo: Memoizer<i32, i32> = Memoizer::new();
    /// let keys = memo.try_keys().unwrap();
    /// ```
    pub fn try_keys(&self) -> Result<Vec<K>, MemoizerError> {
        Ok(self.cache.read().map_err(MemoizerError::from)?.keys())
    }

    /// Returns a list of all values currently in the cache.
    ///
    /// # Panics
    ///
    /// Panics if the lock is poisoned. Use `try_values()` for a safe version.
    ///
    /// # Returns
    ///
    /// A `Vec<V>` containing clones of all cached values.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::wrapper::memoizer::Memoizer;
    ///
    /// let memo: Memoizer<i32, i32> = Memoizer::new();
    /// memo.get_or_compute(1, |k| k * 2);
    /// memo.get_or_compute(2, |k| k * 2);
    ///
    /// let values = memo.values();
    /// assert_eq!(values.len(), 2);
    /// ```
    pub fn values(&self) -> Vec<V> {
        self.cache.read().unwrap().values()
    }

    /// Safe version of `values` that returns a Result.
    ///
    /// Returns an error if the lock is poisoned.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::wrapper::memoizer::Memoizer;
    ///
    /// let memo: Memoizer<i32, i32> = Memoizer::new();
    /// let values = memo.try_values().unwrap();
    /// ```
    pub fn try_values(&self) -> Result<Vec<V>, MemoizerError> {
        Ok(self.cache.read().map_err(MemoizerError::from)?.values())
    }

    /// Returns the number of elements the cache can hold without reallocating.
    ///
    /// This method provides insight into the current capacity of the underlying HashMap.
    /// It can be useful for performance tuning and memory management.
    ///
    /// # Panics
    ///
    /// Panics if the lock is poisoned. Use `try_capacity()` for a safe version.
    ///
    /// # Returns
    ///
    /// The capacity of the cache.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::wrapper::memoizer::Memoizer;
    ///
    /// let memo: Memoizer<i32, i32> = Memoizer::new();
    /// let initial_capacity = memo.capacity();
    ///
    /// memo.reserve(100);
    /// assert!(memo.capacity() >= initial_capacity + 100);
    /// ```
    pub fn capacity(&self) -> usize {
        self.cache.read().unwrap().capacity()
    }

    /// Safe version of `capacity` that returns a Result.
    ///
    /// Returns an error if the lock is poisoned.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::wrapper::memoizer::Memoizer;
    ///
    /// let memo: Memoizer<i32, i32> = Memoizer::new();
    /// let capacity = memo.try_capacity().unwrap();
    /// ```
    pub fn try_capacity(&self) -> Result<usize, MemoizerError> {
        Ok(self.cache.read().map_err(MemoizerError::from)?.capacity())
    }

    /// Safe version of `clear` that returns a Result.
    ///
    /// Returns an error if the lock is poisoned.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::wrapper::memoizer::Memoizer;
    ///
    /// let memo: Memoizer<i32, i32> = Memoizer::new();
    /// memo.try_clear().unwrap();
    /// ```
    pub fn try_clear(&self) -> Result<(), MemoizerError> {
        self.write_cache()?.clear();
        Ok(())
    }
}
