//! Unified cache, chunk, and memory management for PersistentVector.
//!
//! This module integrates caching logic, chunked storage, and custom memory
//! management for efficient persistent vector operations. All types here are
//! internal unless explicitly re-exported in mod.rs.

use std::collections::VecDeque;
use std::convert::AsRef;
use std::fmt::{self, Debug as StdDebug};
use std::iter::FromIterator;
use std::ops::{Index, IndexMut, Range};
use std::sync::Arc;
use std::sync::atomic::{AtomicUsize, Ordering};

use crate::pvec::node::Node;

use parking_lot::Mutex;

pub(super) const MAX_CACHE_LEVELS: usize = 10;

pub type BoxedCachePolicy = Box<dyn CachePolicy>;

#[derive(Clone, Debug, PartialEq, Eq, Default)]
pub(super) struct IndexCache {
    pub index: usize,
    pub path: [usize; MAX_CACHE_LEVELS],
    pub ranges: [Range<usize>; MAX_CACHE_LEVELS],
    pub len: usize,
    pub hits: usize,
    pub misses: usize,
}

impl IndexCache {
    #[inline(always)]
    /// Creates a new `IndexCache` instance.
    pub fn new() -> Self {
        Self::default()
    }

    #[inline(always)]
    /// Checks if the cache is valid.
    pub fn is_valid(&self) -> bool {
        self.len > 0
    }

    #[inline(always)]
    /// Invalidates the cache.
    pub fn invalidate(&mut self) {
        self.len = 0;
    }

    #[inline(always)]
    /// Updates the cache with the given index, path, and ranges.
    pub fn update(&mut self, index: usize, path: &[usize], ranges: &[Range<usize>]) {
        self.index = index;
        self.len = path.len().min(MAX_CACHE_LEVELS);
        self.path[..self.len].copy_from_slice(&path[..self.len]);
        self.ranges[..self.len].clone_from_slice(&ranges[..self.len]);
    }

    #[inline(always)]
    /// Records a cache hit.
    pub fn record_hit(&mut self) {
        self.hits += 1;
    }

    #[inline(always)]
    /// Records a cache miss.
    pub fn record_miss(&mut self) {
        self.misses += 1;
    }
}

/// Trait for cache policy strategies used by PersistentVector.
/// Implementors decide whether to cache a given index.
pub trait CachePolicy: Send + Sync {
    fn should_cache(&self, index: usize) -> bool;
    fn clone_box(&self) -> BoxedCachePolicy;
}

impl Clone for BoxedCachePolicy {
    #[inline(always)]
    fn clone(&self) -> BoxedCachePolicy {
        self.clone_box()
    }
}

/// Cache policy implementations.
///
/// These structs implement the `CachePolicy` trait and decide whether to cache a given index.
#[derive(Clone)]
pub struct AlwaysCache;
impl CachePolicy for AlwaysCache {
    #[inline(always)]
    fn should_cache(&self, _index: usize) -> bool {
        true
    }
    #[inline(always)]
    fn clone_box(&self) -> BoxedCachePolicy {
        Box::new(self.clone())
    }
}

#[derive(Clone)]
pub struct NeverCache;
impl CachePolicy for NeverCache {
    #[inline(always)]
    fn should_cache(&self, _index: usize) -> bool {
        false
    }
    #[inline(always)]
    fn clone_box(&self) -> BoxedCachePolicy {
        Box::new(self.clone())
    }
}

#[derive(Clone)]
pub struct EvenIndexCache;
impl CachePolicy for EvenIndexCache {
    #[inline(always)]
    fn should_cache(&self, index: usize) -> bool {
        index.is_multiple_of(2)
    }
    #[inline(always)]
    fn clone_box(&self) -> BoxedCachePolicy {
        Box::new(self.clone())
    }
}

pub(crate) const DEFAULT_CHUNK_SIZE: usize = 32;
pub(crate) const CHUNK_BITS: usize = 5;

#[derive(Clone, PartialEq, Eq)]
pub(crate) struct Chunk<T> {
    elements: Vec<T>,
    chunk_size: usize,
}

impl<T> Chunk<T> {
    /// Creates a new `Chunk` instance with a given chunk size.
    pub fn new_with_size(chunk_size: usize) -> Self {
        Self {
            elements: Vec::with_capacity(chunk_size),
            chunk_size,
        }
    }
    /// Creates a new `Chunk` with the default chunk size.
    pub fn new() -> Self {
        Self::new_with_size(DEFAULT_CHUNK_SIZE)
    }
    /// Checks if the chunk is full.
    pub fn is_full(&self) -> bool {
        self.elements.len() >= self.chunk_size
    }

    #[inline(always)]
    /// Returns the length of the chunk.
    pub fn len(&self) -> usize {
        self.elements.len()
    }

    #[inline(always)]
    /// Returns a reference to the element at the given index.
    pub fn get(&self, index: usize) -> Option<&T> {
        self.elements.get(index)
    }

    #[inline(always)]
    /// Returns a mutable reference to the element at the given index.
    pub fn get_mut(&mut self, index: usize) -> Option<&mut T> {
        self.elements.get_mut(index)
    }

    #[inline(always)]
    /// Pushes a new element onto the chunk.
    pub fn push_back(&mut self, value: T) -> bool {
        if self.is_full() {
            return false;
        }
        self.elements.push(value);
        true
    }
}

impl<T> FromIterator<T> for Chunk<T> {
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        let chunk_size = DEFAULT_CHUNK_SIZE; // Could be parameterized if needed
        let mut elements = Vec::with_capacity(chunk_size);
        for item in iter.into_iter().take(chunk_size) {
            elements.push(item);
        }
        Self {
            elements,
            chunk_size,
        }
    }
}

impl<T> Default for Chunk<T> {
    #[inline(always)]
    fn default() -> Self {
        Self::new()
    }
}

impl<T: Clone + StdDebug> StdDebug for Chunk<T> {
    #[inline(always)]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self.elements.iter()).finish()
    }
}

impl<T: Clone> Index<usize> for Chunk<T> {
    type Output = T;
    #[inline(always)]
    fn index(&self, index: usize) -> &Self::Output {
        &self.elements[index]
    }
}

impl<T: Clone> IndexMut<usize> for Chunk<T> {
    #[inline(always)]
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        &mut self.elements[index]
    }
}

pub(crate) const DEFAULT_POOL_CAPACITY: usize = 128;

#[derive(Debug, Clone, Copy, PartialEq)]
pub enum AllocationStrategy {
    Direct,
    Pooled,
    Adaptive,
}

#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct MemoryStats {
    pub node_pool_size: usize,
    pub node_pool_capacity: usize,
    pub chunk_pool_size: usize,
    pub chunk_pool_capacity: usize,
    pub node_allocations: usize,
    pub chunk_allocations: usize,
    pub node_pool_hits: usize,
    pub chunk_pool_hits: usize,
}

pub struct MemoryManager<T> {
    allocation_strategy: AllocationStrategy,
    node_pool: Arc<Mutex<ObjectPool<Node<T>>>>,
    chunk_pool: Arc<Mutex<ObjectPool<Chunk<T>>>>,
    node_allocations: AtomicUsize,
    chunk_allocations: AtomicUsize,
    node_pool_hits: AtomicUsize,
    chunk_pool_hits: AtomicUsize,
}

impl<T: Clone> MemoryManager<T> {
    #[inline(always)]
    /// Creates a new `MemoryManager` instance.
    pub fn new(strategy: AllocationStrategy) -> Self {
        Self {
            allocation_strategy: strategy,
            node_pool: Arc::new(Mutex::new(ObjectPool::new(DEFAULT_POOL_CAPACITY))),
            chunk_pool: Arc::new(Mutex::new(ObjectPool::new(DEFAULT_POOL_CAPACITY))),
            node_allocations: AtomicUsize::new(0),
            chunk_allocations: AtomicUsize::new(0),
            node_pool_hits: AtomicUsize::new(0),
            chunk_pool_hits: AtomicUsize::new(0),
        }
    }

    #[inline(always)]
    /// Reserves chunks in the chunk pool.
    pub fn reserve_chunks(&self, count: usize) {
        let mut pool = self.chunk_pool.lock();
        if pool.size() < count {
            pool.prefill(|| Chunk::new_with_size(DEFAULT_CHUNK_SIZE));
        }
    }

    #[inline(always)]
    /// Returns the allocation strategy.
    pub fn strategy(&self) -> AllocationStrategy {
        self.allocation_strategy
    }

    #[inline(always)]
    /// Sets the allocation strategy.
    pub fn set_strategy(&mut self, strategy: AllocationStrategy) {
        self.allocation_strategy = strategy;
    }

    /// Allocate a node according to the current strategy (with adaptive logic).
    pub(crate) fn allocate_node(&self, value: Node<T>) -> ManagedRef<Node<T>> {
        match self.allocation_strategy {
            AllocationStrategy::Direct => {
                self.node_allocations.fetch_add(1, Ordering::Relaxed);
                ManagedRef::new(Arc::new(value))
            },
            AllocationStrategy::Pooled => {
                self.node_allocations.fetch_add(1, Ordering::Relaxed);
                let mut pool = self.node_pool.lock();
                if let Some(obj) = pool.get() {
                    *Arc::get_mut(&mut Arc::clone(&obj)).unwrap() = value;
                    ManagedRef::from(obj)
                } else {
                    ManagedRef::new(Arc::new(value))
                }
            },
            AllocationStrategy::Adaptive => {
                self.node_allocations.fetch_add(1, Ordering::Relaxed);
                ManagedRef::new(Arc::new(value))
            },
        }
    }

    /// Allocate a chunk according to the current strategy (with adaptive logic).
    pub(crate) fn allocate_chunk(&self, value: Chunk<T>) -> ManagedRef<Chunk<T>> {
        match self.allocation_strategy {
            AllocationStrategy::Direct => {
                self.chunk_allocations.fetch_add(1, Ordering::Relaxed);
                ManagedRef::new(Arc::new(value))
            },
            AllocationStrategy::Pooled => {
                self.chunk_allocations.fetch_add(1, Ordering::Relaxed);
                let mut pool = self.chunk_pool.lock();
                if let Some(obj) = pool.get() {
                    *Arc::get_mut(&mut Arc::clone(&obj)).unwrap() = value;
                    ManagedRef::from(obj)
                } else {
                    ManagedRef::new(Arc::new(value))
                }
            },
            AllocationStrategy::Adaptive => {
                self.chunk_allocations.fetch_add(1, Ordering::Relaxed);
                ManagedRef::new(Arc::new(value))
            },
        }
    }

    /// Returns memory statistics.
    pub fn stats(&self) -> MemoryStats {
        let node_pool = self.node_pool.lock();
        let chunk_pool = self.chunk_pool.lock();
        MemoryStats {
            node_pool_size: node_pool.size(),
            chunk_pool_size: chunk_pool.size(),
            node_pool_capacity: node_pool.capacity(),
            chunk_pool_capacity: chunk_pool.capacity(),
            node_allocations: self.node_allocations.load(Ordering::Relaxed),
            chunk_allocations: self.chunk_allocations.load(Ordering::Relaxed),
            node_pool_hits: self.node_pool_hits.load(Ordering::Relaxed),
            chunk_pool_hits: self.chunk_pool_hits.load(Ordering::Relaxed),
        }
    }
}

impl<T: Clone> Clone for MemoryManager<T> {
    #[inline(always)]
    fn clone(&self) -> Self {
        Self {
            allocation_strategy: self.allocation_strategy,
            node_pool: self.node_pool.clone(),
            chunk_pool: self.chunk_pool.clone(),
            node_allocations: AtomicUsize::new(self.node_allocations.load(Ordering::Relaxed)),
            chunk_allocations: AtomicUsize::new(self.chunk_allocations.load(Ordering::Relaxed)),
            node_pool_hits: AtomicUsize::new(self.node_pool_hits.load(Ordering::Relaxed)),
            chunk_pool_hits: AtomicUsize::new(self.chunk_pool_hits.load(Ordering::Relaxed)),
        }
    }
}

impl<T: Clone> Default for MemoryManager<T> {
    #[inline(always)]
    fn default() -> Self {
        Self::new(AllocationStrategy::Pooled)
    }
}

impl<T: Clone + StdDebug> StdDebug for MemoryManager<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("MemoryManager")
            .field("allocation_strategy", &self.allocation_strategy)
            .field("stats", &self.stats())
            .finish()
    }
}

impl<T: Clone> PartialEq for MemoryManager<T> {
    #[inline(always)]
    fn eq(&self, other: &Self) -> bool {
        self.allocation_strategy == other.allocation_strategy
    }
}

impl<T: Clone> Eq for MemoryManager<T> {}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AccessPattern {
    /// Sequential access pattern (e.g., iteration, scanning)
    Sequential,
    /// Random access pattern (e.g., frequent indexing, shuffling)
    Random,
}

impl std::fmt::Display for AccessPattern {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            AccessPattern::Sequential => write!(f, "Sequential"),
            AccessPattern::Random => write!(f, "Random"),
        }
    }
}

impl<T: Clone> MemoryManager<T> {
    /// Optimize the memory manager for a given size and access pattern.
    ///
    /// This method adjusts the allocation strategy and chunk pool based on the
    /// expected vector size and access pattern to reduce memory overhead and improve performance.
    ///
    /// # Arguments
    ///
    /// * `size` - The expected size of the vector.
    /// * `access_pattern` - The expected access pattern (sequential or random).
    pub fn optimize_for(&mut self, size: usize, access_pattern: AccessPattern) {
        match (size, access_pattern) {
            (s, _) if s < 1000 => {
                self.set_strategy(AllocationStrategy::Direct);
            },
            (_, AccessPattern::Random) => {
                self.set_strategy(AllocationStrategy::Adaptive);
                self.reserve_chunks(size / DEFAULT_CHUNK_SIZE + 1);
            },
            (_, AccessPattern::Sequential) => {
                self.set_strategy(AllocationStrategy::Pooled);
                // Prefill the chunk pool for sequential access
                let mut pool = self.chunk_pool.lock();
                pool.prefill(|| Chunk::new_with_size(DEFAULT_CHUNK_SIZE));
            },
        }
    }
}

pub(crate) struct ManagedRef<T> {
    inner: Arc<T>,
}

impl<T> ManagedRef<T> {
    #[inline(always)]
    /// Creates a new `ManagedRef` instance.
    pub fn new(obj: Arc<T>) -> Self {
        Self { inner: obj }
    }

    #[inline(always)]
    /// Returns a reference to the inner object.
    pub fn inner(&self) -> &Arc<T> {
        &self.inner
    }
}

impl<T> From<Arc<T>> for ManagedRef<T> {
    #[inline(always)]
    fn from(obj: Arc<T>) -> Self {
        ManagedRef::new(obj)
    }
}

impl<T> Clone for ManagedRef<T> {
    #[inline(always)]
    fn clone(&self) -> Self {
        ManagedRef {
            inner: self.inner.clone(),
        }
    }
}

impl<T> AsRef<T> for ManagedRef<T> {
    #[inline(always)]
    fn as_ref(&self) -> &T {
        &self.inner
    }
}

impl<T> std::ops::Deref for ManagedRef<T> {
    type Target = T;
    #[inline(always)]
    fn deref(&self) -> &Self::Target {
        &self.inner
    }
}

impl<T: StdDebug> StdDebug for ManagedRef<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("ManagedRef")
            .field("inner", &self.inner)
            .finish()
    }
}

impl<T: PartialEq> PartialEq for ManagedRef<T> {
    fn eq(&self, other: &Self) -> bool {
        *self.inner == *other.inner
    }
}

impl<T: Eq> Eq for ManagedRef<T> {}

pub(crate) struct ObjectPool<T> {
    pool: VecDeque<Arc<T>>,
    capacity: usize,
}

impl<T> ObjectPool<T> {
    pub fn new(capacity: usize) -> Self {
        Self {
            pool: VecDeque::with_capacity(capacity),
            capacity,
        }
    }

    pub fn size(&self) -> usize {
        self.pool.len()
    }
    pub fn capacity(&self) -> usize {
        self.capacity
    }
    pub fn prefill<F: Fn() -> T>(&mut self, create_fn: F) {
        while self.pool.len() < self.capacity {
            self.pool.push_back(Arc::new(create_fn()));
        }
    }
    pub fn get(&mut self) -> Option<Arc<T>> {
        self.pool.pop_front()
    }
}
