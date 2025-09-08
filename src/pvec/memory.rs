//! Unified cache, chunk, and memory management for PersistentVector.
//!
//! This module integrates caching logic, chunked storage, and custom memory
//! management for efficient persistent vector operations. All types here are
//! internal unless explicitly re-exported in mod.rs.

use std::any::TypeId;
use std::collections::{HashMap, VecDeque};
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

/// Hierarchical chunk sizing for optimal memory usage
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ChunkSize {
    /// 1-8 elements (inline storage)
    Tiny(u8),
    /// 9-32 elements (small vector)
    Small(u8),
    /// 33-128 elements (medium vector)
    Medium(u8),
    /// 129+ elements (large vector)
    Large(u16),
}

impl ChunkSize {
    /// Determines optimal chunk size for given element count
    #[inline(always)]
    pub fn optimal_for(size: usize) -> Self {
        match size {
            0..=8 => ChunkSize::Tiny(size as u8),
            9..=32 => ChunkSize::Small(32),
            33..=128 => ChunkSize::Medium(64),
            _ => ChunkSize::Large(128),
        }
    }

    /// Gets the actual size value
    #[inline(always)]
    pub fn size(&self) -> usize {
        match self {
            ChunkSize::Tiny(s) => *s as usize,
            ChunkSize::Small(s) => *s as usize,
            ChunkSize::Medium(s) => *s as usize,
            ChunkSize::Large(s) => *s as usize,
        }
    }
}

#[derive(Clone, PartialEq, Eq)]
pub(crate) struct Chunk<T> {
    elements: Vec<T>,
    chunk_size: ChunkSize,
}

impl<T> Chunk<T> {
    /// Creates a new `Chunk` instance with a given chunk size.
    pub fn new_with_size(chunk_size: ChunkSize) -> Self {
        let capacity = chunk_size.size();
        Self {
            elements: Vec::with_capacity(capacity),
            chunk_size,
        }
    }

    /// Creates a new `Chunk` with the default chunk size.
    pub fn new() -> Self {
        Self::new_with_size(ChunkSize::Small(DEFAULT_CHUNK_SIZE as u8))
    }

    /// Checks if the chunk is full.
    pub fn is_full(&self) -> bool {
        self.elements.len() >= self.chunk_size.size()
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
        let iter = iter.into_iter();

        // Optimize capacity based on iterator size hints
        let (lower, upper) = iter.size_hint();
        let estimated_size = match upper {
            Some(exact) if exact == lower => exact,
            Some(upper_bound) => upper_bound,
            None => lower.max(DEFAULT_CHUNK_SIZE),
        };

        let chunk_size = ChunkSize::optimal_for(estimated_size);
        let capacity = chunk_size.size();

        let mut elements = Vec::with_capacity(capacity.max(8)); // Ensure minimum capacity
        for item in iter.take(capacity) {
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
    /// Direct allocation strategy (no pooling)
    Direct,
    /// Pooled allocation strategy (with pooling)
    Pooled,
    /// Adaptive allocation strategy (dynamic pooling)
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

/// Detailed allocation statistics for a specific type
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct AllocationStats {
    pub count: usize,
    pub pool_hits: usize,
    pub pool_misses: usize,
    pub memory_usage: usize,
}

impl AllocationStats {
    #[inline(always)]
    pub fn hit_rate(&self) -> f64 {
        if self.count == 0 {
            0.0
        } else {
            self.pool_hits as f64 / self.count as f64
        }
    }
}

/// Comprehensive memory profiling information using Functor patterns.
///
/// A Functor is a design pattern that allows a function to be applied to a value
/// inside a generic container (or 'context') without changing the container's structure.
/// The `map` function is the hallmark of a Functor.
///
/// Here, `MemoryProfile` acts as a container for `AllocationStats`. The `map_allocations`
/// method allows transforming the statistics (the contained values) while preserving the
/// overall `HashMap` structure, making the profiling data more versatile.
#[derive(Debug, Clone)]
pub struct MemoryProfile {
    pub allocations: HashMap<TypeId, AllocationStats>,
    pub fragmentation_ratio: f64,
    pub cache_efficiency: f64,
    pub duration: std::time::Duration,
    pub peak_memory_usage: usize,
}

impl MemoryProfile {
    /// Maps over allocation statistics using Functor pattern
    pub fn map_allocations<F>(&self, f: F) -> HashMap<TypeId, AllocationStats>
    where
        F: Fn(&AllocationStats) -> AllocationStats,
    {
        self.allocations.iter().map(|(k, v)| (*k, f(v))).collect()
    }

    /// Calculates total memory efficiency score
    pub fn efficiency_score(&self) -> f64 {
        let fragmentation_score = 1.0 - self.fragmentation_ratio;
        let cache_score = self.cache_efficiency;

        // Weighted average: cache efficiency is more important
        (fragmentation_score * 0.3) + (cache_score * 0.7)
    }

    /// Gets total allocations across all types
    pub fn total_allocations(&self) -> usize {
        self.allocations.values().map(|stats| stats.count).sum()
    }

    /// Gets total memory usage across all types
    pub fn total_memory_usage(&self) -> usize {
        self.allocations
            .values()
            .map(|stats| stats.memory_usage)
            .sum()
    }
}

pub struct MemoryManager<T> {
    allocation_strategy: AllocationStrategy,
    node_pool: Arc<Mutex<ObjectPool<Node<T>>>>,
    chunk_pool: Arc<Mutex<ObjectPool<Chunk<T>>>>,
    node_allocations: Arc<AtomicUsize>,
    chunk_allocations: Arc<AtomicUsize>,
    node_pool_hits: Arc<AtomicUsize>,
    chunk_pool_hits: Arc<AtomicUsize>,
}

impl<T> MemoryManager<T> {
    #[inline(always)]
    /// Creates a new `MemoryManager` instance.
    pub fn new(strategy: AllocationStrategy) -> Self {
        Self {
            allocation_strategy: strategy,
            node_pool: Arc::new(Mutex::new(ObjectPool::new(DEFAULT_POOL_CAPACITY))),
            chunk_pool: Arc::new(Mutex::new(ObjectPool::new(DEFAULT_POOL_CAPACITY))),
            node_allocations: Arc::new(AtomicUsize::new(0)),
            chunk_allocations: Arc::new(AtomicUsize::new(0)),
            node_pool_hits: Arc::new(AtomicUsize::new(0)),
            chunk_pool_hits: Arc::new(AtomicUsize::new(0)),
        }
    }

    #[inline(always)]
    /// Reserves chunks in the chunk pool.
    pub fn reserve_chunks(&self, count: usize) {
        let mut pool = self.chunk_pool.lock();
        if pool.size() < count {
            pool.prefill(|| Chunk::new_with_size(ChunkSize::Small(DEFAULT_CHUNK_SIZE as u8)));
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
                if let Some(mut pooled) = pool.get() {
                    if let Some(pooled_mut) = Arc::get_mut(&mut pooled) {
                        self.node_pool_hits.fetch_add(1, Ordering::Relaxed);
                        *pooled_mut = value;
                        ManagedRef::new(pooled)
                    } else {
                        // It's shared, so we can't reuse it directly. Create new.
                        ManagedRef::new(Arc::new(value))
                    }
                } else {
                    ManagedRef::new(Arc::new(value))
                }
            },
            AllocationStrategy::Adaptive => {
                self.node_allocations.fetch_add(1, Ordering::Relaxed);
                // Adaptive strategy: decide behavior based on pool hit rate
                let stats = self.stats();
                let hit_rate = if stats.node_allocations > 0 {
                    stats.node_pool_hits as f64 / stats.node_allocations as f64
                } else {
                    0.0
                };

                if hit_rate > 0.7 {
                    let mut pool = self.node_pool.lock();
                    if let Some(mut pooled) = pool.get() {
                        if let Some(pooled_mut) = Arc::get_mut(&mut pooled) {
                            self.node_pool_hits.fetch_add(1, Ordering::Relaxed);
                            *pooled_mut = value;
                            ManagedRef::new(pooled)
                        } else {
                            ManagedRef::new(Arc::new(value))
                        }
                    } else {
                        ManagedRef::new(Arc::new(value))
                    }
                } else {
                    ManagedRef::new(Arc::new(value))
                }
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
                if let Some(mut pooled) = pool.get() {
                    if let Some(pooled_mut) = Arc::get_mut(&mut pooled) {
                        self.chunk_pool_hits.fetch_add(1, Ordering::Relaxed);
                        *pooled_mut = value;
                        ManagedRef::new(pooled)
                    } else {
                        // It's shared, so we can't reuse it directly. Create new.
                        ManagedRef::new(Arc::new(value))
                    }
                } else {
                    ManagedRef::new(Arc::new(value))
                }
            },
            AllocationStrategy::Adaptive => {
                self.chunk_allocations.fetch_add(1, Ordering::Relaxed);
                // Adaptive strategy: decide behavior based on pool hit rate
                let stats = self.stats();
                let hit_rate = if stats.chunk_allocations > 0 {
                    stats.chunk_pool_hits as f64 / stats.chunk_allocations as f64
                } else {
                    0.0
                };

                if hit_rate > 0.7 {
                    let mut pool = self.chunk_pool.lock();
                    if let Some(mut pooled) = pool.get() {
                        if let Some(pooled_mut) = Arc::get_mut(&mut pooled) {
                            self.chunk_pool_hits.fetch_add(1, Ordering::Relaxed);
                            *pooled_mut = value;
                            ManagedRef::new(pooled)
                        } else {
                            ManagedRef::new(Arc::new(value))
                        }
                    } else {
                        ManagedRef::new(Arc::new(value))
                    }
                } else {
                    ManagedRef::new(Arc::new(value))
                }
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

    /// Profiles memory operations using Functor pattern for enhanced statistics
    pub fn profile<F, R>(&self, f: F) -> (R, MemoryProfile)
    where
        F: FnOnce(&Self) -> R,
    {
        let before = self.stats();
        let start_time = std::time::Instant::now();

        let result = f(self);

        let after = self.stats();
        let duration = start_time.elapsed();

        let profile = MemoryProfile {
            allocations: self.collect_allocations(&before, &after),
            fragmentation_ratio: self.calculate_fragmentation(&after),
            cache_efficiency: self.calculate_cache_efficiency(&before, &after),
            duration,
            peak_memory_usage: after.node_allocations + after.chunk_allocations,
        };

        (result, profile)
    }

    /// Collects allocation statistics between two snapshots
    fn collect_allocations(
        &self, before: &MemoryStats, after: &MemoryStats,
    ) -> HashMap<TypeId, AllocationStats> {
        let mut allocations = HashMap::new();

        // Node allocations
        allocations.insert(
            TypeId::of::<Node<()>>(),
            AllocationStats {
                count: after.node_allocations - before.node_allocations,
                pool_hits: after.node_pool_hits - before.node_pool_hits,
                pool_misses: (after.node_allocations - before.node_allocations)
                    .saturating_sub(after.node_pool_hits - before.node_pool_hits),
                memory_usage: (after.node_allocations - before.node_allocations)
                    * std::mem::size_of::<Node<()>>(),
            },
        );

        // Chunk allocations
        allocations.insert(
            TypeId::of::<Chunk<()>>(),
            AllocationStats {
                count: after.chunk_allocations - before.chunk_allocations,
                pool_hits: after.chunk_pool_hits - before.chunk_pool_hits,
                pool_misses: (after.chunk_allocations - before.chunk_allocations)
                    .saturating_sub(after.chunk_pool_hits - before.chunk_pool_hits),
                memory_usage: (after.chunk_allocations - before.chunk_allocations)
                    * std::mem::size_of::<Chunk<()>>(),
            },
        );

        allocations
    }

    /// Calculates memory fragmentation ratio
    fn calculate_fragmentation(&self, stats: &MemoryStats) -> f64 {
        let total_capacity = stats.node_pool_capacity + stats.chunk_pool_capacity;
        let total_used = stats.node_pool_size + stats.chunk_pool_size;

        if total_capacity == 0 {
            0.0
        } else {
            1.0 - (total_used as f64 / total_capacity as f64)
        }
    }

    /// Calculates cache efficiency between two snapshots
    fn calculate_cache_efficiency(&self, before: &MemoryStats, after: &MemoryStats) -> f64 {
        let total_hits = (after.node_pool_hits - before.node_pool_hits)
            + (after.chunk_pool_hits - before.chunk_pool_hits);
        let total_allocations = (after.node_allocations - before.node_allocations)
            + (after.chunk_allocations - before.chunk_allocations);

        if total_allocations == 0 {
            1.0
        } else {
            total_hits as f64 / total_allocations as f64
        }
    }

    /// Prefill the chunk pool with empty chunks.
    pub fn prefill_chunks(&self) {
        match self.allocation_strategy {
            AllocationStrategy::Pooled => {
                let mut pool = self.chunk_pool.lock();
                pool.prefill(|| Chunk::new_with_size(ChunkSize::Small(DEFAULT_CHUNK_SIZE as u8)));
            },
            AllocationStrategy::Direct | AllocationStrategy::Adaptive => {
                // No pooling for Direct and Adaptive strategies
            },
        }
    }

    /// Create a shared reference to this memory manager for structural sharing
    pub fn share(&self) -> Self {
        Self {
            allocation_strategy: self.allocation_strategy,
            node_pool: Arc::clone(&self.node_pool),
            chunk_pool: Arc::clone(&self.chunk_pool),
            node_allocations: Arc::clone(&self.node_allocations),
            chunk_allocations: Arc::clone(&self.chunk_allocations),
            node_pool_hits: Arc::clone(&self.node_pool_hits),
            chunk_pool_hits: Arc::clone(&self.chunk_pool_hits),
        }
    }
}

impl<T> Clone for MemoryManager<T> {
    #[inline(always)]
    fn clone(&self) -> Self {
        Self {
            allocation_strategy: self.allocation_strategy,
            node_pool: Arc::clone(&self.node_pool),
            chunk_pool: Arc::clone(&self.chunk_pool),
            node_allocations: Arc::clone(&self.node_allocations),
            chunk_allocations: Arc::clone(&self.chunk_allocations),
            node_pool_hits: Arc::clone(&self.node_pool_hits),
            chunk_pool_hits: Arc::clone(&self.chunk_pool_hits),
        }
    }
}

impl<T> Default for MemoryManager<T> {
    #[inline(always)]
    fn default() -> Self {
        Self::new(AllocationStrategy::Pooled)
    }
}

impl<T> StdDebug for MemoryManager<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("MemoryManager")
            .field("allocation_strategy", &self.allocation_strategy)
            .field("stats", &self.stats())
            .finish()
    }
}

impl<T> PartialEq for MemoryManager<T> {
    #[inline(always)]
    fn eq(&self, other: &Self) -> bool {
        self.allocation_strategy == other.allocation_strategy
    }
}

impl<T> Eq for MemoryManager<T> {}

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

impl<T> MemoryManager<T> {
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
                let optimal_chunk_size = ChunkSize::optimal_for(size / 10); // Estimate average chunk size
                self.reserve_chunks(size / optimal_chunk_size.size() + 1);
            },
            (_, AccessPattern::Sequential) => {
                self.set_strategy(AllocationStrategy::Pooled);
                // Prefill the chunk pool for sequential access
                let mut pool = self.chunk_pool.lock();
                pool.prefill(|| Chunk::new_with_size(ChunkSize::Medium(64)));
            },
        }
    }
}

/// Managed reference that provides safe access to Arc-wrapped objects.
///
/// This type ensures immutability guarantees while providing efficient
/// sharing and cloning capabilities. It prevents unsafe mutations that
/// could break persistent data structure invariants.
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
