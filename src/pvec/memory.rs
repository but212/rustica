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
        index % 2 == 0
    }
    #[inline(always)]
    fn clone_box(&self) -> BoxedCachePolicy {
        Box::new(self.clone())
    }
}

pub(crate) const CHUNK_SIZE: usize = 32;
pub(crate) const CHUNK_BITS: usize = 5;

#[derive(Clone, PartialEq, Eq)]
pub(crate) struct Chunk<T> {
    elements: Vec<T>,
}

impl<T: Clone> Chunk<T> {
    #[inline(always)]
    /// Creates a new `Chunk` instance.
    pub fn new() -> Self {
        Self {
            elements: Vec::with_capacity(CHUNK_SIZE),
        }
    }

    #[inline(always)]
    /// Returns the length of the chunk.
    pub fn len(&self) -> usize {
        self.elements.len()
    }

    #[inline(always)]
    /// Checks if the chunk is full.
    pub fn is_full(&self) -> bool {
        self.elements.len() >= CHUNK_SIZE
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

impl<T: Clone> Default for Chunk<T> {
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

impl<T: Clone> FromIterator<T> for Chunk<T> {
    #[inline(always)]
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        let mut elements = Vec::with_capacity(CHUNK_SIZE);
        for item in iter.into_iter().take(CHUNK_SIZE) {
            elements.push(item);
        }
        Self { elements }
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

pub struct MemoryManager<T> {
    allocation_strategy: AllocationStrategy,
    node_pool: Arc<Mutex<ObjectPool<Node<T>>>>,
    chunk_pool: Arc<Mutex<ObjectPool<Chunk<T>>>>,
}

impl<T: Clone> MemoryManager<T> {
    #[inline(always)]
    /// Creates a new `MemoryManager` instance.
    pub fn new(strategy: AllocationStrategy) -> Self {
        Self {
            allocation_strategy: strategy,
            node_pool: Arc::new(Mutex::new(ObjectPool::new(DEFAULT_POOL_CAPACITY))),
            chunk_pool: Arc::new(Mutex::new(ObjectPool::new(DEFAULT_POOL_CAPACITY))),
        }
    }

    #[inline(always)]
    /// Reserves chunks in the chunk pool.
    pub fn reserve_chunks(&self, count: usize) {
        self.chunk_pool.lock().reserve(count);
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

    #[inline(always)]
    /// Returns memory statistics.
    pub fn stats(&self) -> MemoryStats {
        let node_pool = self.node_pool.lock();
        let chunk_pool = self.chunk_pool.lock();
        MemoryStats {
            node_pool_size: node_pool.size(),
            chunk_pool_size: chunk_pool.size(),
            node_pool_capacity: node_pool.capacity(),
            chunk_pool_capacity: chunk_pool.capacity(),
        }
    }

    #[inline(always)]
    /// Prefills the node and chunk pools.
    pub fn prefill(&self)
    where
        T: Default,
    {
        self.node_pool.lock().prefill(Node::<T>::default);
        self.chunk_pool.lock().prefill(Chunk::<T>::default);
    }
}

impl<T: Clone> Clone for MemoryManager<T> {
    #[inline(always)]
    fn clone(&self) -> Self {
        Self {
            allocation_strategy: self.allocation_strategy,
            node_pool: self.node_pool.clone(),
            chunk_pool: self.chunk_pool.clone(),
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
pub struct MemoryStats {
    pub node_pool_size: usize,
    pub node_pool_capacity: usize,
    pub chunk_pool_size: usize,
    pub chunk_pool_capacity: usize,
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
        f.debug_struct("ManagedRef").field("inner", &self.inner).finish()
    }
}

impl<T: PartialEq> PartialEq for ManagedRef<T> {
    fn eq(&self, other: &Self) -> bool {
        *self.inner == *other.inner
    }
}

impl<T: Eq> Eq for ManagedRef<T> {}

pub(crate) struct ObjectPool<T> {
    pool: VecDeque<T>,
    capacity: usize,
}

impl<T: Clone> ObjectPool<T> {
    #[inline(always)]
    /// Creates a new `ObjectPool` instance.
    pub fn new(capacity: usize) -> Self {
        let pool = VecDeque::with_capacity(capacity);
        Self { pool, capacity }
    }

    #[inline(always)]
    /// Reserves space in the pool.
    pub fn reserve(&mut self, count: usize) {
        self.pool.reserve(count);
    }

    #[inline(always)]
    /// Returns the size of the pool.
    pub fn size(&self) -> usize {
        self.pool.len()
    }

    #[inline(always)]
    /// Returns the capacity of the pool.
    pub fn capacity(&self) -> usize {
        self.pool.capacity()
    }

    #[inline(always)]
    /// Prefills the pool with objects created by the given function.
    pub fn prefill<F>(&mut self, create_fn: F)
    where
        F: Fn() -> T,
    {
        let needed = self.capacity.saturating_sub(self.pool.len());
        self.pool.reserve(needed);
        for _ in 0..needed {
            self.pool.push_back(create_fn());
        }
    }
}
