//! Memory Management Module
//!
//! This module provides memory management utilities for the persistent vector.
//! It includes a memory pool system that reduces allocation overhead by reusing
//! memory for commonly allocated structures.

use parking_lot::Mutex;
use std::collections::VecDeque;
use std::convert::AsRef;
use std::fmt::Debug;
use std::sync::Arc;

use crate::pvec::chunk::Chunk;
use crate::pvec::node::Node;

/// Default capacity for memory pools
pub(crate) const DEFAULT_POOL_CAPACITY: usize = 128;

/// Strategy for allocating and recycling memory
///
/// Controls how memory is allocated and recycled for persistent vector operations:
/// - `Direct`: No pooling, standard allocation/deallocation
/// - `Pooled`: Fixed-size memory pools for efficient reuse
/// - `Adaptive`: Dynamic memory pools that can grow based on demand
#[derive(Debug, Clone, Copy, PartialEq)]
pub enum AllocationStrategy {
    /// No pooling, allocate and free directly
    Direct,

    /// Use memory pools with a fixed capacity
    Pooled,

    /// Use memory pools but allow them to grow beyond capacity
    Adaptive,
}

/// A memory manager that handles allocation and deallocation of resources
/// for the persistent vector.
///
/// Thread-safe and optimized for concurrent, low-latency access.
#[derive()] // marker for future extension
pub struct MemoryManager<T> {
    allocation_strategy: AllocationStrategy,
    node_pool: Arc<Mutex<ObjectPool<Node<T>>>>,
    chunk_pool: Arc<Mutex<ObjectPool<Chunk<T>>>>,
}

impl<T: Clone> MemoryManager<T> {
    /// Create a new memory manager with the given allocation strategy
    #[inline]
    pub fn new(strategy: AllocationStrategy) -> Self {
        Self {
            allocation_strategy: strategy,
            node_pool: Arc::new(Mutex::new(ObjectPool::new(DEFAULT_POOL_CAPACITY))),
            chunk_pool: Arc::new(Mutex::new(ObjectPool::new(DEFAULT_POOL_CAPACITY))),
        }
    }

    /// Reserve capacity for at least `count` additional chunks
    #[inline]
    pub fn reserve_chunks(&self, count: usize) {
        self.chunk_pool.lock().reserve(count);
    }

    /// Get the current allocation strategy
    #[inline(always)]
    pub fn strategy(&self) -> AllocationStrategy {
        self.allocation_strategy
    }

    /// Change the allocation strategy
    #[inline(always)]
    pub fn set_strategy(&mut self, strategy: AllocationStrategy) {
        self.allocation_strategy = strategy;
    }

    /// Get statistics about memory usage
    #[inline(always)]
    #[must_use]
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

    /// Pre-allocate objects in the pools
    #[inline]
    pub fn prefill(&self)
    where
        T: Default,
    {
        self.node_pool.lock().prefill(Node::<T>::default);
        self.chunk_pool.lock().prefill(Chunk::<T>::default);
    }
}

impl<T: Clone> Clone for MemoryManager<T> {
    #[inline]
    fn clone(&self) -> Self {
        Self {
            allocation_strategy: self.allocation_strategy,
            node_pool: self.node_pool.clone(),
            chunk_pool: self.chunk_pool.clone(),
        }
    }
}

impl<T: Clone> Default for MemoryManager<T> {
    #[inline]
    fn default() -> Self {
        Self::new(AllocationStrategy::Pooled)
    }
}

impl<T: Clone + Debug> Debug for MemoryManager<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("MemoryManager")
            .field("allocation_strategy", &self.allocation_strategy)
            .field("stats", &self.stats())
            .finish()
    }
}

impl<T: Clone> PartialEq for MemoryManager<T> {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        // Only compare the allocation strategy as the pools are implementation details
        self.allocation_strategy == other.allocation_strategy
    }
}

impl<T: Clone> Eq for MemoryManager<T> {}

/// Statistics about memory usage in the memory pools
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct MemoryStats {
    /// Number of nodes currently in the node pool
    pub node_pool_size: usize,
    /// Maximum capacity of the node pool
    pub node_pool_capacity: usize,
    /// Number of chunks currently in the chunk pool
    pub chunk_pool_size: usize,
    /// Maximum capacity of the chunk pool
    pub chunk_pool_capacity: usize,
}

/// A reference-counted object that can be returned to a pool when dropped
///
/// This struct wraps an `Arc<T>` and does not attempt to pool or recycle memory.
/// All pooling fields and logic are removed for simplicity and safety.
pub(crate) struct ManagedRef<T> {
    /// The underlying reference-counted object
    inner: Arc<T>,
}

impl<T> ManagedRef<T> {
    /// Create a new managed reference
    #[inline(always)]
    pub fn new(obj: Arc<T>) -> Self {
        Self { inner: obj }
    }

    /// Get the underlying Arc<T>
    #[inline(always)]
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

impl<T: Debug> Debug for ManagedRef<T> {
    #[inline]
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("ManagedRef").field("inner", &self.inner).finish()
    }
}

impl<T: PartialEq> PartialEq for ManagedRef<T> {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        // Compare only the inner values
        *self.inner == *other.inner
    }
}

impl<T: Eq> Eq for ManagedRef<T> {}

/// A pool of reusable objects that helps reduce allocation overhead
///
/// This pool maintains a collection of pre-allocated objects that can be
/// reused across operations, reducing the need for frequent allocations
/// and deallocations. When objects are no longer needed, they can be
/// returned to the pool instead of being dropped.
///
/// # Type Parameters
///
/// * `T`: The type of objects stored in the pool, which must be clonable
pub(crate) struct ObjectPool<T> {
    /// The objects currently in the pool
    pool: VecDeque<T>,
    /// The maximum number of objects the pool can hold
    capacity: usize,
}

impl<T: Clone> ObjectPool<T> {
    /// Create a new object pool with the given capacity
    #[inline(always)]
    pub fn new(capacity: usize) -> Self {
        let pool = VecDeque::with_capacity(capacity);
        Self { pool, capacity }
    }

    /// Reserves capacity for at least `count` additional objects
    #[inline(always)]
    pub fn reserve(&mut self, count: usize) {
        self.pool.reserve(count);
    }

    /// Get the current size of the pool
    #[inline(always)]
    pub fn size(&self) -> usize {
        self.pool.len()
    }

    /// Get the capacity of the pool
    #[inline(always)]
    pub fn capacity(&self) -> usize {
        self.pool.capacity()
    }

    /// Pre-fill the pool with new objects
    #[inline]
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
