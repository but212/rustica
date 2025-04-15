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
/// The memory manager provides efficient memory reuse through pooling,
/// which reduces allocation overhead in operations that frequently
/// create and discard nodes and chunks. It supports different allocation
/// strategies to optimize for specific workloads.
pub struct MemoryManager<T> {
    allocation_strategy: AllocationStrategy,
    node_pool: Arc<Mutex<ObjectPool<Node<T>>>>,
    chunk_pool: Arc<Mutex<ObjectPool<Chunk<T>>>>,
}

impl<T: Clone> MemoryManager<T> {
    /// Create a new memory manager with the given allocation strategy
    ///
    /// This initializes the memory pools with the default capacity and sets up
    /// the memory manager according to the specified allocation strategy.
    pub fn new(strategy: AllocationStrategy) -> Self {
        Self {
            allocation_strategy: strategy,
            node_pool: Arc::new(Mutex::new(ObjectPool::new(DEFAULT_POOL_CAPACITY))),
            chunk_pool: Arc::new(Mutex::new(ObjectPool::new(DEFAULT_POOL_CAPACITY))),
        }
    }

    /// Reserve capacity for at least `count` additional chunks
    ///
    /// This ensures that the chunk pool can hold at least `count` more chunks without
    /// reallocating its internal storage.
    #[inline]
    pub fn reserve_chunks(&self, count: usize) {
        self.chunk_pool.lock().reserve(count);
    }

    /// Get the current allocation strategy
    #[inline]
    pub fn strategy(&self) -> AllocationStrategy {
        self.allocation_strategy
    }

    /// Change the allocation strategy
    #[inline]
    pub fn set_strategy(&mut self, strategy: AllocationStrategy) {
        self.allocation_strategy = strategy;
    }

    /// Get statistics about memory usage
    #[inline]
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
    pub fn prefill(&self) {
        let mut node_pool = self.node_pool.lock();
        let mut chunk_pool = self.chunk_pool.lock();

        node_pool.prefill(|_| Node::new());
        chunk_pool.prefill(|_| Chunk::new());
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
    #[inline]
    pub fn new(obj: Arc<T>) -> Self {
        Self { inner: obj }
    }

    /// Get the underlying Arc<T>
    #[inline]
    pub fn inner(&self) -> &Arc<T> {
        &self.inner
    }
}

impl<T> Clone for ManagedRef<T> {
    #[inline]
    fn clone(&self) -> Self {
        Self {
            inner: self.inner.clone(),
        }
    }
}

impl<T> AsRef<T> for ManagedRef<T> {
    #[inline]
    fn as_ref(&self) -> &T {
        self.inner.as_ref()
    }
}

impl<T> std::ops::Deref for ManagedRef<T> {
    type Target = T;

    #[inline]
    fn deref(&self) -> &Self::Target {
        self.inner.as_ref()
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
    objects: VecDeque<T>,
    /// The maximum number of objects the pool can hold
    capacity: usize,
}

impl<T: Clone> ObjectPool<T> {
    /// Create a new object pool with the given capacity
    ///
    /// This initializes an empty pool that can hold up to `capacity` objects.
    /// The pool starts with no objects but has pre-allocated space to avoid
    /// reallocations when objects are added later.
    ///
    /// # Parameters
    ///
    /// * `capacity`: The maximum number of objects the pool can hold
    #[inline]
    pub fn new(capacity: usize) -> Self {
        Self {
            objects: VecDeque::with_capacity(capacity),
            capacity,
        }
    }

    /// Reserves capacity for at least `count` additional objects
    ///
    /// This ensures that the pool can hold at least `count` more objects without
    /// reallocating its internal storage.
    ///
    /// # Parameters
    ///
    /// * `count`: The number of additional objects to reserve space for
    #[inline]
    pub fn reserve(&mut self, count: usize) {
        self.objects.reserve(count);
    }

    /// Get the current size of the pool
    ///
    /// This returns the number of objects currently in the pool.
    ///
    /// # Returns
    ///
    /// * `usize`: The number of objects in the pool
    #[inline]
    pub fn size(&self) -> usize {
        self.objects.len()
    }

    /// Get the capacity of the pool
    ///
    /// This returns the maximum number of objects the pool can hold.
    ///
    /// # Returns
    ///
    /// * `usize`: The capacity of the pool
    #[inline]
    pub fn capacity(&self) -> usize {
        self.capacity
    }

    /// Pre-fill the pool with new objects
    ///
    /// This populates the pool with new objects created by the provided `create_fn`.
    /// The objects are added to the end of the pool.
    ///
    /// # Parameters
    ///
    /// * `create_fn`: A function that creates a new object of type `T`
    #[inline]
    pub fn prefill<F>(&mut self, create_fn: F)
    where
        F: Fn(usize) -> T,
    {
        for i in self.objects.len()..self.capacity {
            self.objects.push_back(create_fn(i));
        }
    }
}
