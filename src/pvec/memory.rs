//! Memory Management Module
//!
//! This module provides memory management utilities for the persistent vector.
//! It includes a memory pool system that reduces allocation overhead by reusing
//! memory for commonly allocated structures.

use std::sync::Arc;
use std::sync::Mutex;
use std::collections::VecDeque;
use std::fmt::Debug;

use crate::pvec::chunk::Chunk;
use crate::pvec::node::Node;

/// Default capacity for memory pools
pub const DEFAULT_POOL_CAPACITY: usize = 128;

/// Strategy for allocating and recycling memory
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
pub struct MemoryManager<T: Clone> {
    allocation_strategy: AllocationStrategy,
    node_pool: Arc<Mutex<ObjectPool<Node<T>>>>,
    chunk_pool: Arc<Mutex<ObjectPool<Chunk<T>>>>,
}

impl<T: Clone> MemoryManager<T> {
    /// Create a new memory manager with the given allocation strategy
    pub fn new(strategy: AllocationStrategy) -> Self {
        Self {
            allocation_strategy: strategy,
            node_pool: Arc::new(Mutex::new(ObjectPool::new(DEFAULT_POOL_CAPACITY))),
            chunk_pool: Arc::new(Mutex::new(ObjectPool::new(DEFAULT_POOL_CAPACITY))),
        }
    }
    
    /// Create a new memory manager with default settings (Pooled allocation)
    pub fn default() -> Self {
        Self::new(AllocationStrategy::Pooled)
    }
    
    /// Acquire a new node from the pool or allocate one
    pub fn acquire_node(&self) -> ManagedRef<Node<T>> {
        match self.allocation_strategy {
            AllocationStrategy::Direct => {
                ManagedRef::new(Arc::new(Node::new()), None)
            },
            _ => {
                let mut pool = self.node_pool.lock().unwrap();
                if let Some(node) = pool.acquire() {
                    ManagedRef::new(node, Some(self.node_pool.clone()))
                } else {
                    ManagedRef::new(Arc::new(Node::new()), Some(self.node_pool.clone()))
                }
            }
        }
    }
    
    /// Acquire a new chunk from the pool or allocate one
    pub fn acquire_chunk(&self) -> ManagedRef<Chunk<T>> {
        match self.allocation_strategy {
            AllocationStrategy::Direct => {
                ManagedRef::new(Arc::new(Chunk::new()), None)
            },
            _ => {
                let mut pool = self.chunk_pool.lock().unwrap();
                if let Some(chunk) = pool.acquire() {
                    ManagedRef::new(chunk, Some(self.chunk_pool.clone()))
                } else {
                    ManagedRef::new(Arc::new(Chunk::new()), Some(self.chunk_pool.clone()))
                }
            }
        }
    }
    
    /// Get the current allocation strategy
    pub fn strategy(&self) -> AllocationStrategy {
        self.allocation_strategy
    }
    
    /// Change the allocation strategy
    pub fn set_strategy(&mut self, strategy: AllocationStrategy) {
        self.allocation_strategy = strategy;
    }
    
    /// Get statistics about memory usage
    pub fn stats(&self) -> MemoryStats {
        let node_pool = self.node_pool.lock().unwrap();
        let chunk_pool = self.chunk_pool.lock().unwrap();
        
        MemoryStats {
            node_pool_size: node_pool.size(),
            chunk_pool_size: chunk_pool.size(),
            node_pool_capacity: node_pool.capacity(),
            chunk_pool_capacity: chunk_pool.capacity(),
        }
    }
    
    /// Pre-allocate objects in the pools
    pub fn prefill(&self) {
        if self.allocation_strategy == AllocationStrategy::Direct {
            return;
        }
        
        let mut node_pool = self.node_pool.lock().unwrap();
        let mut chunk_pool = self.chunk_pool.lock().unwrap();
        
        node_pool.prefill(|_| Arc::new(Node::new()));
        chunk_pool.prefill(|_| Arc::new(Chunk::new()));
    }
}

impl<T: Clone> Clone for MemoryManager<T> {
    fn clone(&self) -> Self {
        Self {
            allocation_strategy: self.allocation_strategy,
            node_pool: self.node_pool.clone(),
            chunk_pool: self.chunk_pool.clone(),
        }
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

/// Statistics about memory usage in the pools
#[derive(Debug, Clone, Copy)]
pub struct MemoryStats {
    /// Number of nodes in the node pool
    pub node_pool_size: usize,
    /// Number of chunks in the chunk pool
    pub chunk_pool_size: usize,
    /// Capacity of the node pool
    pub node_pool_capacity: usize,
    /// Capacity of the chunk pool
    pub chunk_pool_capacity: usize,
}

/// A reference-counted object that can be returned to a pool when dropped
pub struct ManagedRef<T: Clone> {
    inner: Arc<T>,
    pool: Option<Arc<Mutex<ObjectPool<T>>>>,
}

impl<T: Clone> ManagedRef<T> {
    /// Create a new managed reference
    pub(crate) fn new(obj: Arc<T>, pool: Option<Arc<Mutex<ObjectPool<T>>>>) -> Self {
        Self { inner: obj, pool }
    }
    
    /// Get a reference to the inner object
    pub fn as_ref(&self) -> &T {
        &self.inner
    }
    
    /// Convert to an Arc by cloning the inner reference
    pub fn to_arc(&self) -> Arc<T> {
        self.inner.clone()
    }
    
    /// Check if this reference is unique (not shared)
    pub fn is_unique(&self) -> bool {
        Arc::strong_count(&self.inner) == 1
    }
    
    /// Attempt to get a mutable reference to the inner object
    ///
    /// Returns None if the reference is shared
    pub fn get_mut(&mut self) -> Option<&mut T> {
        Arc::get_mut(&mut self.inner)
    }
    
    /// Get a mutable reference to the inner object, cloning it if necessary
    ///
    /// Returns a new ManagedRef if the object was cloned
    pub fn make_mut(&mut self) -> Result<&mut T, Self> {
        if self.is_unique() {
            Ok(Arc::get_mut(&mut self.inner).unwrap())
        } else {
            // We need to clone the inner object
            let cloned = match &self.pool {
                Some(pool) => {
                    let mut pool_guard = pool.lock().unwrap();
                    if let Some(obj) = pool_guard.acquire() {
                        // If the pool had an unused object, use that
                        obj
                    } else {
                        // Otherwise allocate a new one
                        Arc::new(T::clone(&*self.inner))
                    }
                },
                None => Arc::new(T::clone(&*self.inner)),
            };
            
            let new_ref = Self {
                inner: cloned,
                pool: self.pool.clone(),
            };
            
            Err(new_ref)
        }
    }
}

impl<T: Clone> Clone for ManagedRef<T> {
    fn clone(&self) -> Self {
        Self {
            inner: self.inner.clone(),
            pool: self.pool.clone(),
        }
    }
}

impl<T: Clone> Drop for ManagedRef<T> {
    fn drop(&mut self) {
        // If this is the last reference and we have a pool, return the object to the pool
        if Arc::strong_count(&self.inner) == 1 {
            if let Some(pool) = &self.pool {
                let mut pool_guard = pool.lock().unwrap();
                // Create a clone of the inner value for the pool
                let inner = self.inner.clone();
                pool_guard.release(inner);
            }
        }
    }
}

impl<T: Clone + Debug> Debug for ManagedRef<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("ManagedRef")
            .field("inner", &self.inner)
            .field("has_pool", &self.pool.is_some())
            .finish()
    }
}

impl<T: Clone> std::ops::Deref for ManagedRef<T> {
    type Target = T;
    
    fn deref(&self) -> &Self::Target {
        &self.inner
    }
}

/// A pool of reusable objects
pub(crate) struct ObjectPool<T> {
    objects: VecDeque<Arc<T>>,
    capacity: usize,
}

impl<T: Clone> ObjectPool<T> {
    /// Create a new object pool with the given capacity
    fn new(capacity: usize) -> Self {
        Self {
            objects: VecDeque::with_capacity(capacity),
            capacity,
        }
    }
    
    /// Acquire an object from the pool
    fn acquire(&mut self) -> Option<Arc<T>> {
        self.objects.pop_front()
    }
    
    /// Release an object back to the pool
    fn release(&mut self, obj: Arc<T>) {
        if self.objects.len() < self.capacity {
            self.objects.push_back(obj);
        }
        // If we're at capacity, the object will be dropped
    }
    
    /// Get the current size of the pool
    fn size(&self) -> usize {
        self.objects.len()
    }
    
    /// Get the capacity of the pool
    fn capacity(&self) -> usize {
        self.capacity
    }
    
    /// Pre-fill the pool with new objects
    fn prefill<F>(&mut self, create_fn: F)
    where
        F: Fn(usize) -> Arc<T>
    {
        for i in self.objects.len()..self.capacity {
            self.objects.push_back(create_fn(i));
        }
    }
}