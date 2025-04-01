//! Memory Management Module
//!
//! This module provides memory management utilities for the persistent vector.
//! It includes a memory pool system that reduces allocation overhead by reusing
//! memory for commonly allocated structures.
//!
//! # Examples
//!
//! ```
//! use rustica::pvec::memory::{MemoryManager, AllocationStrategy};
//!
//! // Create a memory manager with pooled allocation
//! let manager: MemoryManager<i32> = MemoryManager::new(AllocationStrategy::Pooled);
//!
//! // Acquire a node and a chunk
//! let node = manager.acquire_node();
//! let chunk = manager.acquire_chunk();
//!
//! // Get memory statistics
//! let stats = manager.stats();
//! println!("Node pool size: {}", stats.node_pool_size);
//! ```

use std::collections::VecDeque;
use std::convert::AsRef;
use std::fmt::Debug;
use std::sync::Arc;
use parking_lot::Mutex;

use crate::pvec::chunk::Chunk;
use crate::pvec::node::Node;

/// Default capacity for memory pools
pub const DEFAULT_POOL_CAPACITY: usize = 128;

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
pub struct MemoryManager<T: Clone> {
    allocation_strategy: AllocationStrategy,
    node_pool: Arc<Mutex<ObjectPool<Node<T>>>>,
    chunk_pool: Arc<Mutex<ObjectPool<Chunk<T>>>>,
}

impl<T: Clone> MemoryManager<T> {
    /// Create a new memory manager with the given allocation strategy
    ///
    /// This initializes the memory pools with the default capacity and sets up
    /// the memory manager according to the specified allocation strategy.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::memory::{MemoryManager, AllocationStrategy};
    ///
    /// // Create a memory manager with pooled allocation
    /// let manager: MemoryManager<i32> = MemoryManager::new(AllocationStrategy::Pooled);
    ///
    /// // Create a memory manager with direct allocation (no pooling)
    /// let direct_manager: MemoryManager<String> = MemoryManager::new(AllocationStrategy::Direct);
    /// ```
    pub fn new(strategy: AllocationStrategy) -> Self {
        Self {
            allocation_strategy: strategy,
            node_pool: Arc::new(Mutex::new(ObjectPool::new(DEFAULT_POOL_CAPACITY))),
            chunk_pool: Arc::new(Mutex::new(ObjectPool::new(DEFAULT_POOL_CAPACITY))),
        }
    }

    /// Acquire a new node from the pool or allocate one
    ///
    /// This method retrieves a node from the memory pool if available,
    /// otherwise allocates a new node. The returned node is wrapped in a
    /// `ManagedRef` which ensures proper reference counting and deallocation.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::memory::MemoryManager;
    ///
    /// let manager: MemoryManager<i32> = MemoryManager::default();
    ///
    /// // Acquire a new node
    /// let node = manager.acquire_node();
    /// ```
    pub fn acquire_node(&self) -> ManagedRef<Node<T>> {
        match self.allocation_strategy {
            AllocationStrategy::Direct => ManagedRef::new(Arc::new(Node::new()), None),
            _ => {
                let mut pool = self.node_pool.lock();
                if let Some(node) = pool.acquire() {
                    ManagedRef::new(node, Some(self.node_pool.clone()))
                } else {
                    ManagedRef::new(Arc::new(Node::new()), Some(self.node_pool.clone()))
                }
            }
        }
    }

    /// Acquire a new chunk from the pool or allocate one
    ///
    /// This method retrieves a chunk from the memory pool if available,
    /// otherwise allocates a new chunk. The returned chunk is wrapped in a
    /// `ManagedRef` which ensures proper reference counting and deallocation.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::memory::MemoryManager;
    ///
    /// let manager: MemoryManager<i32> = MemoryManager::default();
    ///
    /// // Acquire a new chunk
    /// let chunk = manager.acquire_chunk();
    /// ```
    pub fn acquire_chunk(&self) -> ManagedRef<Chunk<T>> {
        match self.allocation_strategy {
            AllocationStrategy::Direct => ManagedRef::new(Arc::new(Chunk::new()), None),
            _ => {
                let mut pool = self.chunk_pool.lock();
                if let Some(chunk) = pool.acquire() {
                    ManagedRef::new(chunk, Some(self.chunk_pool.clone()))
                } else {
                    ManagedRef::new(Arc::new(Chunk::new()), Some(self.chunk_pool.clone()))
                }
            }
        }
    }

    /// Get the current allocation strategy
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::memory::{MemoryManager, AllocationStrategy};
    ///
    /// let manager: MemoryManager<i32> = MemoryManager::default();
    ///
    /// // Get the current allocation strategy
    /// let strategy = manager.strategy();
    /// ```
    pub fn strategy(&self) -> AllocationStrategy {
        self.allocation_strategy
    }

    /// Change the allocation strategy
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::memory::{MemoryManager, AllocationStrategy};
    ///
    /// let mut manager: MemoryManager<i32> = MemoryManager::default();
    ///
    /// // Change the allocation strategy
    /// manager.set_strategy(AllocationStrategy::Direct);
    /// ```
    pub fn set_strategy(&mut self, strategy: AllocationStrategy) {
        self.allocation_strategy = strategy;
    }

    /// Get statistics about memory usage
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::memory::MemoryManager;
    ///
    /// let manager: MemoryManager<i32> = MemoryManager::default();
    ///
    /// // Get memory statistics
    /// let stats = manager.stats();
    /// ```
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
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::memory::MemoryManager;
    ///
    /// let manager: MemoryManager<i32> = MemoryManager::default();
    ///
    /// // Pre-allocate objects in the pools
    /// manager.prefill();
    /// ```
    pub fn prefill(&self) {
        if self.allocation_strategy == AllocationStrategy::Direct {
            return;
        }

        let mut node_pool = self.node_pool.lock();
        let mut chunk_pool = self.chunk_pool.lock();

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

impl<T: Clone> Default for MemoryManager<T> {
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

/// Statistics about memory usage in the memory pools
///
/// This struct provides information about the current state of memory pools
/// including their sizes (current number of objects) and capacities (maximum
/// number of objects they can hold).
#[derive(Debug, Clone, Copy)]
pub struct MemoryStats {
    /// Number of nodes currently available in the node pool
    pub node_pool_size: usize,
    /// Number of chunks currently available in the chunk pool
    pub chunk_pool_size: usize,
    /// Maximum capacity of the node pool
    pub node_pool_capacity: usize,
    /// Maximum capacity of the chunk pool
    pub chunk_pool_capacity: usize,
}

/// A reference-counted object that can be returned to a pool when dropped
///
/// This struct wraps an `Arc<T>` and optionally associates it with an object pool.
/// When the `ManagedRef` is dropped and it's the last reference to the inner value,
/// the object is returned to the pool (if a pool is specified) rather than being deallocated.
///
/// # Type Parameters
///
/// * `T`: The type of the managed object, which must implement `Clone`
pub struct ManagedRef<T: Clone> {
    inner: Arc<T>,
    pool: Option<Arc<Mutex<ObjectPool<T>>>>,
}

impl<T: Clone> ManagedRef<T> {
    /// Create a new managed reference
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::memory::ManagedRef;
    /// use std::sync::Arc;
    ///
    /// let obj = Arc::new(42);
    ///
    /// // Create a managed reference
    /// let ref1 = ManagedRef::new(obj.clone(), None);
    /// ```
    pub fn new(obj: Arc<T>, pool: Option<Arc<Mutex<ObjectPool<T>>>>) -> Self {
        Self { inner: obj, pool }
    }

    /// Converts this managed reference to an Arc<T> by cloning the inner reference
    ///
    /// This method creates a new strong reference to the inner data without
    /// affecting the reference counting of the managed reference itself.
    ///
    /// # Returns
    ///
    /// A new Arc<T> pointing to the same data as this managed reference
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::memory::ManagedRef;
    /// use std::sync::Arc;
    ///
    /// let obj = Arc::new(42);
    /// let managed = ManagedRef::new(obj, None);
    /// let arc = managed.to_arc();
    ///
    /// assert_eq!(*arc, 42);
    /// ```
    pub fn to_arc(&self) -> Arc<T> {
        self.inner.clone()
    }

    /// Checks if this reference is unique (not shared)
    ///
    /// # Returns
    ///
    /// `true` if the reference is unique, `false` otherwise
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::memory::ManagedRef;
    /// use std::sync::Arc;
    ///
    /// let obj = Arc::new(42);
    /// let managed = ManagedRef::new(obj, None);
    ///
    /// assert!(managed.is_unique());
    /// ```
    pub fn is_unique(&self) -> bool {
        Arc::strong_count(&self.inner) == 1
    }

    /// Attempt to get a mutable reference to the inner object
    ///
    /// Returns None if the reference is shared
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::memory::ManagedRef;
    /// use std::sync::Arc;
    ///
    /// let obj = Arc::new(42);
    /// let mut managed = ManagedRef::new(obj, None);
    ///
    /// assert!(managed.get_mut().is_some());
    /// ```
    pub fn get_mut(&mut self) -> Option<&mut T> {
        Arc::get_mut(&mut self.inner)
    }

    /// Get a mutable reference to the inner object, cloning it if necessary
    ///
    /// Returns a new ManagedRef if the object was cloned
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::memory::ManagedRef;
    /// use std::sync::Arc;
    ///
    /// let obj = Arc::new(42);
    /// let mut managed = ManagedRef::new(obj, None);
    ///
    /// assert!(managed.make_mut().is_ok());
    /// ```
    pub fn make_mut(&mut self) -> Result<&mut T, Self> {
        if self.is_unique() {
            Ok(Arc::get_mut(&mut self.inner).unwrap())
        } else {
            // We need to clone the inner object
            let cloned = match &self.pool {
                Some(pool) => {
                    let mut pool_guard = pool.lock();
                    if let Some(obj) = pool_guard.acquire() {
                        // If the pool had an unused object, use that
                        obj
                    } else {
                        // Otherwise allocate a new one
                        Arc::new(T::clone(&*self.inner))
                    }
                }
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

impl<T: Clone> AsRef<T> for ManagedRef<T> {
    fn as_ref(&self) -> &T {
        &self.inner
    }
}

impl<T: Clone> Drop for ManagedRef<T> {
    fn drop(&mut self) {
        // If this is the last reference and we have a pool, return the object to the pool
        if Arc::strong_count(&self.inner) == 1 {
            if let Some(pool) = &self.pool {
                let mut pool_guard = pool.lock();
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
///
/// # Examples
///
/// ```
/// use rustica::pvec::memory::ObjectPool;
/// use std::sync::Arc;
///
/// let mut pool: ObjectPool<Arc<i32>> = ObjectPool::new(10);
///
/// // Acquire an object from the pool or create a new one if empty
/// let obj = pool.acquire_or_create(|| Arc::new(42.into()));
///
/// // Release the object back to the pool
/// pool.release(obj);
/// ```
pub struct ObjectPool<T> {
    objects: VecDeque<Arc<T>>,
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
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::memory::ObjectPool;
    /// use std::sync::Arc;
    ///
    /// // Create a pool that can hold up to 32 objects
    /// let pool: ObjectPool<Arc<i32>> = ObjectPool::new(32);
    /// assert_eq!(pool.size(), 0);
    /// assert_eq!(pool.capacity(), 32);
    /// ```
    pub fn new(capacity: usize) -> Self {
        Self {
            objects: VecDeque::with_capacity(capacity),
            capacity,
        }
    }

    /// Acquire an object from the pool
    ///
    /// This returns an object from the pool if available, otherwise returns `None`.
    ///
    /// # Returns
    ///
    /// * `Option<Arc<T>>`: An object from the pool, or `None` if the pool is empty
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::memory::ObjectPool;
    /// use std::sync::Arc;
    ///
    /// // Create a pool with 2 objects
    /// let mut pool: ObjectPool<Arc<i32>> = ObjectPool::new(2);
    /// pool.prefill(|i| Arc::new(42.into()));
    ///
    /// // Acquire objects from the pool
    /// let obj1 = pool.acquire();
    /// let obj2 = pool.acquire();
    /// let obj3 = pool.acquire();
    ///
    /// // Check the results
    /// assert_eq!(obj1.is_some(), true);
    /// assert_eq!(obj2.is_some(), true);
    /// assert_eq!(obj3.is_some(), false);
    /// ```
    pub fn acquire(&mut self) -> Option<Arc<T>> {
        self.objects.pop_front()
    }

    /// Acquire an object from the pool, or create a new one if the pool is empty
    ///
    /// This returns an object from the pool if available, otherwise creates a new
    /// object using the provided `create_fn` and returns it.
    ///
    /// # Parameters
    ///
    /// * `create_fn`: A function that creates a new object of type `T`
    ///
    /// # Returns
    ///
    /// * `Arc<T>`: An object from the pool or a newly created object
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::memory::ObjectPool;
    /// use std::sync::Arc;
    ///
    /// // Create a pool with 2 objects
    /// let mut pool: ObjectPool<Arc<i32>> = ObjectPool::new(2);
    /// pool.prefill(|i| Arc::new((i as i32).into()));
    ///
    /// // Acquire objects from the pool
    /// let obj1 = pool.acquire_or_create(|| Arc::new(42.into()));
    /// let obj2 = pool.acquire_or_create(|| Arc::new(43.into()));
    /// let obj3 = pool.acquire_or_create(|| Arc::new(44.into()));
    ///
    /// // Check the results
    /// assert_eq!(*obj1, 0.into());
    /// assert_eq!(*obj2, 1.into());
    /// assert_eq!(*obj3, 44.into());
    /// ```
    pub fn acquire_or_create<F>(&mut self, create_fn: F) -> Arc<T>
    where
        F: FnOnce() -> Arc<T>,
    {
        self.acquire().unwrap_or_else(create_fn)
    }

    /// Release an object back to the pool
    ///
    /// This returns an object to the pool if the pool has available space.
    /// If the pool is at capacity, the object will be dropped instead.
    ///
    /// # Parameters
    ///
    /// * `obj`: The object to release back to the pool
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::memory::ObjectPool;
    /// use std::sync::Arc;
    ///
    /// // Create a pool with 2 objects
    /// let mut pool: ObjectPool<Arc<i32>> = ObjectPool::new(2);
    /// pool.prefill(|i| Arc::new((i as i32).into()));
    ///
    /// // Acquire and release objects
    /// let obj1 = pool.acquire();
    /// let obj2 = pool.acquire();
    ///
    /// // Release objects back to the pool
    /// pool.release(obj1.unwrap());
    /// pool.release(obj2.unwrap());
    ///
    /// // Check the results
    /// assert_eq!(pool.size(), 2);
    /// assert_eq!(pool.capacity(), 2);
    /// ```
    pub fn release(&mut self, obj: Arc<T>) {
        if self.objects.len() < self.capacity {
            self.objects.push_back(obj);
        }
        // If we're at capacity, the object will be dropped
    }

    /// Get the current size of the pool
    ///
    /// This returns the number of objects currently in the pool.
    ///
    /// # Returns
    ///
    /// * `usize`: The number of objects in the pool
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::memory::ObjectPool;
    /// use std::sync::Arc;
    ///
    /// // Create a pool with 2 objects
    /// let mut pool: ObjectPool<Arc<i32>> = ObjectPool::new(2);
    /// pool.prefill(|i| Arc::new((i as i32).into()));
    ///
    /// // Check the size of the pool
    /// assert_eq!(pool.size(), 2);
    /// ```
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
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::memory::ObjectPool;
    /// use std::sync::Arc;
    ///
    /// // Create a pool with a capacity of 2 objects
    /// let pool: ObjectPool<Arc<i32>> = ObjectPool::new(2);
    ///
    /// // Check the capacity of the pool
    /// assert_eq!(pool.capacity(), 2);
    /// ```
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
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::memory::ObjectPool;
    /// use std::sync::Arc;
    ///
    /// // Create a pool with a capacity of 2 objects
    /// let mut pool: ObjectPool<Arc<i32>> = ObjectPool::new(2);
    ///
    /// // Pre-fill the pool with objects
    /// pool.prefill(|i| Arc::new((i as i32).into()));
    ///
    /// // Check the size of the pool
    /// assert_eq!(pool.size(), 2);
    /// ```
    pub fn prefill<F>(&mut self, create_fn: F)
    where
        F: Fn(usize) -> Arc<T>,
    {
        for i in self.objects.len()..self.capacity {
            self.objects.push_back(create_fn(i));
        }
    }
}
