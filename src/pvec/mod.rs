//! # Persistent Vector
//!
//! A persistent vector implementation using Relaxed Radix Balanced Trees (RRB-Trees).
//!
//! This data structure provides efficient immutable operations while
//! maintaining structural sharing between versions. This makes it ideal
//! for functional programming patterns and concurrent applications where
//! immutable data structures are preferred.
//!
//! ## Key Features
//!
//! - **Immutability**: Each operation creates a new version without modifying the original
//! - **Structural Sharing**: Minimizes memory usage by sharing unmodified subtrees
//! - **Efficient Updates**: Log32 complexity for most operations
//! - **Thread Safety**: Safe for concurrent access without locks
//! - **Memory Efficiency**: Compact representation with optimizations for small vectors
//!
//! ## Performance Characteristics
//!
//! - **Access (get)**: O(log32 n) - virtually constant time for practical sizes
//! - **Insert/Update**: O(log32 n)
//! - **Push/Pop (at ends)**: O(1) amortized
//! - **Slice**: O(log32 n)
//! - **Concatenation**: O(log32 n)
//! - **Split**: O(log32 n)
//!
//! ## When to Use Persistent Vector
//!
//! Persistent vectors are ideal for:
//!
//! - Maintaining history of changes (undo/redo functionality)
//! - Concurrent programming without locks
//! - Functional programming patterns requiring immutable data
//! - Applications that need to compare or diff versions of collections
//! - Scenarios where you need to provide a snapshot of data at a point in time
//!
//! ## Basic Usage
//!
//! ```rust
//! use rustica::pvec;
//! use rustica::pvec::PersistentVector;
//!
//! // Create a new vector using the pvec! macro
//! let v1: PersistentVector<i32> = pvec![1, 2, 3, 4, 5];
//!
//! // Operations return new vectors, leaving the original unchanged
//! let v2 = v1.push_back(6);
//! let v3 = v1.update(0, 10);
//!
//! // Original vector remains unchanged
//! assert_eq!(v1.get(0), Some(&1));
//! assert_eq!(v1.len(), 5);
//!
//! // New vectors reflect the changes
//! assert_eq!(v2.len(), 6);
//! assert_eq!(v2.get(5), Some(&6));
//!
//! assert_eq!(v3.get(0), Some(&10));
//! ```
//!
//! ## Advanced Examples
//!
//! ### Structural Sharing
//!
//! ```rust
//! use rustica::pvec;
//! use rustica::pvec::PersistentVector;
//!
//! // Create a large vector
//! let mut large: PersistentVector<i32> = PersistentVector::new();
//! for i in 0..1000 {
//!     large = large.push_back(i);
//! }
//!
//! // Modify just one element
//! let modified = large.update(500, 42);
//!
//! // Most of the internal structure is shared between the two vectors
//! assert_eq!(large.get(500), Some(&500));
//! assert_eq!(modified.get(500), Some(&42));
//! ```
//!
//! ### Working with Slices and Splits
//!
//! ```rust
//! use rustica::pvec;
//! use rustica::pvec::PersistentVector;
//!
//! let vec: PersistentVector<char> = pvec!['a', 'b', 'c', 'd', 'e', 'f'];
//!
//! // Create a slice (this is a view, not a copy)
//! let slice = vec.slice(1, 4);
//! assert_eq!(slice.len(), 3);
//! assert_eq!(slice.get(0), Some(&'b'));
//! assert_eq!(slice.get(2), Some(&'d'));
//!
//! // Split a vector into two
//! let (left, right) = vec.split_at(3);
//! assert_eq!(left.len(), 3);
//! assert_eq!(right.len(), 3);
//! assert_eq!(left.get(0), Some(&'a'));
//! assert_eq!(right.get(0), Some(&'d'));
//! ```
//!
//! ### Thread-Safe Sharing with Arc
//!
//! ```rust
//! use rustica::pvec;
//! use rustica::pvec::PersistentVector;
//! use std::sync::Arc;
//! use std::thread;
//!
//! // Create a vector and convert it to Arc for thread-safe sharing
//! let vec: PersistentVector<i32> = pvec![1, 2, 3, 4, 5];
//! let arc_vec = vec.to_arc();
//!
//! // Spawn multiple threads that can safely access the same vector
//! let handles: Vec<_> = (0..3)
//!     .map(|id| {
//!         let thread_vec = arc_vec.clone();
//!         thread::spawn(move || {
//!             // Each thread can safely read from the shared vector
//!             println!("Thread {}: Element at 0: {:?}", id, thread_vec.get(0));
//!             
//!             // Create a new version without affecting other threads
//!             let modified = thread_vec.update(0, id);
//!             (id, modified.get(0).cloned())
//!         })
//!     })
//!     .collect();
//!
//! // Wait for all threads to complete
//! let results: Vec<_> = handles.into_iter().map(|h| h.join().unwrap()).collect();
//! for (id, value) in results {
//!     assert_eq!(value, Some(id));
//! }
//!
//! // Original vector is still unchanged
//! assert_eq!(arc_vec.get(0), Some(&1));
//! ```
//!
//! ## Implementation Details
//!
//! The vector uses a combination of strategies for optimal performance:
//!
//! 1. **Optimized Small Vector**: Vectors with few elements use a compact representation
//! 2. **RRB-Tree Structure**: Larger vectors use a tree with a branching factor of 32
//! 3. **Efficient Memory Management**: Uses Arc for reference counting and structural sharing
//! 4. **Path Caching**: Intelligent caching for faster sequential access
//! 5. **Chunked Storage**: Elements are stored in fixed-size chunks for better cache locality
//!
//! ## Module Structure
//!
//! This module consists of several components:
//!
//! - **vector**: The main `PersistentVector` implementation (public API)
//! - **iterator**: Various iterators for traversing the vector (public API)
//! - **memory**: Memory management with reference counting (internal implementation)
//! - **node**: Tree node implementation for the RRB-Tree (internal implementation)
//! - **tree**: Core tree implementation with balancing algorithms (internal implementation)
//! - **cache**: Path caching to accelerate repeated access patterns (internal implementation)
//! - **chunk**: Efficient storage of elements in fixed-size arrays (internal implementation)
//!
//! Note that only the vector implementation and iterators are exposed as public API,
//! while the internal implementation details are encapsulated to provide a clean
//! and stable interface.

// Submodules

/// Caching system for accelerating tree traversal paths.
#[cfg(feature = "pvec")]
pub(crate) mod cache;

/// Fixed-size chunks for storing elements efficiently.
#[cfg(feature = "pvec")]
pub(crate) mod chunk;

/// Iterators for traversing persistent vectors.
#[cfg(feature = "pvec")]
pub(crate) mod iterator;

/// Custom memory management for optimal allocation.
#[cfg(feature = "pvec")]
pub(crate) mod memory;

/// Tree node implementation for the RRB-Tree structure.
#[cfg(feature = "pvec")]
pub(crate) mod node;

/// Core tree implementation with balancing algorithms.
#[cfg(feature = "pvec")]
pub(crate) mod tree;

/// Main persistent vector implementation.
#[cfg(feature = "pvec")]
pub mod vector;

// Re-exports of primary types

/// The main persistent vector type.
#[cfg(feature = "pvec")]
pub use self::vector::PersistentVector;

/// Custom memory manager for efficient allocation.
#[cfg(feature = "pvec")]
pub use self::memory::MemoryManager;

// Iterator types
#[cfg(feature = "pvec")]
pub use self::iterator::{ChunksIter, IntoIter, Iter, SortedIter};

/// Creates a new `PersistentVector` with the provided elements.
///
/// This macro provides a convenient way to create persistent vectors,
/// similar to the standard library's `vec!` macro for `Vec`.
#[macro_export]
#[cfg(feature = "pvec")]
macro_rules! pvec {
    // Empty vector
    () => { $crate::pvec::PersistentVector::new() };

    // Vector with elements
    ($($x:expr),*) => {{
        let mut v = $crate::pvec::PersistentVector::new();
        $(
            v = v.push_back($x);
        )*
        v
    }};

    // Handle trailing comma case
    ($($x:expr,)*) => { $crate::pvec![$($x),*] };
}

// Re-export the macro at the pvec module level
pub use pvec;
