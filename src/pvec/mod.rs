//! Persistent vector implementation using RRB (Relaxed Radix Balanced) trees.
//!
//! This module provides a persistent, immutable vector data structure that supports
//! efficient operations for insertion, deletion, and random access. The implementation
//! uses RRB trees which maintain logarithmic performance characteristics while
//! supporting efficient concatenation and splitting operations.
//!
//! # Key Features
//!
//! - **Persistence**: All operations return new vectors, leaving the original unchanged
//! - **Structural Sharing**: Modified vectors share structure with originals, minimizing memory usage
//! - **Adaptive Storage**: Small vectors (≤64 elements) use inline storage for optimal performance
//! - **Efficient Operations**: O(log n) for most operations including random access, update, and split
//!
//! # When to Use
//!
//! Use `PersistentVector` when you need:
//! - Immutable data structures with efficient updates
//! - Version history or undo/redo functionality
//! - Safe sharing across threads without locks
//! - Functional programming patterns
//!
//! For mutable use cases where persistence isn't needed, prefer `Vec<T>`.
//!
//! # Error Handling Policy
//!
//! This module follows a dual approach to error handling:
//!
//! - **Total functions** (e.g., `update`, `get`): Return a default value or `Option`
//!   when operations cannot complete. This supports functional programming patterns
//!   where operations should always succeed.
//!
//! - **Fallible functions** (e.g., `try_update`, `try_get`): Return `Result` with
//!   detailed error information via `PVecError`.
//!
//! | Operation | Total Version | Fallible Version |
//! |-----------|---------------|------------------|
//! | Get element | `get()` → `Option<&T>` | `try_get()` → `Result<&T, PVecError>` |
//! | Update element | `update()` → `Self` (clone on error) | `try_update()` → `Result<Self, PVecError>` |
//!
//! # Examples
//!
//! ```
//! use rustica::pvec::{PersistentVector, pvec};
//!
//! // Create a new empty vector
//! let vec: PersistentVector<i32> = PersistentVector::new();
//!
//! // Use the convenience macro
//! let vec = pvec![1, 2, 3, 4, 5];
//!
//! // Add elements
//! let vec = vec.push_back(6).push_front(0);
//!
//! // Access elements
//! assert_eq!(vec.get(0), Some(&0));
//! assert_eq!(vec.get(6), Some(&6));
//! ```

pub mod core;
pub mod error;
pub mod iter;
pub(crate) mod node;
pub mod traits;
pub(crate) mod tree;

pub use core::PersistentVector;
pub use error::PVecError;
pub use iter::{PersistentVectorIntoIter, PersistentVectorIter};

/// Convenience macro for creating persistent vectors.
///
/// # Examples
///
/// ```
/// use rustica::pvec::pvec;
/// use rustica::pvec::PersistentVector;
///
/// // Empty vector
/// let empty: PersistentVector<i32> = pvec![];
///
/// // Vector with elements
/// let vec = pvec![1, 2, 3, 4, 5];
/// ```
#[macro_export]
macro_rules! pvec {
    () => { $crate::pvec::PersistentVector::new() };
    ($($x:expr),+ $(,)?) => {
        $crate::pvec::PersistentVector::from_iter([$($x),+])
    };
}

pub use pvec;
