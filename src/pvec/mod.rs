//! Persistent vector implementation using RRB (Relaxed Radix Balanced) trees.
//!
//! This module provides a persistent, immutable vector data structure that supports
//! efficient operations for insertion, deletion, and random access. The implementation
//! uses RRB trees which maintain logarithmic performance characteristics while
//! supporting efficient concatenation and splitting operations.
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
