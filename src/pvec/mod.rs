//! # Persistent Vector
//!
//! A persistent vector implementation using Relaxed Radix Balanced Trees.
//!
//! This data structure provides efficient immutable operations while
//! maintaining structural sharing between versions. This makes it ideal
//! for functional programming patterns and concurrent applications where
//! immutable data structures are preferred.
//!
//! ## Performance Characteristics
//!
//! - Access: O(log n)
//! - Insert/Update: O(log n)
//! - Push/Pop: O(1) amortized
//! - Concatenation: O(log n)
//!
//! ## Implementation Details
//!
//! The vector uses a combination of strategies for optimal performance:
//!
//! 1. Small vectors use an optimized representation for better memory usage
//! 2. Larger vectors use a tree structure with a fixed branching factor
//! 3. A flexible memory management system to reduce allocation overhead
//! 4. Intelligent caching for faster sequential access

#[cfg(feature = "pvec")]
pub mod cache;

#[cfg(feature = "pvec")]
pub mod chunk;

#[cfg(feature = "pvec")]
pub mod iterator;

#[cfg(feature = "pvec")]
pub mod memory;

#[cfg(feature = "pvec")]
pub mod node;

#[cfg(feature = "pvec")]
pub mod tree;

#[cfg(feature = "pvec")]
pub mod vector;

// Re-export the main types
#[cfg(feature = "pvec")]
pub use self::iterator::{ChunksIter, IntoIter, Iter, SortedIter};
#[cfg(feature = "pvec")]
pub use self::memory::MemoryManager;
#[cfg(feature = "pvec")]
pub use self::vector::PersistentVector;

/// Creates a new `PersistentVector` with the provided elements.
///
/// # Examples
///
/// ```
/// use rustica::pvec;
///
/// // Create an empty vector
/// let empty: rustica::pvec::PersistentVector<i32> = pvec![];
/// assert_eq!(empty.len(), 0);
///
/// // Create a vector with elements
/// let numbers = pvec![1, 2, 3, 4];
/// assert_eq!(numbers.len(), 4);
/// assert_eq!(numbers.get(2), Some(&3));
///
/// // Trailing commas are supported
/// let with_trailing = pvec![10, 20, 30,];
/// assert_eq!(with_trailing.len(), 3);
/// ```
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
