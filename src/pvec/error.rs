//! Error types for persistent vector operations.
//!
//! This module defines the error types that can occur when performing operations
//! on persistent vectors. These errors provide detailed information about what
//! went wrong, including the invalid indices and vector lengths involved.
//!
//! # Error Types
//!
//! - [`PVecError::IndexOutOfBounds`] - Returned when accessing an index beyond the vector's length
//! - [`PVecError::InvalidRange`] - Returned when specifying a range where start > end
//!
//! # Examples
//!
//! ```
//! use rustica::pvec::{PersistentVector, PVecError};
//!
//! let vec = PersistentVector::from_slice(&[1, 2, 3]);
//!
//! // Attempting to access an out-of-bounds index
//! match vec.try_get(10) {
//!     Ok(value) => println!("Value: {}", value),
//!     Err(PVecError::IndexOutOfBounds { index, len }) => {
//!         println!("Cannot access index {} in vector of length {}", index, len);
//!     },
//!     Err(_) => unreachable!(),
//! }
//! ```

use std::fmt::{self, Debug};

/// Errors that can occur during persistent vector operations.
///
/// This enum represents all possible error conditions that can arise when
/// working with [`PersistentVector`](super::PersistentVector). Each variant
/// contains contextual information to help diagnose the issue.
///
/// # Examples
///
/// ```
/// use rustica::pvec::{PersistentVector, PVecError};
///
/// let vec = PersistentVector::from_slice(&[1, 2, 3]);
///
/// // Using try_get for safe access with detailed error information
/// let result = vec.try_get(100);
/// assert!(matches!(result, Err(PVecError::IndexOutOfBounds { .. })));
/// ```
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum PVecError {
    /// Index is out of bounds for the vector.
    ///
    /// This error occurs when attempting to access an element at an index
    /// that is greater than or equal to the vector's length.
    ///
    /// # Fields
    ///
    /// - `index` - The invalid index that was attempted to be accessed
    /// - `len` - The actual length of the vector at the time of access
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::{PersistentVector, PVecError};
    ///
    /// let vec = PersistentVector::from_slice(&[1, 2, 3]);
    /// let err = vec.try_get(5).unwrap_err();
    ///
    /// match err {
    ///     PVecError::IndexOutOfBounds { index, len } => {
    ///         assert_eq!(index, 5);
    ///         assert_eq!(len, 3);
    ///     },
    ///     _ => unreachable!(),
    /// }
    /// ```
    IndexOutOfBounds {
        /// The invalid index that was accessed.
        index: usize,
        /// The actual length of the vector.
        len: usize,
    },

    /// Range is invalid (start > end).
    ///
    /// This error occurs when specifying a range where the start index
    /// is greater than the end index, which represents an invalid or
    /// empty range that cannot be processed.
    ///
    /// # Fields
    ///
    /// - `start` - The start index of the invalid range
    /// - `end` - The end index of the invalid range
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::PVecError;
    ///
    /// let err = PVecError::InvalidRange { start: 5, end: 2 };
    /// assert_eq!(err.to_string(), "Invalid range: start 5 is greater than end 2");
    /// ```
    InvalidRange {
        /// The start index of the range.
        start: usize,
        /// The end index of the range.
        end: usize,
    },
}

impl PVecError {
    /// Creates a new `IndexOutOfBounds` error.
    ///
    /// # Arguments
    ///
    /// * `index` - The invalid index that was accessed
    /// * `len` - The actual length of the vector
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::PVecError;
    ///
    /// let err = PVecError::index_out_of_bounds(10, 5);
    /// assert!(matches!(err, PVecError::IndexOutOfBounds { index: 10, len: 5 }));
    /// ```
    #[inline]
    pub const fn index_out_of_bounds(index: usize, len: usize) -> Self {
        PVecError::IndexOutOfBounds { index, len }
    }

    /// Creates a new `InvalidRange` error.
    ///
    /// # Arguments
    ///
    /// * `start` - The start index of the invalid range
    /// * `end` - The end index of the invalid range
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::PVecError;
    ///
    /// let err = PVecError::invalid_range(5, 2);
    /// assert!(matches!(err, PVecError::InvalidRange { start: 5, end: 2 }));
    /// ```
    #[inline]
    pub const fn invalid_range(start: usize, end: usize) -> Self {
        PVecError::InvalidRange { start, end }
    }

    /// Returns `true` if this is an `IndexOutOfBounds` error.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::PVecError;
    ///
    /// let err = PVecError::index_out_of_bounds(10, 5);
    /// assert!(err.is_index_out_of_bounds());
    /// ```
    #[inline]
    pub const fn is_index_out_of_bounds(&self) -> bool {
        matches!(self, PVecError::IndexOutOfBounds { .. })
    }

    /// Returns `true` if this is an `InvalidRange` error.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::PVecError;
    ///
    /// let err = PVecError::invalid_range(5, 2);
    /// assert!(err.is_invalid_range());
    /// ```
    #[inline]
    pub const fn is_invalid_range(&self) -> bool {
        matches!(self, PVecError::InvalidRange { .. })
    }
}

impl fmt::Display for PVecError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            PVecError::IndexOutOfBounds { index, len } => {
                write!(
                    f,
                    "Index {} out of bounds for vector of length {}",
                    index, len
                )
            },
            PVecError::InvalidRange { start, end } => {
                write!(
                    f,
                    "Invalid range: start {} is greater than end {}",
                    start, end
                )
            },
        }
    }
}

impl std::error::Error for PVecError {}
