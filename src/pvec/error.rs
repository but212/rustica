//! Error types for persistent vector operations.

use std::fmt::{self, Debug};

/// Errors that can occur during persistent vector operations.
#[derive(Debug, Clone, PartialEq)]
pub enum PVecError {
    /// Index is out of bounds for the vector.
    ///
    /// Contains the invalid index and the actual length of the vector.
    IndexOutOfBounds {
        /// The invalid index that was accessed.
        index: usize,
        /// The actual length of the vector.
        len: usize
    },
    /// Range is invalid (start > end).
    ///
    /// Contains the invalid start and end indices.
    InvalidRange {
        /// The start index of the range.
        start: usize,
        /// The end index of the range.
        end: usize
    },
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
