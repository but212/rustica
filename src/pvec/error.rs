//! Errors produced by persistent-vector operations.

use std::fmt;

/// An index was outside the logical vector length.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum PVecError {
    IndexOutOfBounds { index: usize, len: usize },
}

impl PVecError {
    #[inline]
    pub const fn index_out_of_bounds(index: usize, len: usize) -> Self {
        Self::IndexOutOfBounds { index, len }
    }

    #[inline]
    pub const fn is_index_out_of_bounds(&self) -> bool {
        matches!(self, Self::IndexOutOfBounds { .. })
    }
}

impl fmt::Display for PVecError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let Self::IndexOutOfBounds { index, len } = self;
        write!(f, "Index {index} out of bounds for vector of length {len}")
    }
}

impl std::error::Error for PVecError {}
