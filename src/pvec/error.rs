use std::fmt::{self, Debug};

#[derive(Debug, Clone, PartialEq)]
pub enum PVecError {
    IndexOutOfBounds { index: usize, len: usize },
    InvalidRange { start: usize, end: usize },
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
