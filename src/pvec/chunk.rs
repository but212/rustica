//! Chunk Module
//!
//! This module defines the Chunk type, which is the basic building block
//! for leaf nodes in the persistent vector. Chunks are fixed-size arrays
//! that store elements directly.

use std::fmt::{self, Debug};
use std::iter::FromIterator;
use std::ops::{Index, IndexMut};

/// The default size of a chunk, measured in number of elements.
///
/// This value is chosen as a balance between memory usage and performance.
/// Smaller values would reduce memory usage but increase tree height,
/// while larger values would decrease tree height but potentially waste memory.
pub(crate) const CHUNK_SIZE: usize = 32;

/// Number of bits needed to represent indices within a chunk.
pub(crate) const CHUNK_BITS: usize = 5; // log2(32)

/// A fixed-size chunk of elements used as the basic storage unit in the vector.
///
/// Chunks are used in leaf nodes and provide efficient operations for small
/// sequences of elements. They are implemented as a wrapper around a Vec
/// with a maximum capacity of CHUNK_SIZE.
#[derive(Clone)]
pub(crate) struct Chunk<T> {
    elements: Vec<T>,
}

impl<T: Clone> Chunk<T> {
    /// Create a new empty chunk.
    ///
    /// This initializes a chunk with zero elements but pre-allocates memory
    /// for the maximum capacity (CHUNK_SIZE) to avoid reallocations when
    /// adding elements.
    #[inline]
    pub fn new() -> Self {
        Self {
            elements: Vec::with_capacity(CHUNK_SIZE),
        }
    }

    /// Get the number of elements in the chunk.
    ///
    /// This operation is O(1) as it just returns the length of the internal vector.
    #[inline]
    pub fn len(&self) -> usize {
        self.elements.len()
    }

    /// Check if the chunk is full (contains CHUNK_SIZE elements).
    #[inline]
    pub fn is_full(&self) -> bool {
        self.elements.len() >= CHUNK_SIZE
    }

    /// Get a reference to the element at the specified index.
    ///
    /// Returns `None` if the index is out of bounds.
    #[inline]
    pub fn get(&self, index: usize) -> Option<&T> {
        self.elements.get(index)
    }

    /// Get a mutable reference to the element at the specified index.
    ///
    /// Returns `None` if the index is out of bounds.
    #[inline]
    pub fn get_mut(&mut self, index: usize) -> Option<&mut T> {
        self.elements.get_mut(index)
    }

    /// Add an element to the end of the chunk.
    ///
    /// If the chunk is full (contains CHUNK_SIZE elements), the operation
    /// will fail and return false. Otherwise, the element is added and
    /// the function returns true.
    #[inline]
    pub fn push_back(&mut self, value: T) -> bool {
        if self.is_full() {
            return false;
        }
        self.elements.push(value);
        true
    }

    /// Get a slice of the underlying elements.
    #[inline]
    pub fn as_slice(&self) -> &[T] {
        &self.elements
    }
}

impl<T: Clone + PartialEq> PartialEq for Chunk<T> {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        // Compare slice contents
        let s1 = self.as_slice();
        let s2 = other.as_slice();
        s1 == s2
    }
}

impl<T: Clone + Eq> Eq for Chunk<T> {}

impl<T: Clone> Default for Chunk<T> {
    #[inline]
    fn default() -> Self {
        Self::new()
    }
}

impl<T: Clone + Debug> Debug for Chunk<T> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self.elements.iter()).finish()
    }
}

impl<T: Clone> FromIterator<T> for Chunk<T> {
    #[inline]
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        let mut chunk = Self::new();
        for item in iter {
            if !chunk.push_back(item) {
                break;
            }
        }
        chunk
    }
}

impl<T: Clone> Index<usize> for Chunk<T> {
    type Output = T;

    #[inline]
    fn index(&self, index: usize) -> &Self::Output {
        &self.elements[index]
    }
}

impl<T: Clone> IndexMut<usize> for Chunk<T> {
    #[inline]
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        &mut self.elements[index]
    }
}
