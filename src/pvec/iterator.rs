//! Iterators for the Persistent Vector
//!
//! This module defines various iterators to traverse the persistent vector efficiently.
//!
//! # Iterator Types
//!
//! - `Iter`: References elements of a vector without consuming it
//! - `IntoIter`: Consumes a vector and yields owned elements
//! - `ChunksIter`: Yields chunks of elements for efficient parallel processing
//! - `SortedIter`: Provides elements in sorted order without modifying the vector
//!
//! All iterators implement the standard Rust iterator traits including
//! `Iterator`, `DoubleEndedIterator` (where applicable), `ExactSizeIterator`,
//! and `FusedIterator`.

use std::cmp::Ordering;
use std::iter::FusedIterator;

use crate::pvec::vector::PersistentVector;

/// An iterator over the elements of a persistent vector.
pub struct Iter<'a, T: Clone> {
    /// Reference to the vector being iterated
    vector: &'a PersistentVector<T>,

    /// Current position from the front
    front_pos: usize,

    /// Current position from the back
    back_pos: usize,
}

impl<'a, T: Clone> Iter<'a, T> {
    /// Create a new iterator for the given vector.
    pub(crate) fn new(vector: &'a PersistentVector<T>) -> Self {
        let len = vector.len();
        Self {
            vector,
            front_pos: 0,
            back_pos: len,
        }
    }
}

impl<'a, T: Clone> Iterator for Iter<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        if self.front_pos >= self.back_pos {
            return None;
        }

        let result = self.vector.get(self.front_pos);
        self.front_pos += 1;
        result
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        let remaining = self.back_pos - self.front_pos;
        (remaining, Some(remaining))
    }
}

impl<T: Clone> DoubleEndedIterator for Iter<'_, T> {
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.front_pos >= self.back_pos {
            return None;
        }

        self.back_pos -= 1;
        self.vector.get(self.back_pos)
    }
}

impl<T: Clone> ExactSizeIterator for Iter<'_, T> {}

impl<T: Clone> FusedIterator for Iter<'_, T> {}

/// An iterator that consumes a persistent vector and yields its elements.
pub struct IntoIter<T: Clone> {
    /// The vector being consumed
    vector: PersistentVector<T>,

    /// Current position from the front
    front_pos: usize,

    /// Current position from the back
    back_pos: usize,
}

impl<T: Clone> IntoIter<T> {
    /// Create a new consuming iterator for the given vector.
    pub(crate) fn new(vector: PersistentVector<T>) -> Self {
        let len = vector.len();
        Self {
            vector,
            front_pos: 0,
            back_pos: len,
        }
    }
}

impl<T: Clone> Iterator for IntoIter<T> {
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        if self.front_pos >= self.back_pos {
            return None;
        }

        let result = self.vector.get(self.front_pos).cloned();
        self.front_pos += 1;
        result
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        let remaining = self.back_pos - self.front_pos;
        (remaining, Some(remaining))
    }
}

impl<T: Clone> DoubleEndedIterator for IntoIter<T> {
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.front_pos >= self.back_pos {
            return None;
        }

        self.back_pos -= 1;
        self.vector.get(self.back_pos).cloned()
    }
}

impl<T: Clone> ExactSizeIterator for IntoIter<T> {}

impl<T: Clone> FusedIterator for IntoIter<T> {}

/// An iterator over chunks of elements in a persistent vector.
///
/// This is useful for efficiently processing large vectors in parallel.
pub struct ChunksIter<'a, T: Clone> {
    /// Reference to the vector being iterated
    vector: &'a PersistentVector<T>,

    /// Starting index for the current chunk
    current_index: usize,

    /// End index of iteration
    end_index: usize,

    /// Minimum chunk size to yield
    min_chunk_size: usize,

    /// Maximum chunk size to yield
    max_chunk_size: usize,
}

impl<'a, T: Clone> ChunksIter<'a, T> {
    /// Create a new chunk iterator with custom chunk size parameters.
    #[inline]
    pub(crate) fn new(
        vector: &'a PersistentVector<T>,
        min_chunk_size: usize,
        max_chunk_size: usize,
    ) -> Self {
        let len = vector.len();
        Self {
            vector,
            current_index: 0,
            end_index: len,
            min_chunk_size,
            max_chunk_size,
        }
    }

    /// Create a new chunk iterator with default parameters.
    #[inline]
    pub(crate) fn with_default_sizes(vector: &'a PersistentVector<T>) -> Self {
        // Default to chunks between 16 and 256 elements
        Self::new(vector, 16, 256)
    }
}

impl<T: Clone> Iterator for ChunksIter<'_, T> {
    type Item = Vec<T>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.current_index >= self.end_index {
            return None;
        }

        // Get the chunk from the vector
        let chunk =
            self.vector
                .get_chunk(self.current_index, self.min_chunk_size, self.max_chunk_size);

        // Use the size of the returned chunk to calculate the end index
        let chunk_size = chunk.len();
        let end_idx = std::cmp::min(self.current_index + chunk_size, self.end_index);

        self.current_index = end_idx;

        // Return the chunk
        Some(chunk)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        if self.current_index >= self.end_index {
            return (0, Some(0));
        }

        let remaining_elements = self.end_index - self.current_index;
        let min_chunks = remaining_elements / self.max_chunk_size
            + if remaining_elements % self.max_chunk_size > 0 {
                1
            } else {
                0
            };

        let max_chunks = remaining_elements / self.min_chunk_size
            + if remaining_elements % self.min_chunk_size > 0 {
                1
            } else {
                0
            };

        (min_chunks, Some(max_chunks))
    }
}

/// An iterator that yields elements in sorted order without modifying the original vector.
///
/// This iterator creates a sorted view of the vector by tracking indices in sorted order
/// rather than modifying the original data structure. This provides efficient iteration
/// over elements in their natural ordering while preserving the original vector's structure.
pub struct SortedIter<'a, T: Clone + Ord> {
    /// Reference to the vector being iterated
    vector: &'a PersistentVector<T>,

    /// Indices sorted by element values
    sorted_indices: Vec<usize>,

    /// Current position in the iteration
    position: usize,
}

impl<'a, T: Clone + Ord> SortedIter<'a, T> {
    /// Create a new iterator that yields elements in sorted order.
    ///
    /// This method sorts the indices of the vector elements based on their values,
    /// allowing iteration in sorted order without modifying the original vector.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::PersistentVector;
    ///
    /// let vec = PersistentVector::from_slice(&[3, 1, 4, 2, 5]);
    /// let sorted: Vec<&i32> = vec.sorted().collect();
    /// assert_eq!(sorted, vec![&1, &2, &3, &4, &5]);
    /// ```
    pub(crate) fn new(vector: &'a PersistentVector<T>) -> Self {
        let len = vector.len();
        let mut indices: Vec<usize> = (0..len).collect();

        // Sort indices based on element values
        indices.sort_by(|&a, &b| match (vector.get(a), vector.get(b)) {
            (Some(val_a), Some(val_b)) => val_a.cmp(val_b),
            (None, Some(_)) => Ordering::Less,
            (Some(_), None) => Ordering::Greater,
            (None, None) => Ordering::Equal,
        });

        Self {
            vector,
            sorted_indices: indices,
            position: 0,
        }
    }
}

impl<'a, T: Clone + Ord> Iterator for SortedIter<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        if self.position >= self.sorted_indices.len() {
            return None;
        }

        let index = self.sorted_indices[self.position];
        self.position += 1;
        self.vector.get(index)
    }

    #[inline]
    fn size_hint(&self) -> (usize, Option<usize>) {
        let remaining = self.sorted_indices.len() - self.position;
        (remaining, Some(remaining))
    }
}

impl<T: Clone + Ord> ExactSizeIterator for SortedIter<'_, T> {}

impl<T: Clone + Ord> FusedIterator for SortedIter<'_, T> {}
