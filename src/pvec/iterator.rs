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
    ///
    /// Returns a new iterator that references elements of the vector without consuming it.
    #[inline(always)]
    #[must_use]
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

    /// Advances the iterator and returns the next value.
    ///
    /// Returns `None` when the iterator is exhausted.
    #[inline(always)]
    fn next(&mut self) -> Option<Self::Item> {
        if self.front_pos >= self.back_pos {
            return None;
        }
        let result = self.vector.get(self.front_pos);
        self.front_pos += 1;
        result
    }

    /// Returns the number of elements remaining in the iterator.
    ///
    /// This method is a hint, and may not be accurate in all cases.
    #[inline(always)]
    fn size_hint(&self) -> (usize, Option<usize>) {
        let remaining = self.back_pos - self.front_pos;
        (remaining, Some(remaining))
    }
}

impl<T: Clone> DoubleEndedIterator for Iter<'_, T> {
    /// Advances the iterator from the back and returns the next value.
    ///
    /// Returns `None` when the iterator is exhausted.
    #[inline(always)]
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
    ///
    /// Returns a new iterator that consumes the vector and yields its elements.
    #[inline(always)]
    #[must_use]
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

    /// Advances the iterator and returns the next value.
    ///
    /// Returns `None` when the iterator is exhausted.
    #[inline(always)]
    fn next(&mut self) -> Option<Self::Item> {
        if self.front_pos >= self.back_pos {
            return None;
        }
        let result = self.vector.get(self.front_pos).cloned();
        self.front_pos += 1;
        result
    }

    /// Returns the number of elements remaining in the iterator.
    ///
    /// This method is a hint, and may not be accurate in all cases.
    #[inline(always)]
    fn size_hint(&self) -> (usize, Option<usize>) {
        let remaining = self.back_pos - self.front_pos;
        (remaining, Some(remaining))
    }
}

impl<T: Clone> DoubleEndedIterator for IntoIter<T> {
    /// Advances the iterator from the back and returns the next value.
    ///
    /// Returns `None` when the iterator is exhausted.
    #[inline(always)]
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

    /// Current position in the iteration
    pos: usize,

    /// Minimum chunk size to yield
    min_chunk_size: usize,

    /// Maximum chunk size to yield
    max_chunk_size: usize,
}

impl<'a, T: Clone> ChunksIter<'a, T> {
    /// Create a new chunk iterator with custom chunk size parameters.
    ///
    /// Returns a new iterator that yields chunks of elements in the vector.
    #[inline(always)]
    #[must_use]
    pub(crate) fn new(
        vector: &'a PersistentVector<T>, min_chunk_size: usize, max_chunk_size: usize,
    ) -> Self {
        Self {
            vector,
            pos: 0,
            min_chunk_size,
            max_chunk_size,
        }
    }

    /// Create a new chunk iterator with default parameters.
    ///
    /// Returns a new iterator that yields chunks of elements in the vector.
    /// The chunk size is set to the vector's configured chunk_size.
    #[inline(always)]
    #[must_use]
    pub(crate) fn with_default_sizes(vector: &'a PersistentVector<T>) -> Self {
        let chunk_size = vector.chunk_size();
        Self::new(vector, chunk_size, chunk_size)
    }
}

impl<T: Clone> Iterator for ChunksIter<'_, T> {
    type Item = Vec<T>;

    /// Advances the iterator and returns the next chunk.
    ///
    /// Returns `None` when the iterator is exhausted.
    #[inline(always)]
    fn next(&mut self) -> Option<Self::Item> {
        if self.pos >= self.vector.len() {
            return None;
        }
        let remaining = self.vector.len() - self.pos;
        let chunk_size = remaining.min(self.max_chunk_size).max(self.min_chunk_size);
        let mut chunk = Vec::with_capacity(chunk_size);
        for _ in 0..chunk_size {
            if let Some(item) = self.vector.get(self.pos).cloned() {
                chunk.push(item);
                self.pos += 1;
            } else {
                break;
            }
        }
        Some(chunk)
    }

    /// Returns the number of chunks remaining in the iterator.
    ///
    /// This method is a hint, and may not be accurate in all cases.
    #[inline(always)]
    fn size_hint(&self) -> (usize, Option<usize>) {
        let remaining = self.vector.len().saturating_sub(self.pos);
        let min_chunks = remaining.div_ceil(self.max_chunk_size);
        (min_chunks, Some(min_chunks))
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
    indices: Vec<usize>,

    /// Current position in the iteration
    pos: usize,
}

impl<'a, T: Clone + Ord> SortedIter<'a, T> {
    /// Create a new iterator that yields elements in sorted order.
    ///
    /// Returns a new iterator that yields elements in sorted order without modifying the original vector.
    #[inline(always)]
    #[must_use]
    pub(crate) fn new(vector: &'a PersistentVector<T>) -> Self {
        let len = vector.len();
        let mut indices: Vec<usize> = (0..len).collect();
        indices.sort_unstable_by(|&i, &j| vector.get(i).cmp(&vector.get(j)));
        Self {
            vector,
            indices,
            pos: 0,
        }
    }
}

impl<'a, T: Clone + Ord> Iterator for SortedIter<'a, T> {
    type Item = &'a T;

    /// Advances the iterator and returns the next value.
    ///
    /// Returns `None` when the iterator is exhausted.
    #[inline(always)]
    fn next(&mut self) -> Option<Self::Item> {
        if self.pos >= self.indices.len() {
            return None;
        }
        let idx = self.indices[self.pos];
        self.pos += 1;
        self.vector.get(idx)
    }

    /// Returns the number of elements remaining in the iterator.
    ///
    /// This method is a hint, and may not be accurate in all cases.
    #[inline(always)]
    fn size_hint(&self) -> (usize, Option<usize>) {
        let remaining = self.indices.len().saturating_sub(self.pos);
        (remaining, Some(remaining))
    }
}

impl<T: Clone + Ord> ExactSizeIterator for SortedIter<'_, T> {}

impl<T: Clone + Ord> FusedIterator for SortedIter<'_, T> {}
