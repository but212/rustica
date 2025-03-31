//! Iterators for the Persistent Vector
//!
//! This module defines various iterators to traverse the persistent vector efficiently.

use std::iter::FusedIterator;
use std::cmp::Ordering;

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
    
    fn size_hint(&self) -> (usize, Option<usize>) {
        let remaining = self.back_pos - self.front_pos;
        (remaining, Some(remaining))
    }
}

impl<'a, T: Clone> DoubleEndedIterator for Iter<'a, T> {
    fn next_back(&mut self) -> Option<Self::Item> {
        if self.front_pos >= self.back_pos {
            return None;
        }
        
        self.back_pos -= 1;
        self.vector.get(self.back_pos)
    }
}

impl<'a, T: Clone> ExactSizeIterator for Iter<'a, T> {}

impl<'a, T: Clone> FusedIterator for Iter<'a, T> {}

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
    pub(crate) fn new(
        vector: &'a PersistentVector<T>,
        min_chunk_size: usize,
        max_chunk_size: usize
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
    pub(crate) fn with_default_sizes(vector: &'a PersistentVector<T>) -> Self {
        // Default to chunks between 16 and 256 elements
        Self::new(vector, 16, 256)
    }
}

impl<'a, T: Clone> Iterator for ChunksIter<'a, T> {
    type Item = Vec<T>;
    
    fn next(&mut self) -> Option<Self::Item> {
        if self.current_index >= self.end_index {
            return None;
        }
        
        let chunk_size = self.vector.get_chunk(self.current_index, self.min_chunk_size, self.max_chunk_size);
        let end_idx = std::cmp::min(self.current_index + chunk_size, self.end_index);
        
        let mut items = Vec::with_capacity(end_idx - self.current_index);
        
        for i in self.current_index..end_idx {
            if let Some(item) = self.vector.get(i) {
                items.push(item.clone());
            }
        }
        
        self.current_index = end_idx;
        
        Some(items)
    }
    
    fn size_hint(&self) -> (usize, Option<usize>) {
        if self.current_index >= self.end_index {
            return (0, Some(0));
        }
        
        let remaining_elements = self.end_index - self.current_index;
        let min_chunks = remaining_elements / self.max_chunk_size + 
                         if remaining_elements % self.max_chunk_size > 0 { 1 } else { 0 };
        
        let max_chunks = remaining_elements / self.min_chunk_size +
                         if remaining_elements % self.min_chunk_size > 0 { 1 } else { 0 };
        
        (min_chunks, Some(max_chunks))
    }
}

/// An iterator that yields elements in sorted order.
///
/// This doesn't actually sort the vector, but provides elements in sorted order.
pub struct SortedIter<'a, T: Clone + Ord> {
    /// Reference to the vector being iterated
    vector: &'a PersistentVector<T>,
    
    /// Indices sorted by element values
    sorted_indices: Vec<usize>,
    
    /// Current position
    position: usize,
}

impl<'a, T: Clone + Ord> SortedIter<'a, T> {
    /// Create a new iterator that yields elements in sorted order.
    pub(crate) fn new(vector: &'a PersistentVector<T>) -> Self {
        let len = vector.len();
        let mut indices: Vec<usize> = (0..len).collect();
        
        // Sort indices based on element values
        indices.sort_by(|&a, &b| {
            match (vector.get(a), vector.get(b)) {
                (Some(val_a), Some(val_b)) => val_a.cmp(val_b),
                (None, Some(_)) => Ordering::Less,
                (Some(_), None) => Ordering::Greater,
                (None, None) => Ordering::Equal,
            }
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
    
    fn size_hint(&self) -> (usize, Option<usize>) {
        let remaining = self.sorted_indices.len() - self.position;
        (remaining, Some(remaining))
    }
}

impl<'a, T: Clone + Ord> ExactSizeIterator for SortedIter<'a, T> {}

impl<'a, T: Clone + Ord> FusedIterator for SortedIter<'a, T> {}