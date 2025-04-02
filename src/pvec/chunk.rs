//! Chunk Module
//!
//! This module defines the Chunk type, which is the basic building block
//! for leaf nodes in the persistent vector. Chunks are fixed-size arrays
//! that store elements directly.
//!
//! # Examples
//!
//! ```
//! use rustica::pvec::chunk::{Chunk, CHUNK_SIZE};
//!
//! // Create a new empty chunk
//! let mut chunk: Chunk<i32> = Chunk::new();
//!
//! // Add elements to the chunk
//! chunk.push_back(1);
//! chunk.push_back(2);
//! chunk.push_back(3);
//!
//! // Access elements
//! assert_eq!(chunk.get(0), Some(&1));
//! assert_eq!(chunk.len(), 3);
//!
//! // Create a chunk from a slice
//! let data = [10, 20, 30, 40];
//! let chunk_from_slice = Chunk::from_slice(&data);
//! assert_eq!(chunk_from_slice.len(), 4);
//! ```

use std::cmp::min;
use std::fmt::{self, Debug};
use std::iter::FromIterator;
use std::ops::{Index, IndexMut};

/// The default size of a chunk, measured in number of elements.
///
/// This value is chosen as a balance between memory usage and performance.
/// Smaller values would reduce memory usage but increase tree height,
/// while larger values would decrease tree height but potentially waste memory.
pub const CHUNK_SIZE: usize = 32;

/// Bit mask for extracting the index within a chunk.
pub const CHUNK_MASK: usize = CHUNK_SIZE - 1;

/// Number of bits needed to represent indices within a chunk.
pub const CHUNK_BITS: usize = 5; // log2(32)

/// A fixed-size chunk of elements used as the basic storage unit in the vector.
///
/// Chunks are used in leaf nodes and provide efficient operations for small
/// sequences of elements. They are implemented as a wrapper around a Vec
/// with a maximum capacity of CHUNK_SIZE.
#[derive(Clone)]
pub struct Chunk<T> {
    elements: Vec<T>,
}

impl<T: Clone> Chunk<T> {
    /// Create a new empty chunk.
    ///
    /// This initializes a chunk with zero elements but pre-allocates memory
    /// for the maximum capacity (CHUNK_SIZE) to avoid reallocations when
    /// adding elements.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::chunk::Chunk;
    ///
    /// let chunk: Chunk<i32> = Chunk::new();
    /// assert_eq!(chunk.len(), 0);
    /// ```
    #[inline]
    pub fn new() -> Self {
        Self {
            elements: Vec::with_capacity(CHUNK_SIZE),
        }
    }

    /// Create a new chunk with a single element.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::chunk::Chunk;
    ///
    /// let chunk = Chunk::unit(42);
    /// assert_eq!(chunk.len(), 1);
    /// assert_eq!(chunk.get(0), Some(&42));
    /// ```
    #[inline]
    pub fn unit(value: T) -> Self {
        let mut chunk = Self::new();
        chunk.push_back(value);
        chunk
    }

    /// Create a new chunk from a slice of elements.
    ///
    /// If the slice contains more than CHUNK_SIZE elements,
    /// only the first CHUNK_SIZE elements will be used.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::chunk::Chunk;
    ///
    /// let data = vec![1, 2, 3, 4, 5];
    /// let chunk = Chunk::from_slice(&data);
    /// assert_eq!(chunk.len(), 5);
    /// assert_eq!(chunk.get(2), Some(&3));
    /// ```
    #[inline]
    pub fn from_slice(slice: &[T]) -> Self {
        let mut chunk = Self::new();
        for item in slice.iter().take(min(slice.len(), CHUNK_SIZE)) {
            chunk.push_back(item.clone());
        }
        chunk
    }

    /// Get the number of elements in the chunk.
    ///
    /// This operation is O(1) as it just returns the length of the internal vector.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::chunk::Chunk;
    ///
    /// let mut chunk = Chunk::new();
    /// assert_eq!(chunk.len(), 0);
    ///
    /// chunk.push_back(42);
    /// assert_eq!(chunk.len(), 1);
    /// ```
    #[inline]
    pub fn len(&self) -> usize {
        self.elements.len()
    }

    /// Check if the chunk is empty (contains no elements).
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::chunk::Chunk;
    ///
    /// let chunk: Chunk<i32> = Chunk::new();
    /// assert!(chunk.is_empty());
    ///
    /// let mut chunk = Chunk::new();
    /// chunk.push_back(42);
    /// assert!(!chunk.is_empty());
    /// ```
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.elements.is_empty()
    }

    /// Check if the chunk is full (contains CHUNK_SIZE elements).
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::chunk::{Chunk, CHUNK_SIZE};
    ///
    /// let mut chunk = Chunk::new();
    /// assert!(!chunk.is_full());
    ///
    /// // Fill the chunk to capacity
    /// for i in 0..CHUNK_SIZE {
    ///     chunk.push_back(i);
    /// }
    /// assert!(chunk.is_full());
    /// ```
    #[inline]
    pub fn is_full(&self) -> bool {
        self.elements.len() >= CHUNK_SIZE
    }

    /// Get a reference to the element at the specified index.
    ///
    /// Returns `None` if the index is out of bounds.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::chunk::Chunk;
    ///
    /// let mut chunk = Chunk::new();
    /// chunk.push_back(42);
    /// assert_eq!(chunk.get(0), Some(&42));
    /// assert_eq!(chunk.get(1), None); // Out of bounds
    /// ```
    #[inline]
    pub fn get(&self, index: usize) -> Option<&T> {
        self.elements.get(index)
    }

    /// Get a mutable reference to the element at the specified index.
    ///
    /// Returns `None` if the index is out of bounds.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::chunk::Chunk;
    ///
    /// let mut chunk = Chunk::new();
    /// chunk.push_back(42);
    /// if let Some(value) = chunk.get_mut(0) {
    ///     *value = 100;
    /// }
    /// assert_eq!(chunk.get(0), Some(&100));
    /// assert_eq!(chunk.get_mut(1), None); // Out of bounds
    /// ```
    #[inline]
    pub fn get_mut(&mut self, index: usize) -> Option<&mut T> {
        self.elements.get_mut(index)
    }

    /// Add an element to the end of the chunk.
    ///
    /// If the chunk is full (contains CHUNK_SIZE elements), the operation
    /// will fail and return false. Otherwise, the element is added and
    /// the function returns true.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::chunk::Chunk;
    ///
    /// let mut chunk = Chunk::new();
    /// assert_eq!(chunk.len(), 0);
    ///
    /// assert!(chunk.push_back(42));
    /// assert_eq!(chunk.len(), 1);
    /// assert_eq!(chunk.get(0), Some(&42));
    /// ```
    #[inline]
    pub fn push_back(&mut self, value: T) -> bool {
        if self.is_full() {
            return false;
        }
        self.elements.push(value);
        true
    }

    /// Add an element to the beginning of the chunk.
    ///
    /// If the chunk is full (contains CHUNK_SIZE elements), the operation
    /// will fail and return false. Otherwise, the element is added and
    /// the function returns true.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::chunk::Chunk;
    ///
    /// let mut chunk = Chunk::new();
    /// assert_eq!(chunk.len(), 0);
    ///
    /// assert!(chunk.push_front(42));
    /// assert_eq!(chunk.len(), 1);
    /// assert_eq!(chunk.get(0), Some(&42));
    /// ```
    #[inline]
    pub fn push_front(&mut self, value: T) -> bool {
        if self.is_full() {
            return false;
        }
        self.elements.insert(0, value);
        true
    }

    /// Remove and return the last element from the chunk.
    ///
    /// Returns `None` if the chunk is empty.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::chunk::Chunk;
    ///
    /// let mut chunk = Chunk::new();
    /// chunk.push_back(42);
    /// assert_eq!(chunk.pop_back(), Some(42));
    /// assert_eq!(chunk.pop_back(), None);
    /// ```
    #[inline]
    pub fn pop_back(&mut self) -> Option<T> {
        self.elements.pop()
    }

    /// Remove and return the first element from the chunk.
    ///
    /// Returns `None` if the chunk is empty.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::chunk::Chunk;
    ///
    /// let mut chunk = Chunk::new();
    /// chunk.push_front(42);
    /// assert_eq!(chunk.pop_front(), Some(42));
    /// assert_eq!(chunk.pop_front(), None);
    /// ```
    #[inline]
    pub fn pop_front(&mut self) -> Option<T> {
        if self.is_empty() {
            None
        } else {
            Some(self.elements.remove(0))
        }
    }

    /// Insert an element at the specified index.
    ///
    /// Returns false if the chunk is already full.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::chunk::Chunk;
    ///
    /// let mut chunk = Chunk::new();
    /// assert_eq!(chunk.len(), 0);
    ///
    /// assert!(chunk.insert(0, 42));
    /// assert_eq!(chunk.len(), 1);
    /// assert_eq!(chunk.get(0), Some(&42));
    /// ```
    #[inline]
    pub fn insert(&mut self, index: usize, value: T) -> bool {
        if self.is_full() {
            return false;
        }

        if index > self.elements.len() {
            return false;
        }

        self.elements.insert(index, value);
        true
    }

    /// Remove and return the element at the specified index.
    ///
    /// Returns `None` if the index is out of bounds.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::chunk::Chunk;
    ///
    /// let mut chunk = Chunk::new();
    /// chunk.push_back(42);
    /// assert_eq!(chunk.remove(0), Some(42));
    /// assert_eq!(chunk.remove(0), None); // Out of bounds
    /// ```
    #[inline]
    pub fn remove(&mut self, index: usize) -> Option<T> {
        if index >= self.elements.len() {
            None
        } else {
            Some(self.elements.remove(index))
        }
    }

    /// Split the chunk at the specified index.
    ///
    /// Returns a new chunk containing all elements from the given index onwards.
    /// Those elements are removed from the original chunk.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::chunk::Chunk;
    ///
    /// let mut chunk = Chunk::new();
    /// chunk.push_back(1);
    /// chunk.push_back(2);
    /// chunk.push_back(3);
    ///
    /// let right = chunk.split_off(1);
    /// assert_eq!(chunk.len(), 1);
    /// assert_eq!(right.len(), 2);
    /// assert_eq!(chunk.get(0), Some(&1));
    /// assert_eq!(right.get(0), Some(&2));
    /// ```
    #[inline]
    pub fn split_off(&mut self, index: usize) -> Self {
        if index >= self.elements.len() {
            return Self::new();
        }

        let right_elements = self.elements.split_off(index);
        Self {
            elements: right_elements,
        }
    }

    /// Append the contents of another chunk to this one.
    ///
    /// Only appends as many elements as will fit in this chunk.
    /// Returns the number of elements that were appended.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::chunk::Chunk;
    ///
    /// let mut chunk = Chunk::new();
    /// chunk.push_back(1);
    /// chunk.push_back(2);
    ///
    /// let mut other = Chunk::new();
    /// other.push_back(3);
    /// other.push_back(4);
    ///
    /// let appended = chunk.append(&mut other);
    /// assert_eq!(appended, 2);
    /// assert_eq!(chunk.len(), 4);
    /// assert_eq!(other.len(), 0);
    /// ```
    pub fn append(&mut self, other: &mut Chunk<T>) -> usize {
        let space_available = CHUNK_SIZE - self.elements.len();
        if space_available == 0 {
            return 0;
        }

        let elements_to_take = min(space_available, other.len());
        let drain_range = 0..elements_to_take;

        // Use drain to efficiently move elements from other to self
        self.elements.extend(other.elements.drain(drain_range));

        elements_to_take
    }

    /// Get a slice of the underlying elements.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::chunk::Chunk;
    ///
    /// let mut chunk = Chunk::new();
    /// chunk.push_back(1);
    /// chunk.push_back(2);
    ///
    /// let slice = chunk.as_slice();
    /// assert_eq!(slice, &[1, 2]);
    /// ```
    #[inline]
    pub fn as_slice(&self) -> &[T] {
        &self.elements
    }

    /// Get a mutable slice of the underlying elements.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::chunk::Chunk;
    ///
    /// let mut chunk = Chunk::new();
    /// chunk.push_back(1);
    /// chunk.push_back(2);
    ///
    /// let mut slice = chunk.as_mut_slice();
    /// slice[0] = 3;
    /// assert_eq!(slice, &[3, 2]);
    /// ```
    #[inline]
    pub fn as_mut_slice(&mut self) -> &mut [T] {
        &mut self.elements
    }
}

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
