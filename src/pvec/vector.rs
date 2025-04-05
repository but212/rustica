//! Persistent Vector Implementation
//!
//! This module defines the `PersistentVector` type, which provides a high-level
//! interface for the persistent vector data structure. It is implemented using
//! a Relaxed Radix Balanced (RRB) tree for efficient operations.
//!
//! A persistent vector is an immutable data structure that provides efficient
//! random access, updates, and structural modifications. All operations create
//! a new version of the vector without modifying the original, allowing for
//! efficient structural sharing between different versions.
//!
//! # Examples
//!
//! ```
//! use rustica::pvec::PersistentVector;
//! use rustica::pvec::pvec;
//!
//! // Create a new vector
//! let mut vec = PersistentVector::<i32>::new();
//!
//! // Add elements to the vector
//! let vec = vec.push_back(10);
//! let vec = vec.push_back(20);
//! let vec = vec.push_back(30);
//!
//! // Access elements
//! assert_eq!(vec.get(1), Some(&20));
//! assert_eq!(vec.len(), 3);
//!
//! // Update an element
//! let updated_vec = vec.update(1, 25);
//! assert_eq!(updated_vec.get(1), Some(&25));
//!
//! // The original vector is unchanged
//! assert_eq!(vec.get(1), Some(&20));
//!
//! // Use the convenience macro
//! let vec = pvec![1, 2, 3, 4, 5];
//! assert_eq!(vec.len(), 5);
//! ```

use std::fmt::{self, Debug};
use std::iter::FromIterator;
use std::ops::Index;
use std::sync::Arc;
use std::vec::Vec as StdVec;

use super::iterator::{ChunksIter, IntoIter, Iter, SortedIter};
use super::memory::MemoryManager;
use super::tree::Tree;

/// A persistent vector implemented using a Relaxed Radix Balanced (RRB) tree.
///
/// This provides a high-level interface for working with the persistent vector,
/// with operations that are more familiar to users of standard vector types.
#[repr(transparent)]
#[derive(Clone)]
pub struct PersistentVector<T: Clone> {
    /// The underlying tree data structure
    tree: Tree<T>,
}

impl<T: Clone> PersistentVector<T> {
    /// Creates a new, empty persistent vector.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::PersistentVector;
    ///
    /// let vec: PersistentVector<i32> = PersistentVector::new();
    /// assert_eq!(vec.len(), 0);
    /// assert!(vec.is_empty());
    /// ```
    #[inline]
    pub fn new() -> Self {
        Self { tree: Tree::new() }
    }

    /// Clears the vector, removing all elements and returning an empty vector.
    ///
    /// This operation creates a new empty vector without modifying the original one.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::PersistentVector;
    ///
    /// let vec = PersistentVector::from_slice(&[1, 2, 3]);
    /// let empty = vec.clear();
    /// assert!(empty.is_empty());
    /// assert_eq!(vec.len(), 3); // Original is unchanged
    /// ```
    #[inline]
    pub fn clear(&self) -> Self {
        Self {
            tree: self.tree.clear(),
        }
    }

    /// Creates a new persistent vector with a single element.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::PersistentVector;
    ///
    /// let vec = PersistentVector::unit(42);
    /// assert_eq!(vec.len(), 1);
    /// assert_eq!(vec.get(0), Some(&42));
    /// ```
    #[inline]
    pub fn unit(value: T) -> Self {
        Self {
            tree: Tree::unit(value),
        }
    }

    /// Creates a new persistent vector from a slice of elements.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::PersistentVector;
    ///
    /// let data = vec![1, 2, 3, 4, 5];
    /// let vec = PersistentVector::from_slice(&data);
    /// assert_eq!(vec.len(), 5);
    /// assert_eq!(vec.get(2), Some(&3));
    /// ```
    #[inline]
    pub fn from_slice(slice: &[T]) -> Self {
        Self {
            tree: Tree::from_slice(slice),
        }
    }

    /// Returns the number of elements in the vector.
    ///
    /// This operation is O(1) as the size is cached at the tree level.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::PersistentVector;
    ///
    /// let vec = PersistentVector::from_slice(&[1, 2, 3]);
    /// assert_eq!(vec.len(), 3);
    /// ```
    #[inline]
    pub const fn len(&self) -> usize {
        self.tree.len()
    }

    /// Returns true if the vector contains no elements.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::PersistentVector;
    ///
    /// let vec: PersistentVector<i32> = PersistentVector::new();
    /// assert!(vec.is_empty());
    ///
    /// let vec = PersistentVector::unit(42);
    /// assert!(!vec.is_empty());
    /// ```
    #[inline]
    pub const fn is_empty(&self) -> bool {
        self.tree.is_empty()
    }

    /// Returns a reference to the element at the specified index, or None if the index is out of bounds.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::PersistentVector;
    ///
    /// let vec = PersistentVector::from_slice(&[10, 20, 30]);
    /// assert_eq!(vec.get(1), Some(&20));
    /// assert_eq!(vec.get(5), None); // Out of bounds
    /// ```
    #[inline]
    pub fn get(&self, index: usize) -> Option<&T> {
        self.tree.get(index)
    }

    /// Creates a new vector containing elements from a range of the original vector.
    ///
    /// Returns a new vector containing elements from index `start` (inclusive) to
    /// index `end` (exclusive). If `start` is greater than or equal to `end`, or
    /// if `start` is greater than or equal to the vector's length, an empty vector
    /// is returned.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::PersistentVector;
    ///
    /// let vec = PersistentVector::from_slice(&[1, 2, 3, 4, 5]);
    /// let sliced = vec.slice(1, 4);
    /// assert_eq!(sliced.len(), 3);
    /// assert_eq!(sliced.get(0), Some(&2));
    /// assert_eq!(sliced.get(2), Some(&4));
    /// assert_eq!(vec.len(), 5); // Original unchanged
    /// ```
    #[inline]
    pub fn slice(&self, start: usize, end: usize) -> Self {
        Self {
            tree: self.tree.slice(start, end),
        }
    }

    /// Returns a new vector with the given element appended to the end.
    ///
    /// This is an alias for `push_back`.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::PersistentVector;
    ///
    /// let vec = PersistentVector::<i32>::new();
    /// let vec = vec.append(10);
    /// let vec = vec.append(20);
    /// assert_eq!(vec.len(), 2);
    /// assert_eq!(vec.get(1), Some(&20));
    /// ```
    #[inline]
    pub fn append(&self, value: T) -> Self {
        Self {
            tree: self.tree.append(value),
        }
    }

    /// Returns a new vector with the specified length.
    ///
    /// If the new length is greater than the current length, the vector is
    /// extended with copies of the provided value. If the new length is less
    /// than the current length, the vector is truncated.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::PersistentVector;
    ///
    /// let vec = PersistentVector::from_slice(&[1, 2, 3]);
    ///
    /// // Extend the vector
    /// let extended = vec.resize(5, 0);
    /// assert_eq!(extended.len(), 5);
    /// assert_eq!(extended.get(3), Some(&0));
    ///
    /// // Truncate the vector
    /// let truncated = vec.resize(2, 0);
    /// assert_eq!(truncated.len(), 2);
    /// assert_eq!(truncated.get(2), None);
    /// ```
    #[inline]
    pub fn resize(&self, new_len: usize, value: T) -> Self {
        Self {
            tree: self.tree.resize(new_len, value),
        }
    }

    /// Returns a new vector with the element at the specified index removed.
    ///
    /// If the index is out of bounds, returns a copy of the original vector unchanged.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::PersistentVector;
    ///
    /// let vec = PersistentVector::from_slice(&[10, 20, 30, 40]);
    /// let new_vec = vec.remove(1);
    /// assert_eq!(new_vec.len(), 3);
    /// assert_eq!(new_vec.get(0), Some(&10));
    /// assert_eq!(new_vec.get(1), Some(&30));
    /// assert_eq!(new_vec.get(2), Some(&40));
    /// ```
    #[inline]
    pub fn remove(&self, index: usize) -> Self {
        Self {
            tree: self.tree.remove(index),
        }
    }

    /// Returns a new vector truncated to the specified length.
    ///
    /// If the new length is less than the current length, the vector is truncated.
    /// If the new length is greater than or equal to the current length, the vector is unchanged.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::PersistentVector;
    ///
    /// let vec = PersistentVector::from_slice(&[1, 2, 3, 4, 5]);
    /// let truncated = vec.truncate(3);
    /// assert_eq!(truncated.len(), 3);
    /// assert_eq!(truncated.get(2), Some(&3));
    /// assert_eq!(truncated.get(3), None);
    /// assert_eq!(vec.len(), 5); // Original unchanged
    /// ```
    #[inline]
    pub fn truncate(&self, new_len: usize) -> Self {
        Self {
            tree: self.tree.truncate(new_len),
        }
    }

    /// Returns a new vector with elements in the specified range removed.
    ///
    /// This creates a new vector with all elements from the original vector except those in the range
    /// from `start` (inclusive) to `end` (exclusive). If the range is invalid (e.g., `start` > `end` or
    /// the range is out of bounds), the original vector is returned unchanged.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::PersistentVector;
    ///
    /// let vec = PersistentVector::from_slice(&[1, 2, 3, 4, 5]);
    /// let new_vec = vec.drain(1, 3);
    /// assert_eq!(new_vec.len(), 3);
    /// assert_eq!(new_vec.get(0), Some(&1));
    /// assert_eq!(new_vec.get(1), Some(&4));
    /// assert_eq!(new_vec.get(2), Some(&5));
    /// assert_eq!(vec.len(), 5); // Original unchanged
    /// ```
    #[inline]
    pub fn drain(&self, start: usize, end: usize) -> Self {
        Self {
            tree: self.tree.drain(start, end),
        }
    }

    /// Returns a new vector with all elements from the provided iterator appended to the end.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::PersistentVector;
    ///
    /// let vec = PersistentVector::from_slice(&[1, 2, 3]);
    /// let extended = vec.extend(vec![4, 5, 6]);
    /// assert_eq!(extended.len(), 6);
    /// assert_eq!(extended.get(5), Some(&6));
    /// assert_eq!(vec.len(), 3); // Original unchanged
    /// ```
    #[inline]
    pub fn extend(&self, values: impl IntoIterator<Item = T>) -> Self {
        Self {
            tree: self.tree.extend(values),
        }
    }

    /// Returns a new vector with the element at the specified index updated to the given value.
    ///
    /// Returns a clone of the original vector if the index is out of bounds.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::PersistentVector;
    ///
    /// let vec = PersistentVector::from_slice(&[10, 20, 30]);
    /// let updated_vec = vec.update(1, 25);
    /// assert_eq!(updated_vec.get(1), Some(&25));
    /// assert_eq!(vec.get(1), Some(&20)); // Original unchanged
    /// ```
    #[inline]
    pub fn update(&self, index: usize, value: T) -> Self {
        Self {
            tree: self.tree.update(index, value),
        }
    }

    /// Returns a new vector with the given element appended to the end.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::PersistentVector;
    ///
    /// let vec = PersistentVector::<i32>::new();
    /// let vec = vec.push_back(10);
    /// let vec = vec.push_back(20);
    /// assert_eq!(vec.len(), 2);
    /// assert_eq!(vec.get(1), Some(&20));
    /// ```
    #[inline]
    pub fn push_back(&self, value: T) -> Self {
        Self {
            tree: self.tree.push_back(value),
        }
    }

    /// Returns a tuple containing a new vector with the last element removed and the removed element,
    /// or None if the vector is empty.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::PersistentVector;
    ///
    /// let vec = PersistentVector::from_slice(&[10, 20, 30, 40, 50]);
    /// let (new_vec, element) = vec.pop_back().unwrap();
    /// assert_eq!(element, 50);
    /// assert_eq!(new_vec.len(), 4);
    /// ```
    #[inline]
    pub fn pop_back(&self) -> Option<(Self, T)> {
        self.tree
            .pop_back()
            .map(|(tree, value)| (Self { tree }, value))
    }

    /// Sets the memory manager for this vector.
    ///
    /// This can be used to customize how memory is allocated and recycled
    /// for vector operations.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::PersistentVector;
    /// use rustica::pvec::MemoryManager;
    /// use rustica::pvec::memory::AllocationStrategy;
    ///
    /// let mut vec: PersistentVector<i32> = PersistentVector::new();
    /// let manager = MemoryManager::new(AllocationStrategy::Direct);
    /// vec.set_memory_manager(manager);
    /// ```
    #[inline]
    pub fn set_memory_manager(&mut self, manager: MemoryManager<T>) {
        self.tree.set_memory_manager(manager);
    }

    /// Returns a new vector with all elements in reverse order.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::PersistentVector;
    ///
    /// let vec = PersistentVector::from_slice(&[1, 2, 3, 4]);
    /// let reversed = vec.reverse();
    /// assert_eq!(reversed.len(), 4);
    /// assert_eq!(reversed.get(0), Some(&4));
    /// assert_eq!(reversed.get(1), Some(&3));
    /// assert_eq!(reversed.get(2), Some(&2));
    /// assert_eq!(reversed.get(3), Some(&1));
    /// ```
    #[inline]
    pub fn reverse(&self) -> Self {
        Self {
            tree: self.tree.reverse(),
        }
    }

    /// Converts this vector to an `Arc<PersistentVector<T>>`.
    ///
    /// This is useful when you want to share the vector across multiple
    /// threads or owners, while preserving its immutable nature.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::PersistentVector;
    /// use std::sync::Arc;
    ///
    /// let vec = PersistentVector::from_slice(&[1, 2, 3]);
    /// let arc_vec = vec.to_arc();
    /// assert_eq!(arc_vec.len(), 3);
    /// ```
    #[inline]
    pub fn to_arc(self) -> Arc<Self> {
        Arc::new(self)
    }

    /// Returns an iterator over the elements of the vector.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::PersistentVector;
    ///
    /// let vec = PersistentVector::from_slice(&[1, 2, 3]);
    /// let mut sum = 0;
    /// for &x in vec.iter() {
    ///     sum += x;
    /// }
    /// assert_eq!(sum, 6);
    /// ```
    #[inline]
    pub fn iter(&self) -> Iter<'_, T> {
        Iter::new(self)
    }

    /// Returns an iterator that yields chunks of elements.
    ///
    /// This is useful for efficiently processing large vectors in parallel.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::PersistentVector;
    ///
    /// let vec = PersistentVector::from_slice(&[1, 2, 3, 4, 5, 6, 7, 8]);
    /// let chunks: Vec<Vec<i32>> = vec.chunks().collect();
    /// // The exact chunking depends on the implementation details,
    /// // but we should have at least one chunk
    /// assert!(!chunks.is_empty());
    /// ```
    #[inline]
    pub fn chunks(&self) -> ChunksIter<'_, T> {
        ChunksIter::with_default_sizes(self)
    }

    /// Returns an iterator that yields elements in sorted order.
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
    #[inline]
    pub fn sorted(&self) -> SortedIter<'_, T>
    where
        T: Ord,
    {
        SortedIter::new(self)
    }

    /// Converts this persistent vector to a standard `Vec`.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::PersistentVector;
    ///
    /// let pvec = PersistentVector::from_slice(&[1, 2, 3]);
    /// let std_vec = pvec.to_vec();
    /// assert_eq!(std_vec, vec![1, 2, 3]);
    /// ```
    #[inline]
    pub fn to_vec(&self) -> StdVec<T> {
        self.iter().cloned().collect()
    }

    /// Gets a chunk of elements starting at the specified index.
    ///
    /// This method is primarily used by the chunk iterator implementation.
    ///
    /// # Parameters
    ///
    /// - `start_index`: The index to start extracting elements from
    /// - `min_size`: The minimum chunk size to extract
    /// - `max_size`: The maximum chunk size to extract
    ///
    /// # Returns
    ///
    /// A vector containing the elements in the specified range,
    /// with size between min_size and max_size (inclusive).
    pub(crate) fn get_chunk(
        &self,
        start_index: usize,
        min_size: usize,
        max_size: usize,
    ) -> StdVec<T> {
        if start_index >= self.len() {
            return StdVec::new();
        }

        // Calculate the actual chunk size based on min_size, max_size, and remaining elements
        let remaining = self.len() - start_index;
        let chunk_size = remaining.min(max_size).max(min_size).min(remaining);

        // Collect the elements into a vector
        let mut result = StdVec::with_capacity(chunk_size);
        for i in 0..chunk_size {
            if let Some(element) = self.get(start_index + i) {
                result.push(element.clone());
            } else {
                break;
            }
        }

        result
    }

    /// Splits the vector into two parts at the given index.
    ///
    /// Returns a tuple containing two vectors: the first with elements from `0..index`,
    /// and the second with elements from `index..len`.
    ///
    /// If `index` is greater than or equal to the length, the first vector will contain
    /// all elements and the second will be empty. If `index` is 0, the first vector
    /// will be empty and the second will contain all elements.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::PersistentVector;
    ///
    /// let vec = PersistentVector::from_slice(&[1, 2, 3, 4, 5]);
    /// let (left, right) = vec.split_at(2);
    ///
    /// assert_eq!(left.len(), 2);
    /// assert_eq!(right.len(), 3);
    /// assert_eq!(left.get(0), Some(&1));
    /// assert_eq!(right.get(0), Some(&3));
    /// ```
    #[inline]
    pub fn split_at(&self, index: usize) -> (Self, Self) {
        if index >= self.len() {
            return (self.clone(), Self { tree: Tree::new() });
        }

        if index == 0 {
            return (Self { tree: Tree::new() }, self.clone());
        }

        let (left_tree, right_tree) = self.tree.split_at(index);
        (Self { tree: left_tree }, Self { tree: right_tree })
    }

    /// Returns a new vector containing the elements from `start` to `end` (exclusive).
    ///
    /// This method is an alias for `slice` that provides a more familiar name for users
    /// coming from other vector implementations.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::PersistentVector;
    ///
    /// let vec = PersistentVector::from_slice(&[1, 2, 3, 4, 5]);
    /// let sub = vec.subvec(1, 4);
    ///
    /// assert_eq!(sub.len(), 3);
    /// assert_eq!(sub.get(0), Some(&2));
    /// assert_eq!(sub.get(2), Some(&4));
    /// ```
    #[inline]
    pub fn subvec(&self, start: usize, end: usize) -> Self {
        self.slice(start, end)
    }

    /// Rotates the vector to the left by one position.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::PersistentVector;
    ///
    /// let vec = PersistentVector::from_slice(&[1, 2, 3, 4]);
    /// let rotated = vec.rotate_left();
    /// assert_eq!(rotated.len(), 4);
    /// assert_eq!(rotated.get(0), Some(&2));
    /// assert_eq!(rotated.get(1), Some(&3));
    /// assert_eq!(rotated.get(2), Some(&4));
    /// assert_eq!(rotated.get(3), Some(&1));
    /// ```
    #[inline]
    pub fn rotate_left(&self) -> Self {
        Self {
            tree: self.tree.rotate_left(),
        }
    }

    /// Rotates the vector to the right by one position.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::PersistentVector;
    ///
    /// let vec = PersistentVector::from_slice(&[1, 2, 3, 4]);
    /// let rotated = vec.rotate_right();
    /// assert_eq!(rotated.len(), 4);
    /// assert_eq!(rotated.get(0), Some(&4));
    /// assert_eq!(rotated.get(1), Some(&1));
    /// assert_eq!(rotated.get(2), Some(&2));
    /// assert_eq!(rotated.get(3), Some(&3));
    /// ```
    #[inline]
    pub fn rotate_right(&self) -> Self {
        Self {
            tree: self.tree.rotate_right(),
        }
    }

    /// Returns true if the vector contains an element equal to the given value.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::PersistentVector;
    ///
    /// let vec = PersistentVector::from_slice(&[1, 2, 3, 4, 5]);
    /// assert!(vec.contains(3));
    /// assert!(!vec.contains(10));
    /// ```
    #[inline]
    pub fn contains(&self, value: T) -> bool
    where
        T: PartialEq,
    {
        self.iter().any(|x| x == &value)
    }

    /// Returns the first element that matches the given predicate, or None if no such element exists.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::PersistentVector;
    ///
    /// let vec = PersistentVector::from_slice(&[1, 2, 3, 4, 5]);
    /// assert_eq!(vec.find(|x| x % 2 == 0), Some(&2));
    /// assert_eq!(vec.find(|x| *x > 5), None);
    /// ```
    #[inline]
    pub fn find<P>(&self, predicate: P) -> Option<&T>
    where
        P: Fn(&T) -> bool,
    {
        self.iter().find(|x| predicate(x))
    }

    /// Returns the first index at which a given element can be found in the vector, or None if it is not present.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::PersistentVector;
    ///
    /// let vec = PersistentVector::from_slice(&[1, 2, 3, 4, 5]);
    /// assert_eq!(vec.position(|x| x % 2 == 0), Some(1));
    /// assert_eq!(vec.position(|x| *x > 5), None);
    /// ```
    #[inline]
    pub fn position<P>(&self, predicate: P) -> Option<usize>
    where
        P: Fn(&T) -> bool,
    {
        self.iter().position(predicate)
    }

    /// Returns the last index at which a given element can be found in the vector, or None if it is not present.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::PersistentVector;
    ///
    /// let vec = PersistentVector::from_slice(&[1, 2, 3, 4, 5]);
    /// assert_eq!(vec.rposition(|x| x % 2 == 0), Some(3));
    /// assert_eq!(vec.rposition(|x| *x > 5), None);
    /// ```
    #[inline]
    pub fn rposition<P>(&self, predicate: P) -> Option<usize>
    where
        P: Fn(&T) -> bool,
    {
        self.iter().rposition(predicate)
    }

    /// Performs a binary search on the vector to find the index of a given element.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::PersistentVector;
    ///
    /// let vec = PersistentVector::from_slice(&[1, 2, 3, 4, 5]);
    /// assert_eq!(vec.binary_search(&3), Ok(2));
    /// assert_eq!(vec.binary_search(&6), Err(5));
    /// ```
    #[inline]
    pub fn binary_search(&self, x: &T) -> Result<usize, usize>
    where
        T: Ord,
    {
        if self.is_empty() {
            return Err(0);
        }

        let mut low = 0;
        let mut high = self.len() - 1;

        while low <= high {
            let mid = low + (high - low) / 2;
            match self.get(mid).unwrap().cmp(x) {
                std::cmp::Ordering::Equal => return Ok(mid),
                std::cmp::Ordering::Greater => {
                    if mid == 0 {
                        return Err(0);
                    }
                    high = mid - 1;
                }
                std::cmp::Ordering::Less => low = mid + 1,
            }
        }

        Err(low)
    }

    /// Returns `true` if the vector is sorted.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::PersistentVector;
    ///
    /// let vec = PersistentVector::from_slice(&[1, 2, 3, 4, 5]);
    /// assert!(vec.is_sorted());
    ///
    /// let vec = PersistentVector::from_slice(&[5, 3, 1, 4, 2]);
    /// assert!(!vec.is_sorted());
    /// ```
    #[inline]
    pub fn is_sorted(&self) -> bool
    where
        T: Ord,
    {
        self.iter().is_sorted()
    }

    /// Removes consecutive duplicate elements from the vector.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::PersistentVector;
    ///
    /// let vec = PersistentVector::from_slice(&[1, 2, 2, 3, 3, 3, 4]);
    /// let deduped = vec.dedup();
    /// assert_eq!(deduped.len(), 4);
    /// assert_eq!(deduped.get(0), Some(&1));
    /// assert_eq!(deduped.get(1), Some(&2));
    /// assert_eq!(deduped.get(2), Some(&3));
    /// assert_eq!(deduped.get(3), Some(&4));
    /// ```
    pub fn dedup(&self) -> PersistentVector<T>
    where
        T: PartialEq,
    {
        if self.len() <= 1 {
            return self.clone();
        }

        let mut result = PersistentVector::new();
        let mut prev: Option<&T> = None;

        for item in self.iter() {
            if prev != Some(item) {
                result = result.push_back(item.clone());
                prev = Some(item);
            }
        }

        result
    }

    /// Creates a new vector by zipping this vector with another iterable collection.
    ///
    /// The returned vector contains pairs of elements from this vector and the provided iterable.
    /// The length of the result is the minimum of the lengths of the two inputs.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::PersistentVector;
    ///
    /// let vec1 = PersistentVector::from_slice(&[1, 2, 3]);
    /// let vec2 = vec!['a', 'b', 'c'];
    /// let zipped = vec1.zip(vec2);
    /// assert_eq!(zipped.get(0), Some(&(1, 'a')));
    /// assert_eq!(zipped.get(1), Some(&(2, 'b')));
    /// assert_eq!(zipped.get(2), Some(&(3, 'c')));
    /// ```
    pub fn zip<U, I: IntoIterator<Item = U>>(&self, other: I) -> PersistentVector<(T, U)>
    where
        T: Clone,
        U: Clone,
    {
        let mut result = PersistentVector::new();
        let iter = self.iter().zip(other);

        for (a, b) in iter {
            result = result.push_back((a.clone(), b));
        }

        result
    }

    /// Partitions the vector into two vectors based on a predicate.
    ///
    /// Returns a tuple of two vectors: the first containing elements that satisfy the predicate,
    /// and the second containing elements that don't satisfy the predicate.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::PersistentVector;
    ///
    /// let vec = PersistentVector::from_slice(&[1, 2, 3, 4, 5]);
    /// let (evens, odds) = vec.partition(|&x| x % 2 == 0);
    /// assert_eq!(evens.to_vec(), vec![2, 4]);
    /// assert_eq!(odds.to_vec(), vec![1, 3, 5]);
    /// ```
    pub fn partition<F: Fn(&T) -> bool>(
        &self,
        predicate: F,
    ) -> (PersistentVector<T>, PersistentVector<T>)
    where
        T: Clone,
    {
        let mut true_vec = PersistentVector::new();
        let mut false_vec = PersistentVector::new();

        for item in self.iter() {
            if predicate(item) {
                true_vec = true_vec.push_back(item.clone());
            } else {
                false_vec = false_vec.push_back(item.clone());
            }
        }

        (true_vec, false_vec)
    }

    /// Performs a scan operation on the vector.
    ///
    /// The scan operation applies a function to each element of the vector and accumulates the result.
    /// The initial value is used as the first accumulator value.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::PersistentVector;
    ///
    /// let vec = PersistentVector::from_slice(&[1, 2, 3, 4, 5]);
    /// let scan_result = vec.scan(0, |acc, &x| acc + x);
    /// assert_eq!(scan_result.to_vec(), vec![0, 1, 3, 6, 10, 15]);
    /// ```
    pub fn scan<F: Fn(T, &T) -> T>(&self, initial: T, f: F) -> PersistentVector<T>
    where
        T: Clone,
    {
        let mut result = PersistentVector::new();
        result = result.push_back(initial.clone());

        let mut acc = initial;
        for item in self.iter() {
            acc = f(acc, item);
            result = result.push_back(acc.clone());
        }

        result
    }

    /// Performs a scan operation (also known as inclusive prefix sum) on the vector.
    ///
    /// The scan_left operation applies a function to each element of the vector and accumulates the result.
    /// Unlike `scan`, this version passes the accumulator as a reference to the function.
    /// The initial value is used as the first accumulator value.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::PersistentVector;
    ///
    /// let vec = PersistentVector::from_slice(&[1, 2, 3, 4, 5]);
    /// let scan_result = vec.scan_left(0, |acc, x| *acc + x);
    /// assert_eq!(scan_result.to_vec(), vec![0, 1, 3, 6, 10, 15]);
    /// ```
    pub fn scan_left<F: Fn(&T, T) -> T>(&self, initial: T, f: F) -> PersistentVector<T>
    where
        T: Clone,
    {
        let mut result = PersistentVector::new();
        result = result.push_back(initial.clone());

        let mut acc = initial;
        for item in self.iter() {
            acc = f(&acc, item.clone());
            result = result.push_back(acc.clone());
        }

        result
    }

    /// Performs a scan operation in reverse (right-to-left) on the vector.
    ///
    /// The scan_right operation applies a function to each element of the vector in reverse order
    /// and accumulates the result. The initial value is used as the first accumulator value.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::PersistentVector;
    ///
    /// let vec = PersistentVector::from_slice(&[1, 2, 3, 4, 5]);
    /// let scan_result = vec.scan_right(0, |acc, x| *acc + x);
    /// assert_eq!(scan_result.to_vec(), vec![0, 5, 9, 12, 14, 15]);
    /// ```
    pub fn scan_right<F: Fn(&T, T) -> T>(&self, initial: T, f: F) -> PersistentVector<T>
    where
        T: Clone,
    {
        let mut result = PersistentVector::new();
        result = result.push_back(initial.clone());

        let mut acc = initial;
        for item in self.iter().rev() {
            acc = f(&acc, item.clone());
            result = result.push_back(acc.clone());
        }

        result
    }

    /// Groups elements of the vector by a key function.
    ///
    /// This method applies the function `f` to each element to derive a key,
    /// then groups elements with the same key into separate vectors.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::PersistentVector;
    ///
    /// let vec = PersistentVector::from_slice(&[1, 2, 3, 4, 5, 6]);
    /// let groups = vec.group_by(|&x| x % 3); // Group by remainder when divided by 3
    ///
    /// // Convert result to standard Vec for easier testing
    /// let groups_vec: Vec<Vec<i32>> = groups
    ///     .iter()
    ///     .map(|group| group.iter().cloned().collect())
    ///     .collect();
    ///
    /// // Elements should be grouped by their remainder mod 3
    /// assert_eq!(groups_vec.len(), 3);
    /// ```
    pub fn group_by<F: Fn(&T) -> K, K: Clone + Eq + std::hash::Hash>(
        &self,
        f: F,
    ) -> PersistentVector<PersistentVector<T>>
    where
        T: Clone,
    {
        // First collect items into a HashMap of standard Vecs for efficient mutation
        let mut groups = std::collections::HashMap::<K, Vec<T>>::new();

        for item in self.iter() {
            let key = f(item);
            groups.entry(key).or_default().push(item.clone());
        }

        // Convert the final result to PersistentVectors in one go
        let mut result = PersistentVector::new();
        for (_, items) in groups {
            result = result.push_back(PersistentVector::from_iter(items));
        }

        result
    }

    /// Performs a left fold operation on the vector, using the provided initial value and function.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::PersistentVector;
    ///
    /// let vec = PersistentVector::from_slice(&[1, 2, 3, 4, 5]);
    /// let sum = vec.fold_left(0, |acc, &x| acc + x);
    /// assert_eq!(sum, 15);
    /// ```
    #[inline]
    pub fn fold_left<F: Fn(T, &T) -> T>(&self, initial: T, f: F) -> T
    where
        T: Clone,
    {
        self.iter().fold(initial, f)
    }

    /// Performs a right fold operation on the vector, using the provided initial value and function.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::PersistentVector;
    ///
    /// let vec = PersistentVector::from_slice(&[1, 2, 3, 4, 5]);
    /// let sum = vec.fold_right(0, |&x, acc| acc + x);
    /// assert_eq!(sum, 15);
    /// ```
    #[inline]
    pub fn fold_right<F: Fn(&T, T) -> T>(&self, initial: T, f: F) -> T
    where
        T: Clone,
    {
        let mut acc = initial;
        for item in self.iter().rev() {
            acc = f(item, acc);
        }
        acc
    }

    /// Flat maps each element in the vector using the given function.
    ///
    /// This method applies the function to each element in the vector, which produces an
    /// iterator for each element. Then it flattens all these iterators into a single vector.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::PersistentVector;
    ///
    /// let vec = PersistentVector::from_slice(&[1, 2, 3]);
    /// let result = vec.flat_map(|&x| vec![x, x * 10]);
    /// assert_eq!(result.to_vec(), vec![1, 10, 2, 20, 3, 30]);
    /// ```
    pub fn flat_map<I: IntoIterator<Item = T>, F: Fn(&T) -> I>(&self, f: F) -> PersistentVector<T> {
        let mut result = PersistentVector::new();
        for item in self.iter() {
            result = result.extend(f(item));
        }
        result
    }
}

impl<T: Clone> Default for PersistentVector<T> {
    /// Creates a new, empty persistent vector.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::PersistentVector;
    /// use std::default::Default;
    ///
    /// let vec: PersistentVector<i32> = Default::default();
    /// assert!(vec.is_empty());
    /// ```
    #[inline]
    fn default() -> Self {
        Self::new()
    }
}

impl<T: Clone + Debug> Debug for PersistentVector<T> {
    #[inline]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self.iter()).finish()
    }
}

impl<T: Clone> FromIterator<T> for PersistentVector<T> {
    /// Creates a persistent vector from an iterator.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::PersistentVector;
    /// use std::iter::FromIterator;
    ///
    /// let vec = PersistentVector::from_iter(vec![1, 2, 3, 4, 5]);
    /// assert_eq!(vec.len(), 5);
    /// assert_eq!(vec.get(2), Some(&3));
    /// ```
    #[inline]
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        Self {
            tree: Tree::from_iter(iter),
        }
    }
}

impl<T: Clone> IntoIterator for PersistentVector<T> {
    type Item = T;
    type IntoIter = IntoIter<T>;

    /// Creates a consuming iterator from a persistent vector.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::PersistentVector;
    ///
    /// let vec = PersistentVector::from_slice(&[1, 2, 3]);
    /// let sum: i32 = vec.into_iter().sum();
    /// assert_eq!(sum, 6);
    /// ```
    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        IntoIter::new(self)
    }
}

impl<'a, T: Clone> IntoIterator for &'a PersistentVector<T> {
    type Item = &'a T;
    type IntoIter = Iter<'a, T>;

    /// Creates a borrowing iterator from a reference to a persistent vector.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::PersistentVector;
    ///
    /// let vec = PersistentVector::from_slice(&[1, 2, 3]);
    /// let sum: i32 = (&vec).into_iter().fold(0, |acc, &x| acc + x);
    /// assert_eq!(sum, 6);
    /// ```
    #[inline]
    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<T: Clone> Index<usize> for PersistentVector<T> {
    type Output = T;

    /// Provides indexed access to the vector elements.
    ///
    /// # Panics
    ///
    /// Panics if the index is out of bounds.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::PersistentVector;
    ///
    /// let vec = PersistentVector::from_slice(&[10, 20, 30]);
    /// assert_eq!(vec[1], 20);
    /// ```
    #[inline]
    fn index(&self, index: usize) -> &Self::Output {
        self.get(index).expect("index out of bounds")
    }
}

// Additional helper methods to extend functionality

impl<T: Clone> PersistentVector<T> {
    /// Maps each element in the vector using the given function.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::PersistentVector;
    ///
    /// let vec = PersistentVector::from_slice(&[1, 2, 3]);
    /// let doubled = vec.map(|x| x * 2);
    /// assert_eq!(doubled.to_vec(), vec![2, 4, 6]);
    /// ```
    pub fn map<F, U>(&self, f: F) -> PersistentVector<U>
    where
        F: Fn(&T) -> U,
        U: Clone,
    {
        let mut buffer = Vec::with_capacity(self.len());
        for item in self.iter() {
            buffer.push(f(item));
        }
        PersistentVector::from_iter(buffer)
    }

    /// Filters elements in the vector keeping only those that satisfy the predicate.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::PersistentVector;
    ///
    /// let vec = PersistentVector::from_slice(&[1, 2, 3, 4, 5]);
    /// let evens = vec.filter(|&x| x % 2 == 0);
    /// assert_eq!(evens.to_vec(), vec![2, 4]);
    /// ```
    pub fn filter<F>(&self, predicate: F) -> PersistentVector<T>
    where
        F: Fn(&T) -> bool,
        T: Clone,
    {
        let mut buffer = Vec::with_capacity(self.len());
        for item in self.iter() {
            if predicate(item) {
                buffer.push(item.clone());
            }
        }
        PersistentVector::from_iter(buffer)
    }

    /// Returns the first element of the vector, or None if it's empty.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::PersistentVector;
    ///
    /// let vec = PersistentVector::from_slice(&[10, 20, 30]);
    /// assert_eq!(vec.first(), Some(&10));
    ///
    /// let empty: PersistentVector<i32> = PersistentVector::new();
    /// assert_eq!(empty.first(), None);
    /// ```
    pub fn first(&self) -> Option<&T> {
        self.get(0)
    }

    /// Returns the last element of the vector, or None if it's empty.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::PersistentVector;
    ///
    /// let vec = PersistentVector::from_slice(&[10, 20, 30]);
    /// assert_eq!(vec.last(), Some(&30));
    ///
    /// let empty: PersistentVector<i32> = PersistentVector::new();
    /// assert_eq!(empty.last(), None);
    /// ```
    pub fn last(&self) -> Option<&T> {
        if self.is_empty() {
            None
        } else {
            self.get(self.len() - 1)
        }
    }

    /// Concatenates two vectors, returning a new vector.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::PersistentVector;
    ///
    /// let vec1 = PersistentVector::from_slice(&[1, 2, 3]);
    /// let vec2 = PersistentVector::from_slice(&[4, 5, 6]);
    /// let combined = vec1.concat(&vec2);
    /// assert_eq!(combined.to_vec(), vec![1, 2, 3, 4, 5, 6]);
    /// ```
    #[inline]
    pub fn concat(&self, other: &Self) -> Self {
        self.extend(other.iter().cloned())
    }
}

impl<T: Clone> From<PersistentVector<T>> for Vec<T> {
    fn from(val: PersistentVector<T>) -> Self {
        val.to_vec()
    }
}

impl<T: Clone> From<Vec<T>> for PersistentVector<T> {
    fn from(val: Vec<T>) -> Self {
        val.into_iter().collect()
    }
}
