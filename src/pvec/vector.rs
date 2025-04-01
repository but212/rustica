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
    pub fn new() -> Self {
        Self { tree: Tree::new() }
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
    pub fn len(&self) -> usize {
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
    pub fn is_empty(&self) -> bool {
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
    pub fn get(&self, index: usize) -> Option<&T> {
        self.tree.get(index)
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
    pub fn append(&self, value: T) -> Self {
        Self {
            tree: self.tree.append(value),
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
    pub fn set_memory_manager(&mut self, manager: MemoryManager<T>) {
        self.tree.set_memory_manager(manager);
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
    fn default() -> Self {
        Self::new()
    }
}

impl<T: Clone + Debug> Debug for PersistentVector<T> {
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
        let mut result = PersistentVector::<U>::new();
        for item in self.iter() {
            result = result.push_back(f(item));
        }
        result
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
    {
        let mut result = PersistentVector::new();
        for item in self.iter() {
            if predicate(item) {
                result = result.push_back(item.clone());
            }
        }
        result
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
    pub fn concat(&self, other: &Self) -> Self {
        let mut result = self.clone();
        for item in other.iter() {
            result = result.push_back(item.clone());
        }
        result
    }
}

impl<T: Clone> From<PersistentVector<T>> for Vec<T> {
    fn from(val: PersistentVector<T>) -> Self {
        val.to_vec()
    }
}
