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

use super::iterator::{ChunksIter, Iter, SortedIter};
use super::tree::Tree;

/// A persistent vector implemented using a Relaxed Radix Balanced (RRB) tree.
///
/// This immutable data structure provides efficient operations with structural sharing
/// between versions. All operations create a new vector without modifying the original,
/// making it ideal for functional programming patterns and concurrent applications.
///
/// # Performance
///
/// - Random access: O(log n)
/// - Updates: O(log n)
/// - Push/pop: O(1) amortized
/// - Small vectors use an optimized representation for better memory efficiency
///
/// # Examples
///
/// ```
/// use rustica::pvec;
///
/// let vec1 = pvec![1, 2, 3];
/// let vec2 = vec1.push_back(4);
///
/// // Original vector is unchanged
/// assert_eq!(vec1.len(), 3);
/// assert_eq!(vec2.len(), 4);
/// ```
#[repr(transparent)]
#[derive(Clone, PartialEq, Eq)]
pub struct PersistentVector<T> {
    /// The underlying implementation
    inner: VectorImpl<T>,
}

/// Optimized implementation for persistent vectors
///
/// This enum provides two different storage strategies:
/// - Small vectors (≤ SMALL_VECTOR_SIZE) use an optimized inline representation
/// - Larger vectors use the full RRB tree structure
///
/// The small vector optimization avoids the overhead of tree structures
/// for collections with few elements, improving both memory usage and
/// performance for common cases.
#[derive(Clone, PartialEq, Eq)]
pub(crate) enum VectorImpl<T> {
    /// Optimized storage for small vectors, using a fixed-size array
    Small {
        /// Direct inline storage of elements
        elements: SmallVec<T>,
    },
    /// Full tree structure for larger vectors
    Tree {
        /// The underlying tree data structure
        tree: Tree<T>,
    },
}

/// Maximum number of elements that can be stored directly in a small vector.
///
/// This constant defines the threshold at which vectors switch from the small
/// vector optimization to the full tree representation. The value is chosen
/// to balance memory usage with performance for common use cases.
const SMALL_VECTOR_SIZE: usize = 8;

/// A small vector implementation with inline storage to avoid heap allocations.
///
/// This optimized vector stores elements directly in an array rather than using
/// the full tree structure, improving performance and memory usage for vectors
/// with few elements.
///
/// The implementation uses `Option<T>` for each slot to allow for efficient
/// initialization without requiring `T` to implement `Default`.
#[derive(Clone, PartialEq, Eq)]
pub(crate) struct SmallVec<T> {
    /// The elements stored inline in a fixed-size array
    elements: [Option<T>; SMALL_VECTOR_SIZE],
    /// The number of elements currently stored in the vector
    len: usize,
}

impl<T: Clone> SmallVec<T> {
    /// Creates a new, empty SmallVec
    #[inline(always)]
    #[must_use]
    pub fn new() -> Self {
        Self {
            elements: Self::none_array(),
            len: 0,
        }
    }

    fn none_array() -> [Option<T>; SMALL_VECTOR_SIZE] {
        std::array::from_fn(|_| None)
    }

    /// Returns a reference to the element at the given index, or None if out of bounds
    #[inline(always)]
    #[must_use]
    pub fn get(&self, index: usize) -> Option<&T> {
        if index < self.len {
            self.elements[index].as_ref()
        } else {
            None
        }
    }

    /// Returns the number of elements in the vector
    #[inline(always)]
    #[must_use]
    pub fn len(&self) -> usize {
        self.len
    }

    /// Returns a new SmallVec with the given element appended
    #[inline(always)]
    #[must_use]
    pub fn push_back(&self, value: T) -> Self {
        let mut new = self.clone();
        if new.len < SMALL_VECTOR_SIZE {
            new.elements[new.len] = Some(value);
            new.len += 1;
        }
        new
    }

    /// Returns a new SmallVec with the element at the given index updated
    #[inline(always)]
    #[must_use]
    pub fn update(&self, index: usize, value: T) -> Self {
        let mut new = self.clone();
        if index < new.len {
            new.elements[index] = Some(value);
        }
        new
    }

    /// Convert to a standard Vec
    #[inline(always)]
    #[must_use]
    pub fn to_vec(&self) -> std::vec::Vec<T> {
        self.elements[..self.len].iter().filter_map(|x| x.clone()).collect()
    }
}

impl<T: Clone> Default for SmallVec<T> {
    #[inline(always)]
    fn default() -> Self {
        Self::new()
    }
}

impl<T: Clone> VectorImpl<T> {
    /// Creates a new, empty vector
    #[inline(always)]
    #[must_use]
    pub fn new() -> Self {
        VectorImpl::Small {
            elements: SmallVec::new(),
        }
    }

    /// Creates a unit vector with one element
    #[inline(always)]
    #[must_use]
    pub fn unit(value: T) -> Self {
        VectorImpl::Small {
            elements: SmallVec::new().push_back(value),
        }
    }

    /// Creates a vector from a slice of elements
    #[inline(always)]
    #[must_use]
    pub fn from_slice(slice: &[T]) -> Self {
        if slice.len() <= SMALL_VECTOR_SIZE {
            VectorImpl::Small {
                elements: {
                    let mut v = SmallVec::new();
                    for x in slice {
                        v = v.push_back(x.clone());
                    }
                    v
                },
            }
        } else {
            VectorImpl::Tree {
                tree: Tree::from_slice(slice),
            }
        }
    }

    /// Returns a reference to the element at the specified index, or None if the index is out of bounds.
    #[inline(always)]
    #[must_use]
    pub fn get(&self, index: usize) -> Option<&T> {
        match self {
            VectorImpl::Small { elements } => elements.get(index),
            VectorImpl::Tree { tree } => tree.get(index),
        }
    }

    /// Returns a new vector with the given element appended
    #[inline(always)]
    #[must_use]
    pub fn push_back(&self, value: T) -> Self {
        match self {
            VectorImpl::Small { elements } if elements.len() < SMALL_VECTOR_SIZE => {
                VectorImpl::Small {
                    elements: elements.push_back(value),
                }
            },
            VectorImpl::Small { elements } => {
                let mut v: Vec<T> = elements.to_vec();
                v.push(value);
                VectorImpl::Tree {
                    tree: Tree::from_slice(&v),
                }
            },
            VectorImpl::Tree { tree } => VectorImpl::Tree {
                tree: tree.push_back(value),
            },
        }
    }

    /// Returns a new vector with the element at the given index updated
    #[inline(always)]
    #[must_use]
    pub fn update(&self, index: usize, value: T) -> Self {
        match self {
            VectorImpl::Small { elements } => VectorImpl::Small {
                elements: elements.update(index, value),
            },
            VectorImpl::Tree { tree } => VectorImpl::Tree {
                tree: tree.update(index, value),
            },
        }
    }

    /// Convert to a standard Vec
    #[inline(always)]
    #[must_use]
    pub fn to_vec(&self) -> std::vec::Vec<T> {
        match self {
            VectorImpl::Small { elements } => elements.to_vec(),
            VectorImpl::Tree { tree } => tree.to_vec(),
        }
    }

    /// Returns a new vector with all elements from the provided iterator appended to the end.
    #[inline(always)]
    #[must_use]
    pub fn extend(&self, values: impl IntoIterator<Item = T>) -> Self {
        let mut result = self.clone();
        for v in values {
            result = result.push_back(v);
        }
        result
    }

    /// Removes the last element from the vector and returns it, along with the updated vector.
    #[inline(always)]
    #[must_use]
    pub fn pop_back(&self) -> Option<(Self, T)> {
        match self {
            VectorImpl::Small { elements } if elements.len() > 0 => {
                let mut v = elements.clone();
                let val = v.elements[v.len - 1].take().unwrap();
                v.len -= 1;
                Some((VectorImpl::Small { elements: v }, val))
            },
            VectorImpl::Tree { tree } => tree
                .pop_back()
                .map(|(new_tree, val)| (VectorImpl::Tree { tree: new_tree }, val)),
            _ => None,
        }
    }
}

impl<T: Clone> FromIterator<T> for VectorImpl<T> {
    #[inline(always)]
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        let mut v = VectorImpl::new();
        for item in iter {
            v = v.push_back(item);
        }
        v
    }
}

impl<T: Clone + Debug> Debug for VectorImpl<T> {
    #[inline(always)]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            VectorImpl::Small { elements } => f.debug_list().entries(elements.to_vec()).finish(),
            VectorImpl::Tree { tree } => tree.fmt(f),
        }
    }
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
    /// assert!(vec.is_empty());
    /// assert_eq!(vec.len(), 0);
    /// ```
    #[inline(always)]
    #[must_use]
    pub fn new() -> Self {
        Self {
            inner: VectorImpl::new(),
        }
    }

    /// Creates a new persistent vector containing a single element.
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
    #[inline(always)]
    #[must_use]
    pub fn unit(value: T) -> Self {
        Self {
            inner: VectorImpl::unit(value),
        }
    }

    /// Creates a new persistent vector from a slice of elements.
    ///
    /// This is an efficient way to create a vector with multiple initial elements.
    /// For small slices (≤ 8 elements), this uses an optimized storage representation.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::PersistentVector;
    ///
    /// let vec = PersistentVector::from_slice(&[1, 2, 3, 4]);
    /// assert_eq!(vec.len(), 4);
    /// assert_eq!(vec.get(2), Some(&3));
    /// ```
    #[inline(always)]
    #[must_use]
    pub fn from_slice(slice: &[T]) -> Self {
        Self {
            inner: VectorImpl::from_slice(slice),
        }
    }

    /// Returns the number of elements in the vector.
    ///
    /// This operation is O(1) as it simply returns the cached length value.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::PersistentVector;
    ///
    /// let vec = PersistentVector::from_slice(&[1, 2, 3, 4, 5]);
    /// assert_eq!(vec.len(), 5);
    /// ```
    #[inline(always)]
    #[must_use]
    pub fn len(&self) -> usize {
        match &self.inner {
            VectorImpl::Small { elements } => elements.len(),
            VectorImpl::Tree { tree } => tree.len(),
        }
    }

    /// Returns true if the vector contains no elements.
    ///
    /// This operation is O(1) as it simply checks the cached length value.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::PersistentVector;
    ///
    /// let empty: PersistentVector<i32> = PersistentVector::new();
    /// assert!(empty.is_empty());
    ///
    /// let non_empty = PersistentVector::unit(42);
    /// assert!(!non_empty.is_empty());
    /// ```
    #[inline(always)]
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Get a reference to the element at the specified index.
    ///
    /// Returns `None` if the index is out of bounds.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::PersistentVector;
    ///
    /// let vec = PersistentVector::from_slice(&[10, 20, 30, 40]);
    /// assert_eq!(vec.get(1), Some(&20));
    /// assert_eq!(vec.get(10), None);
    /// ```
    #[inline(always)]
    #[must_use]
    pub fn get(&self, index: usize) -> Option<&T> {
        self.inner.get(index)
    }

    /// Returns a new vector with the element at the specified index updated to the given value.
    #[inline(always)]
    #[must_use]
    pub fn update(&self, index: usize, value: T) -> Self {
        Self {
            inner: self.inner.update(index, value),
        }
    }

    /// Returns a new vector with the given element appended to the end.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::PersistentVector;
    ///
    /// let vec1 = PersistentVector::new();
    /// let vec2 = vec1.push_back(42);
    ///
    /// assert_eq!(vec1.len(), 0);
    /// assert_eq!(vec2.len(), 1);
    /// assert_eq!(vec2.get(0), Some(&42));
    /// ```
    #[inline(always)]
    #[must_use]
    pub fn push_back(&self, value: T) -> Self {
        Self {
            inner: self.inner.push_back(value),
        }
    }

    /// Converts this persistent vector to a standard `Vec`.
    ///
    /// This operation creates a new standard Vec with all the elements from the persistent vector.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::PersistentVector;
    ///
    /// let pvec = PersistentVector::from_slice(&[1, 2, 3]);
    /// let vec = pvec.to_vec();
    /// assert_eq!(vec, vec![1, 2, 3]);
    /// ```
    #[inline(always)]
    #[must_use]
    pub fn to_vec(&self) -> std::vec::Vec<T> {
        self.inner.to_vec()
    }

    /// Returns an iterator over the elements of the vector.
    ///
    /// This method provides a way to iterate through all elements without consuming the vector.
    /// The iterator yields shared references to each element in sequence.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::PersistentVector;
    ///
    /// let vec = PersistentVector::from_slice(&[1, 2, 3]);
    /// let mut sum = 0;
    /// for &value in vec.iter() {
    ///     sum += value;
    /// }
    /// assert_eq!(sum, 6);
    /// ```
    #[inline(always)]
    #[must_use]
    pub fn iter(&self) -> Iter<'_, T> {
        Iter::new(self)
    }

    /// Returns an iterator that yields chunks of elements from the vector.
    ///
    /// This method provides an efficient way to process the vector in fixed-size blocks.
    /// Each chunk contains a contiguous sequence of elements.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::PersistentVector;
    ///
    /// let vec = PersistentVector::from_slice(&[1, 2, 3, 4, 5, 6, 7, 8]);
    /// let chunks: Vec<Vec<i32>> = vec.chunks().collect();
    /// // chunks will contain the elements grouped into fixed-size blocks
    /// ```
    #[inline(always)]
    #[must_use]
    pub fn chunks(&self) -> ChunksIter<'_, T> {
        ChunksIter::with_default_sizes(self)
    }

    /// Returns an iterator that yields elements in sorted order without modifying the original vector.
    ///
    /// This iterator creates a sorted view of the vector by tracking indices in sorted order
    /// rather than modifying the original data structure. This provides efficient iteration
    /// over elements in their natural ordering while preserving the original vector's structure.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::PersistentVector;
    ///
    /// let vec = PersistentVector::from_slice(&[3, 1, 4, 2]);
    /// let sorted: Vec<&i32> = vec.sorted().collect();
    /// assert_eq!(sorted, vec![&1, &2, &3, &4]);
    /// ```
    #[inline(always)]
    #[must_use]
    pub fn sorted(&self) -> SortedIter<'_, T>
    where
        T: Ord,
    {
        SortedIter::new(self)
    }

    /// Returns a new vector with all elements from the provided iterator appended to the end.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::PersistentVector;
    ///
    /// let vec1 = PersistentVector::from_slice(&[1, 2, 3]);
    /// let vec2 = vec1.extend(vec![4, 5, 6]);
    ///
    /// assert_eq!(vec1.len(), 3);
    /// assert_eq!(vec2.len(), 6);
    /// assert_eq!(vec2.to_vec(), vec![1, 2, 3, 4, 5, 6]);
    /// ```
    #[inline(always)]
    #[must_use]
    pub fn extend(&self, values: impl IntoIterator<Item = T>) -> Self {
        Self {
            inner: self.inner.extend(values),
        }
    }

    /// Returns a tuple containing a new vector with the last element removed and the removed element, or None if the vector is empty.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::PersistentVector;
    ///
    /// let vec = PersistentVector::from_slice(&[1, 2, 3]);
    /// let (new_vec, value) = vec.pop_back().unwrap();
    ///
    /// assert_eq!(value, 3);
    /// assert_eq!(new_vec.len(), 2);
    /// assert_eq!(new_vec.to_vec(), vec![1, 2]);
    ///
    /// // Original vector is unchanged
    /// assert_eq!(vec.len(), 3);
    /// ```
    #[inline(always)]
    #[must_use]
    pub fn pop_back(&self) -> Option<(Self, T)> {
        self.inner.pop_back().map(|(inner, val)| (Self { inner }, val))
    }

    /// Converts this vector to an `Arc<PersistentVector<T>>` for thread-safe sharing.
    ///
    /// This is useful when you need to share the vector across multiple threads.
    /// Since `PersistentVector` is immutable, it can be safely shared without locks.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::PersistentVector;
    /// use std::sync::Arc;
    /// use std::thread;
    ///
    /// let vec = PersistentVector::from_slice(&[1, 2, 3]);
    /// let arc_vec = vec.to_arc();
    ///
    /// let handle = thread::spawn(move || {
    ///     // Access the vector from another thread
    ///     assert_eq!(arc_vec.get(0), Some(&1));
    /// });
    ///
    /// handle.join().unwrap();
    /// ```
    #[inline(always)]
    #[must_use]
    pub fn to_arc(self) -> Arc<Self> {
        Arc::new(self)
    }

    /// Creates a slice of this vector, returning a new vector with elements from the specified range.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::PersistentVector;
    ///
    /// let vec = PersistentVector::from_slice(&[1, 2, 3, 4, 5]);
    /// let slice = vec.slice(1, 4);
    /// assert_eq!(slice.to_vec(), vec![2, 3, 4]);
    /// ```
    #[inline(always)]
    #[must_use]
    pub fn slice(&self, start: usize, end: usize) -> Self {
        assert!(start <= end && end <= self.len());
        let mut result = Self::new();
        for i in start..end {
            if let Some(val) = self.get(i) {
                result = result.push_back(val.clone());
            }
        }
        result
    }

    /// Splits the vector at the given index, returning a pair of vectors.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::PersistentVector;
    ///
    /// let vec = PersistentVector::from_slice(&[1, 2, 3, 4, 5]);
    /// let (left, right) = vec.split_at(2);
    ///
    /// assert_eq!(left.to_vec(), vec![1, 2]);
    /// assert_eq!(right.to_vec(), vec![3, 4, 5]);
    /// ```
    #[inline(always)]
    #[must_use]
    pub fn split_at(&self, at: usize) -> (Self, Self) {
        assert!(at <= self.len());
        let mut left = Self::new();
        let mut right = Self::new();
        for i in 0..at {
            if let Some(val) = self.get(i) {
                left = left.push_back(val.clone());
            }
        }
        for i in at..self.len() {
            if let Some(val) = self.get(i) {
                right = right.push_back(val.clone());
            }
        }
        (left, right)
    }

    /// Returns a reference to the first element, or None if empty.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::PersistentVector;
    ///
    /// let vec = PersistentVector::from_slice(&[1, 2, 3]);
    /// assert_eq!(vec.first(), Some(&1));
    ///
    /// let empty: PersistentVector<i32> = PersistentVector::new();
    /// assert_eq!(empty.first(), None);
    /// ```
    #[inline(always)]
    #[must_use]
    pub fn first(&self) -> Option<&T> {
        self.get(0)
    }

    /// Returns a reference to the last element, or None if empty.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::PersistentVector;

    /// let vec = PersistentVector::from_slice(&[1, 2, 3]);
    /// assert_eq!(vec.last(), Some(&3));

    /// let empty: PersistentVector<i32> = PersistentVector::new();
    /// assert_eq!(empty.last(), None);
    /// ```
    #[inline(always)]
    #[must_use]
    pub fn last(&self) -> Option<&T> {
        if self.is_empty() {
            None
        } else {
            self.get(self.len() - 1)
        }
    }

    /// Returns true if the vector contains the given value.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::PersistentVector;
    ///
    /// let vec = PersistentVector::from_slice(&[1, 2, 3]);
    /// assert!(vec.contains(&2));
    /// assert!(!vec.contains(&4));
    /// ```
    #[inline(always)]
    #[must_use]
    pub fn contains(&self, value: &T) -> bool
    where
        T: PartialEq,
    {
        self.iter().any(|x| x == value)
    }

    /// Returns a Vec of references to all elements (for compatibility).
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::PersistentVector;
    ///
    /// let vec = PersistentVector::from_slice(&[1, 2, 3]);
    /// let slice = vec.as_slice();
    /// assert_eq!(slice, vec![&1, &2, &3]);
    /// ```
    #[inline(always)]
    #[must_use]
    pub fn as_slice(&self) -> Vec<&T> {
        self.iter().collect()
    }

    /// Returns a new vector with the element inserted at the given index.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::PersistentVector;
    ///
    /// let vec = PersistentVector::from_slice(&[1, 2, 3]);
    /// let new_vec = vec.insert(1, 42);
    /// assert_eq!(new_vec.to_vec(), vec![1, 42, 2, 3]);
    /// ```
    #[inline(always)]
    #[must_use]
    pub fn insert(&self, index: usize, value: T) -> Self {
        assert!(index <= self.len());
        let mut result = Self::new();
        for i in 0..index {
            if let Some(val) = self.get(i) {
                result = result.push_back(val.clone());
            }
        }
        result = result.push_back(value);
        for i in index..self.len() {
            if let Some(val) = self.get(i) {
                result = result.push_back(val.clone());
            }
        }
        result
    }

    /// Returns a new vector with the element at the given index removed.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::PersistentVector;
    ///
    /// let vec = PersistentVector::from_slice(&[1, 2, 3, 4]);
    /// let (new_vec, value) = vec.remove(2);
    /// assert_eq!(new_vec.to_vec(), vec![1, 2, 4]);
    /// assert_eq!(value, 3);
    /// ```
    #[inline(always)]
    #[must_use]
    pub fn remove(&self, index: usize) -> (Self, T) {
        assert!(index < self.len());
        let mut result = Self::new();
        let mut removed = None;
        for i in 0..self.len() {
            if i == index {
                removed = self.get(i).cloned();
                continue;
            }
            if let Some(val) = self.get(i) {
                result = result.push_back(val.clone());
            }
        }
        (result, removed.expect("index out of bounds"))
    }

    /// Returns a new vector containing only elements that match the predicate.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::PersistentVector;
    ///
    /// let vec = PersistentVector::from_slice(&[1, 2, 3, 4, 5]);
    /// let filtered = vec.retain(|&x| x % 2 == 0);
    /// assert_eq!(filtered.to_vec(), vec![2, 4]);
    /// ```
    #[inline(always)]
    #[must_use]
    pub fn retain<F>(&self, mut f: F) -> Self
    where
        F: FnMut(&T) -> bool,
    {
        let mut result = Self::new();
        for item in self.iter() {
            if f(item) {
                result = result.push_back(item.clone());
            }
        }
        result
    }

    /// Returns a new vector containing only elements that match the predicate (alias for retain).
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::PersistentVector;
    ///
    /// let vec = PersistentVector::from_slice(&[1, 2, 3, 4, 5]);
    /// let filtered = vec.filter(|&x| x % 2 == 0);
    /// assert_eq!(filtered.to_vec(), vec![2, 4]);
    /// ```
    #[inline(always)]
    #[must_use]
    pub fn filter<F>(&self, f: F) -> Self
    where
        F: FnMut(&T) -> bool,
    {
        self.retain(f)
    }

    /// Returns a new vector truncated to the given length.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::PersistentVector;
    ///
    /// let vec = PersistentVector::from_slice(&[1, 2, 3, 4, 5]);
    /// let truncated = vec.truncate(3);
    /// assert_eq!(truncated.to_vec(), vec![1, 2, 3]);
    /// ```
    #[inline(always)]
    #[must_use]
    pub fn truncate(&self, len: usize) -> Self {
        assert!(len <= self.len());
        self.slice(0, len)
    }

    /// Returns a new vector resized to the given length, filling with clones of value if needed.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::PersistentVector;
    ///
    /// let vec = PersistentVector::from_slice(&[1, 2, 3]);
    /// let resized = vec.resize(5, 42);
    /// assert_eq!(resized.to_vec(), vec![1, 2, 3, 42, 42]);
    /// ```
    #[inline(always)]
    #[must_use]
    pub fn resize(&self, new_len: usize, value: T) -> Self {
        let mut result = self.clone();
        let old_len = self.len();
        if new_len < old_len {
            result = result.truncate(new_len);
        } else if new_len > old_len {
            for _ in old_len..new_len {
                result = result.push_back(value.clone());
            }
        }
        result
    }

    /// Returns a new vector with elements in reverse order.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::PersistentVector;
    ///
    /// let vec = PersistentVector::from_slice(&[1, 2, 3, 4, 5]);
    /// let reversed = vec.reverse();
    /// assert_eq!(reversed.to_vec(), vec![5, 4, 3, 2, 1]);
    /// ```
    #[inline(always)]
    #[must_use]
    pub fn reverse(&self) -> Self {
        let mut result = Self::new();
        for item in self.iter().rev() {
            result = result.push_back(item.clone());
        }
        result
    }

    /// Returns a new vector with duplicate consecutive elements removed.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::PersistentVector;
    ///
    /// let vec = PersistentVector::from_slice(&[1, 2, 2, 3, 4, 4, 5]);
    /// let deduplicated = vec.dedup();
    /// assert_eq!(deduplicated.to_vec(), vec![1, 2, 3, 4, 5]);
    /// ```
    #[inline(always)]
    #[must_use]
    pub fn dedup(&self) -> Self
    where
        T: PartialEq,
    {
        let mut result = Self::new();
        let mut last: Option<&T> = None;
        for item in self.iter() {
            if Some(item) != last {
                result = result.push_back(item.clone());
            }
            last = Some(item);
        }
        result
    }

    /// Returns the index of the first occurrence of the value, or None if not found.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::PersistentVector;
    ///
    /// let vec = PersistentVector::from_slice(&[1, 2, 3, 4, 5]);
    /// assert_eq!(vec.position(&3), Some(2));
    /// assert_eq!(vec.position(&6), None);
    /// ```
    #[inline(always)]
    #[must_use]
    pub fn position(&self, value: &T) -> Option<usize>
    where
        T: PartialEq,
    {
        self.iter().position(|x| x == value)
    }

    /// Returns the result of a binary search.
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
    #[inline(always)]
    #[must_use]
    pub fn binary_search(&self, x: &T) -> Result<usize, usize>
    where
        T: Ord,
    {
        self.to_vec().binary_search(x)
    }

    /// Returns a new vector with elements sorted.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::PersistentVector;
    ///
    /// let vec = PersistentVector::from_slice(&[3, 1, 2]);
    /// let sorted = vec.sort();
    /// assert_eq!(sorted.to_vec(), vec![1, 2, 3]);
    /// ```
    #[inline(always)]
    #[must_use]
    pub fn sort(&self) -> Self
    where
        T: Ord,
    {
        let mut v = self.to_vec();
        v.sort();
        Self::from_slice(&v)
    }

    /// Returns a new vector with elements sorted by a comparator function.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::PersistentVector;
    ///
    /// let vec = PersistentVector::from_slice(&[3, 1, 2]);
    /// let sorted = vec.sort_by(|a, b| a.cmp(b));
    /// assert_eq!(sorted.to_vec(), vec![1, 2, 3]);
    /// ```
    #[inline(always)]
    #[must_use]
    pub fn sort_by<F>(&self, mut compare: F) -> Self
    where
        F: FnMut(&T, &T) -> std::cmp::Ordering,
    {
        let mut v = self.to_vec();
        v.sort_by(|a, b| compare(a, b));
        Self::from_slice(&v)
    }

    /// Maps each element in the vector using the given function.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::PersistentVector;
    ///
    /// let vec = PersistentVector::from_slice(&[1, 2, 3]);
    /// let mapped = vec.map(|x| x * 2);
    /// assert_eq!(mapped.to_vec(), vec![2, 4, 6]);
    /// ```
    #[inline(always)]
    #[must_use]
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
    /// let filtered = vec.filter_map(|x| if x % 2 == 0 { Some(x * 2) } else { None });
    /// assert_eq!(filtered.to_vec(), vec![4, 8]);
    /// ```
    #[inline(always)]
    #[must_use]
    pub fn filter_map<F, U>(&self, f: F) -> PersistentVector<U>
    where
        F: Fn(&T) -> Option<U>,
        U: Clone,
    {
        let mut buffer = Vec::with_capacity(self.len());
        for item in self.iter() {
            if let Some(val) = f(item) {
                buffer.push(val);
            }
        }
        PersistentVector::from_iter(buffer)
    }

    /// Flat maps each element in the vector using the given function.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::PersistentVector;
    ///
    /// let vec = PersistentVector::from_slice(&[1, 2, 3]);
    /// let flattened = vec.flat_map(|&x| vec![x, x * 2]);
    /// assert_eq!(flattened.to_vec(), vec![1, 2, 2, 4, 3, 6]);
    /// ```
    #[inline(always)]
    #[must_use]
    pub fn flat_map<I: IntoIterator<Item = T>, F: Fn(&T) -> I>(&self, f: F) -> PersistentVector<T> {
        let mut result = PersistentVector::new();
        for item in self.iter() {
            for flattened in f(item) {
                result = result.push_back(flattened);
            }
        }
        result
    }

    /// Concatenates two vectors, returning a new vector containing all elements from both.
    ///
    /// This operation creates a new vector with the contents of `self` followed by all elements of `other`.
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
    #[inline(always)]
    #[must_use]
    pub fn concat(&self, other: &Self) -> Self {
        let mut result = self.clone();
        for item in other.iter() {
            result = result.push_back(item.clone());
        }
        result
    }
}

impl<T: Clone> Default for PersistentVector<T> {
    #[inline(always)]
    fn default() -> Self {
        Self::new()
    }
}

impl<T: Clone + Debug> Debug for PersistentVector<T> {
    #[inline(always)]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self.iter()).finish()
    }
}

impl<T: Clone> FromIterator<T> for PersistentVector<T> {
    #[inline(always)]
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        let mut v = Self::new();
        for item in iter {
            v = v.push_back(item);
        }
        v
    }
}

impl<T: Clone> From<Vec<T>> for PersistentVector<T> {
    #[inline(always)]
    fn from(val: Vec<T>) -> Self {
        Self::from_slice(&val)
    }
}

impl<T: Clone> From<PersistentVector<T>> for Vec<T> {
    #[inline(always)]
    fn from(val: PersistentVector<T>) -> Self {
        val.to_vec()
    }
}

impl<T: Clone> Index<usize> for PersistentVector<T> {
    type Output = T;
    #[inline(always)]
    fn index(&self, index: usize) -> &Self::Output {
        self.get(index).expect("index out of bounds")
    }
}

impl<T: Clone> IntoIterator for PersistentVector<T> {
    type Item = T;
    type IntoIter = crate::pvec::iterator::IntoIter<T>;
    #[inline(always)]
    fn into_iter(self) -> Self::IntoIter {
        crate::pvec::iterator::IntoIter::new(self)
    }
}

impl<'a, T: Clone> IntoIterator for &'a PersistentVector<T> {
    type Item = &'a T;
    type IntoIter = crate::pvec::iterator::Iter<'a, T>;
    #[inline(always)]
    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}
