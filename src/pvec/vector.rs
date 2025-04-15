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
    #[inline(always)]
    #[must_use]
    pub fn new() -> Self {
        Self {
            inner: VectorImpl::new(),
        }
    }

    /// Creates a new persistent vector with a single element.
    #[inline(always)]
    #[must_use]
    pub fn unit(value: T) -> Self {
        Self {
            inner: VectorImpl::unit(value),
        }
    }

    /// Creates a new persistent vector from a slice of elements.
    #[inline(always)]
    #[must_use]
    pub fn from_slice(slice: &[T]) -> Self {
        Self {
            inner: VectorImpl::from_slice(slice),
        }
    }

    /// Returns the number of elements in the vector.
    #[inline(always)]
    #[must_use]
    pub fn len(&self) -> usize {
        match &self.inner {
            VectorImpl::Small { elements } => elements.len(),
            VectorImpl::Tree { tree } => tree.len(),
        }
    }

    /// Returns true if the vector contains no elements.
    #[inline(always)]
    #[must_use]
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Returns a reference to the element at the specified index, or None if the index is out of bounds.
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
    #[inline(always)]
    #[must_use]
    pub fn push_back(&self, value: T) -> Self {
        Self {
            inner: self.inner.push_back(value),
        }
    }

    /// Converts this persistent vector to a standard `Vec`.
    #[inline(always)]
    #[must_use]
    pub fn to_vec(&self) -> std::vec::Vec<T> {
        self.inner.to_vec()
    }

    /// Returns an iterator over the elements of the vector.
    #[inline(always)]
    #[must_use]
    pub fn iter(&self) -> Iter<'_, T> {
        Iter::new(self)
    }

    /// Returns an iterator that yields chunks of elements.
    #[inline(always)]
    #[must_use]
    pub fn chunks(&self) -> ChunksIter<'_, T> {
        ChunksIter::with_default_sizes(self)
    }

    /// Returns an iterator that yields elements in sorted order.
    #[inline(always)]
    #[must_use]
    pub fn sorted(&self) -> SortedIter<'_, T>
    where
        T: Ord,
    {
        SortedIter::new(self)
    }

    /// Returns a new vector with all elements from the provided iterator appended to the end.
    #[inline(always)]
    #[must_use]
    pub fn extend(&self, values: impl IntoIterator<Item = T>) -> Self {
        Self {
            inner: self.inner.extend(values),
        }
    }

    /// Returns a tuple containing a new vector with the last element removed and the removed element, or None if the vector is empty.
    #[inline(always)]
    #[must_use]
    pub fn pop_back(&self) -> Option<(Self, T)> {
        self.inner.pop_back().map(|(inner, val)| (Self { inner }, val))
    }

    /// Converts this vector to an `Arc<PersistentVector<T>>`.
    #[inline(always)]
    #[must_use]
    pub fn to_arc(self) -> Arc<Self> {
        Arc::new(self)
    }

    /// Creates a slice of this vector, returning a new vector with elements from the specified range.
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

impl<T: Clone> PersistentVector<T> {
    /// Maps each element in the vector using the given function.
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
    #[inline(always)]
    #[must_use]
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
    #[inline(always)]
    #[must_use]
    pub fn first(&self) -> Option<&T> {
        self.get(0)
    }

    /// Returns the last element of the vector, or None if it's empty.
    #[inline(always)]
    #[must_use]
    pub fn last(&self) -> Option<&T> {
        if self.is_empty() {
            None
        } else {
            self.get(self.len() - 1)
        }
    }

    /// Concatenates two vectors, returning a new vector.
    #[inline(always)]
    #[must_use]
    pub fn concat(&self, other: &Self) -> Self {
        let mut result = self.clone();
        for item in other.iter() {
            result = result.push_back(item.clone());
        }
        result
    }

    /// Flat maps each element in the vector using the given function.
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
