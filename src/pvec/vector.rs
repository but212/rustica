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
pub struct PersistentVector<T>
where
    T: Clone,
{
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
enum VectorImpl<T>
where
    T: Clone,
{
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
#[derive(Clone, PartialEq, Eq, Debug)]
struct SmallVec<T> {
    /// The elements stored inline in a fixed-size array
    elements: [Option<T>; SMALL_VECTOR_SIZE],
    /// The number of elements currently stored in the vector
    size: usize,
}

impl<T: Clone> SmallVec<T> {
    /// Creates a new, empty SmallVec
    ///
    /// Initializes a SmallVec with zero elements and all storage slots set to None.
    /// This operation is O(1) as it uses Default to initialize the array.
    fn new() -> Self {
        Self {
            // Initialize all slots with None
            elements: Default::default(),
            size: 0,
        }
    }

    /// Returns a reference to the element at the given index, or None if out of bounds
    fn get(&self, index: usize) -> Option<&T> {
        if index < self.size {
            self.elements[index].as_ref()
        } else {
            None
        }
    }

    /// Returns true if the vector is empty
    const fn is_empty(&self) -> bool {
        self.size == 0
    }

    /// Returns the number of elements in the vector
    const fn len(&self) -> usize {
        self.size
    }

    /// Returns a new SmallVec with the given element appended
    fn push_back(&self, value: T) -> Self {
        if self.size < SMALL_VECTOR_SIZE {
            // We have space, add to inline storage
            let mut new_vec = self.clone();
            new_vec.elements[self.size] = Some(value);
            new_vec.size += 1;
            new_vec
        } else {
            // Should never happen - caller should upgrade to tree
            panic!("SmallVec overflow");
        }
    }

    /// Returns a new SmallVec with the element at the given index updated
    fn update(&self, index: usize, value: T) -> Self {
        if index < self.size {
            let mut new_vec = self.clone();
            new_vec.elements[index] = Some(value);
            new_vec
        } else {
            self.clone()
        }
    }

    /// Convert to a standard Vec
    fn to_vec(&self) -> std::vec::Vec<T> {
        self.elements[0..self.size].iter().filter_map(|opt| opt.clone()).collect()
    }
}

impl<T: Clone> Default for SmallVec<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T: Clone> VectorImpl<T> {
    /// Creates a new, empty vector
    fn new() -> Self {
        VectorImpl::Small {
            elements: SmallVec::new(),
        }
    }

    /// Creates a unit vector with one element
    fn unit(value: T) -> Self {
        let mut elements = SmallVec::new();
        elements = elements.push_back(value);
        VectorImpl::Small { elements }
    }

    /// Creates a vector from a slice of elements
    fn from_slice(slice: &[T]) -> Self {
        if slice.len() <= SMALL_VECTOR_SIZE {
            // We can use the small vector optimization
            let mut elements = SmallVec::new();
            for item in slice {
                elements = elements.push_back(item.clone());
            }
            VectorImpl::Small { elements }
        } else {
            // Use the tree implementation for larger vectors
            VectorImpl::Tree {
                tree: Tree::from_slice(slice),
            }
        }
    }

    /// Returns a reference to the element at the specified index, or None if the index is out of bounds.
    fn get(&self, index: usize) -> Option<&T> {
        match self {
            VectorImpl::Small { elements } => elements.get(index),
            VectorImpl::Tree { tree } => tree.get(index),
        }
    }

    /// Returns a new vector with the given element appended
    fn push_back(&self, value: T) -> Self {
        match self {
            VectorImpl::Small { elements } => {
                if elements.len() < SMALL_VECTOR_SIZE - 1 {
                    // Still fits in the small vector
                    VectorImpl::Small {
                        elements: elements.push_back(value),
                    }
                } else {
                    // Need to upgrade to tree
                    let mut tree = Tree::new();

                    // Add all elements from the small vector
                    for i in 0..elements.len() {
                        if let Some(elem) = elements.get(i) {
                            tree = tree.push_back(elem.clone());
                        }
                    }

                    // Add the new element
                    tree = tree.push_back(value);

                    VectorImpl::Tree { tree }
                }
            },
            VectorImpl::Tree { tree } => VectorImpl::Tree {
                tree: tree.push_back(value),
            },
        }
    }

    /// Returns a new vector with the element at the given index updated
    fn update(&self, index: usize, value: T) -> Self {
        match self {
            VectorImpl::Small { elements } => {
                if index < elements.len() {
                    VectorImpl::Small {
                        elements: elements.update(index, value),
                    }
                } else {
                    self.clone()
                }
            },
            VectorImpl::Tree { tree } => {
                if index < tree.len() {
                    VectorImpl::Tree {
                        tree: tree.update(index, value),
                    }
                } else {
                    self.clone()
                }
            },
        }
    }

    /// Convert to a standard Vec
    fn to_vec(&self) -> std::vec::Vec<T> {
        match self {
            VectorImpl::Small { elements } => elements.to_vec(),
            VectorImpl::Tree { tree } => {
                let mut result = std::vec::Vec::with_capacity(tree.len());
                for i in 0..tree.len() {
                    if let Some(elem) = tree.get(i) {
                        result.push(elem.clone());
                    }
                }
                result
            },
        }
    }

    /// Gets a chunk of elements starting at the specified index.
    ///
    /// This method is used by the chunk iterator implementation to efficiently retrieve
    /// batches of elements. It returns a vector containing elements from `start_index` up to
    /// a calculated chunk size that satisfies the given constraints.
    ///
    /// # Parameters
    ///
    /// * `start_index` - The starting index to retrieve elements from
    /// * `min_size` - The minimum number of elements to retrieve (if available)
    /// * `max_size` - The maximum number of elements to retrieve
    ///
    /// # Returns
    ///
    /// A standard vector containing the requested elements. If `start_index` is out of bounds,
    /// an empty vector is returned.
    fn get_chunk(&self, start_index: usize, min_size: usize, max_size: usize) -> StdVec<T> {
        match self {
            VectorImpl::Small { elements } => {
                if start_index >= elements.len() {
                    return StdVec::new();
                }

                // Calculate chunk size based on constraints
                let remaining = elements.len() - start_index;
                let chunk_size = remaining.min(max_size).max(min_size).min(remaining);

                // Collect elements into vector
                let mut result = StdVec::with_capacity(chunk_size);
                for i in 0..chunk_size {
                    if let Some(elem) = elements.get(start_index + i) {
                        result.push(elem.clone());
                    }
                }

                result
            },
            VectorImpl::Tree { tree } => {
                if start_index >= tree.len() {
                    return StdVec::new();
                }

                // Calculate chunk size based on constraints
                let remaining = tree.len() - start_index;
                let chunk_size = remaining.min(max_size).max(min_size).min(remaining);

                // Collect elements into vector
                let mut result = StdVec::with_capacity(chunk_size);
                for i in 0..chunk_size {
                    if let Some(elem) = tree.get(start_index + i) {
                        result.push(elem.clone());
                    }
                }

                result
            },
        }
    }

    /// Returns a new vector with all elements from the provided iterator appended to the end.
    ///
    /// Unlike the `extend` method in the `Extend` trait, this method returns a new vector
    /// rather than modifying the existing one, preserving immutability.
    fn extend(&self, values: impl IntoIterator<Item = T>) -> Self {
        let mut result = self.clone();
        for item in values {
            result = result.push_back(item);
        }
        result
    }

    /// Removes the last element from the vector and returns it, along with the updated vector.
    ///
    /// This method returns a tuple containing the new vector (with the last element removed) and
    /// the removed element. If the vector is empty, it returns `None`.
    fn pop_back(&self) -> Option<(Self, T)> {
        match self {
            VectorImpl::Small { elements } => {
                if elements.is_empty() {
                    None
                } else {
                    let mut new_elements = elements.clone();
                    let last_idx = elements.len() - 1;
                    let last_elem = elements.get(last_idx)?.clone();
                    new_elements.size -= 1;
                    Some((
                        VectorImpl::Small {
                            elements: new_elements,
                        },
                        last_elem,
                    ))
                }
            },
            VectorImpl::Tree { tree } => tree
                .pop_back()
                .map(|(new_tree, value)| (VectorImpl::Tree { tree: new_tree }, value)),
        }
    }
}

impl<T: Clone> FromIterator<T> for VectorImpl<T> {
    #[inline]
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        let mut result = VectorImpl::new();
        for item in iter {
            result = result.push_back(item);
        }
        result
    }
}

impl<T: Clone + Debug> Debug for VectorImpl<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            VectorImpl::Small { elements } => {
                f.debug_struct("Small").field("elements", elements).finish()
            },
            VectorImpl::Tree { tree } => f.debug_struct("Tree").field("tree", tree).finish(),
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
    /// assert_eq!(vec.len(), 0);
    /// assert!(vec.is_empty());
    /// ```
    #[inline]
    pub fn new() -> Self {
        Self {
            inner: VectorImpl::new(),
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
            inner: VectorImpl::unit(value),
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
            inner: VectorImpl::from_slice(slice),
        }
    }

    /// Returns the number of elements in the vector.
    ///
    /// This operation is O(1) as the size is cached.
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
        match &self.inner {
            VectorImpl::Small { elements } => elements.len(),
            VectorImpl::Tree { tree } => tree.len(),
        }
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
        match &self.inner {
            VectorImpl::Small { elements } => elements.is_empty(),
            VectorImpl::Tree { tree } => tree.is_empty(),
        }
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
        self.inner.get(index)
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
    /// let vec = PersistentVector::<i32>::new();
    /// let vec = vec.push_back(10);
    /// let vec = vec.push_back(20);
    /// assert_eq!(vec.len(), 2);
    /// assert_eq!(vec.get(1), Some(&20));
    /// ```
    #[inline]
    pub fn push_back(&self, value: T) -> Self {
        Self {
            inner: self.inner.push_back(value),
        }
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
    pub fn to_vec(&self) -> std::vec::Vec<T> {
        self.inner.to_vec()
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
    #[inline]
    pub(crate) fn get_chunk(
        &self, start_index: usize, min_size: usize, max_size: usize,
    ) -> StdVec<T> {
        self.inner.get_chunk(start_index, min_size, max_size)
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
            inner: self.inner.extend(values),
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
        self.inner.pop_back().map(|(inner, value)| (Self { inner }, value))
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

    /// Creates a slice of this vector, returning a new vector with elements from the specified range.
    ///
    /// # Parameters
    ///
    /// - `start`: The starting index (inclusive)
    /// - `end`: The ending index (exclusive)
    ///
    /// # Returns
    ///
    /// A new `PersistentVector` containing only the elements in the specified range.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::PersistentVector;
    ///
    /// let vec = PersistentVector::from_slice(&[1, 2, 3, 4, 5]);
    /// let slice = vec.slice(1, 4);
    /// assert_eq!(slice.len(), 3);
    /// assert_eq!(slice.get(0), Some(&2));
    /// assert_eq!(slice.get(1), Some(&3));
    /// assert_eq!(slice.get(2), Some(&4));
    /// ```
    ///
    /// # Panics
    ///
    /// Panics if `start > end` or if `end > len`.
    #[inline]
    pub fn slice(&self, start: usize, end: usize) -> Self
    where
        T: Clone,
    {
        if start > end {
            panic!("start index {} greater than end index {}", start, end);
        }
        if end > self.len() {
            panic!("end index {} out of bounds for length {}", end, self.len());
        }

        if start == end {
            return Self::new();
        }

        let mut result = Self::new();
        for i in start..end {
            result = result.push_back(self.get(i).unwrap().clone());
        }
        result
    }

    /// Splits the vector at the given index, returning a pair of vectors.
    ///
    /// The first vector contains all elements up to (but not including) the given index,
    /// and the second vector contains all elements from the given index to the end.
    ///
    /// # Parameters
    ///
    /// - `at`: The index at which to split
    ///
    /// # Returns
    ///
    /// A tuple of two `PersistentVector`s: `(left, right)` where `left` contains elements
    /// with indices from `0` to `at-1`, and `right` contains elements with indices from `at`
    /// to the end.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::PersistentVector;
    ///
    /// let vec = PersistentVector::from_slice(&[1, 2, 3, 4, 5]);
    /// let (left, right) = vec.split_at(3);
    /// assert_eq!(left.len(), 3);
    /// assert_eq!(right.len(), 2);
    /// assert_eq!(left.to_vec(), vec![1, 2, 3]);
    /// assert_eq!(right.to_vec(), vec![4, 5]);
    /// ```
    ///
    /// # Panics
    ///
    /// Panics if `at > len`.
    #[inline]
    pub fn split_at(&self, at: usize) -> (Self, Self)
    where
        T: Clone,
    {
        if at > self.len() {
            panic!("split index {} out of bounds for length {}", at, self.len());
        }

        let left = self.slice(0, at);
        let right = self.slice(at, self.len());

        (left, right)
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
            inner: VectorImpl::from_iter(iter),
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
    /// let mut sum = 0;
    /// for &x in vec.iter() {
    ///     sum += x;
    /// }
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

impl<T: Clone> Extend<T> for PersistentVector<T> {
    fn extend<I: IntoIterator<Item = T>>(&mut self, iter: I) {
        // Since this is an immutable vector, we can't modify its contents directly.
        // Instead, we create a new vector and assign it to self.
        let mut vec = self.clone();
        for item in iter {
            vec = vec.push_back(item);
        }
        *self = vec;
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
    #[inline]
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
    #[inline]
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
        let mut result = self.clone();
        for item in other.iter() {
            result = result.push_back(item.clone());
        }
        result
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
            for flattened in f(item) {
                result = result.push_back(flattened);
            }
        }
        result
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
