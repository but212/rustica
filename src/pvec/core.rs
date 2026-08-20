//! Core implementation of the persistent vector data structure.

use smallvec::SmallVec;
use std::cmp::Ordering;
use std::fmt::{self, Debug};
use std::hash::{Hash, Hasher};
use std::sync::Arc;

use super::error::PVecError;
use super::iter::{PersistentVectorIntoIter, PersistentVectorIter};
use super::tree::RRBTree;

pub(crate) const ADAPTIVE_INLINE_SIZE: usize = 64;

/// A persistent, immutable vector data structure.
///
/// `PersistentVector` provides an efficient implementation of an immutable vector
/// that supports structural sharing. Operations like `push_back`, `push_front`,
/// and `update` return new vectors that share structure with the original,
/// making them efficient in both time and space.
///
/// The implementation uses an adaptive strategy: small vectors are stored inline
/// for optimal performance, while larger vectors use an RRB (Relaxed Radix Balanced)
/// tree structure that provides logarithmic time complexity for most operations.
///
/// # Examples
///
/// ```
/// use rustica::pvec::PersistentVector;
///
/// let vec = PersistentVector::new();
/// let vec = vec.push_back(1).push_back(2).push_back(3);
///
/// assert_eq!(vec.len(), 3);
/// assert_eq!(vec.get(1), Some(&2));
///
/// let vec2 = vec.update(1, 42);
/// assert_eq!(vec.get(1), Some(&2));  // Original unchanged
/// assert_eq!(vec2.get(1), Some(&42)); // New vector updated
/// ```
#[derive(Clone)]
pub struct PersistentVector<T> {
    pub(crate) inner: VectorImpl<T>,
}

/// Internal representation of the vector data.
///
/// Uses an adaptive strategy where small vectors are stored inline
/// and larger vectors use a tree structure.
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) enum VectorImpl<T> {
    /// Inline storage for small vectors.
    Inline {
        elements: SmallVec<[T; ADAPTIVE_INLINE_SIZE]>,
    },
    /// Tree storage for larger vectors.
    Tree { tree: Arc<RRBTree<T>> },
}

impl<T> VectorImpl<T> {
    fn len(&self) -> usize {
        match self {
            Self::Inline { elements } => elements.len(),
            Self::Tree { tree } => tree.len,
        }
    }
}

impl<T: PartialEq> PartialEq for PersistentVector<T> {
    fn eq(&self, other: &Self) -> bool {
        self.iter().eq(other.iter())
    }
}

impl<T: Eq> Eq for PersistentVector<T> {}

impl<T: PartialOrd> PartialOrd for PersistentVector<T> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        self.iter().partial_cmp(other.iter())
    }
}

impl<T: Ord> Ord for PersistentVector<T> {
    fn cmp(&self, other: &Self) -> Ordering {
        self.iter().cmp(other.iter())
    }
}

impl<T: Hash> Hash for PersistentVector<T> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.len().hash(state);
        for value in self {
            value.hash(state);
        }
    }
}

impl<T> PersistentVector<T> {
    #[inline]
    fn inline(elements: SmallVec<[T; ADAPTIVE_INLINE_SIZE]>) -> Self {
        Self {
            inner: VectorImpl::Inline { elements },
        }
    }

    #[inline]
    fn tree(tree: RRBTree<T>) -> Self {
        Self {
            inner: VectorImpl::Tree {
                tree: Arc::new(tree),
            },
        }
    }

    /// Creates a new empty persistent vector.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::PersistentVector;
    ///
    /// let vec: PersistentVector<i32> = PersistentVector::new();
    /// assert!(vec.is_empty());
    /// ```
    pub fn new() -> Self {
        Self::inline(SmallVec::new())
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
    pub fn unit(value: T) -> Self {
        Self::inline(SmallVec::from_iter([value]))
    }

    /// Returns the number of elements in the vector.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::PersistentVector;
    ///
    /// let vec = PersistentVector::new().push_back(1).push_back(2);
    /// assert_eq!(vec.len(), 2);
    /// ```
    pub fn len(&self) -> usize {
        self.inner.len()
    }

    /// Returns `true` if the vector contains no elements.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::PersistentVector;
    ///
    /// let vec: PersistentVector<i32> = PersistentVector::new();
    /// assert!(vec.is_empty());
    ///
    /// let vec = vec.push_back(1);
    /// assert!(!vec.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Returns an iterator over the vector elements.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::PersistentVector;
    ///
    /// let vec = PersistentVector::new().push_back(1).push_back(2).push_back(3);
    /// let collected: Vec<_> = vec.iter().collect();
    /// assert_eq!(collected, vec![&1, &2, &3]);
    /// ```
    pub fn iter(&self) -> PersistentVectorIter<'_, T> {
        PersistentVectorIter::new(self)
    }
}

impl<T> PersistentVector<T> {
    /// Gets a reference to the element at the specified index.
    ///
    /// Returns `None` if the index is out of bounds.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::PersistentVector;
    ///
    /// let vec = PersistentVector::from_slice(&[1, 2, 3]);
    /// assert_eq!(vec.get(1), Some(&2));
    /// assert_eq!(vec.get(10), None);
    /// ```
    pub fn get(&self, index: usize) -> Option<&T> {
        if index >= self.len() {
            return None;
        }

        match &self.inner {
            VectorImpl::Inline { elements } => elements.get(index),
            VectorImpl::Tree { tree } => tree.as_ref().get(index),
        }
    }
}

impl<T: Clone> PersistentVector<T> {
    /// Creates a persistent vector from a slice.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::PersistentVector;
    ///
    /// let slice = &[1, 2, 3, 4, 5];
    /// let vec = PersistentVector::from_slice(slice);
    /// assert_eq!(vec.len(), 5);
    /// ```
    pub fn from_slice(slice: &[T]) -> Self {
        Self::from_iter(slice.iter().cloned())
    }

    /// Creates a new vector by applying a function to each element.
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
    pub fn map<U, F>(&self, f: F) -> PersistentVector<U>
    where
        F: Fn(&T) -> U,
        U: Clone,
    {
        PersistentVector::from_iter(self.iter().map(f))
    }

    /// Creates a new vector containing only elements that match the predicate.
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
    pub fn filter<F>(&self, predicate: F) -> Self
    where
        F: Fn(&T) -> bool,
    {
        Self::from_iter(self.iter().filter(|x| predicate(x)).cloned())
    }

    /// Gets a reference to the element at the specified index, returning an error if out of bounds.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::PersistentVector;
    ///
    /// let vec = PersistentVector::from_slice(&[1, 2, 3]);
    /// assert!(vec.try_get(1).is_ok());
    /// assert!(vec.try_get(10).is_err());
    /// ```
    pub fn try_get(&self, index: usize) -> Result<&T, PVecError> {
        self.get(index).ok_or(PVecError::IndexOutOfBounds {
            index,
            len: self.len(),
        })
    }

    /// Gets a reference to the first element.
    ///
    /// Returns `None` if the vector is empty.
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
    pub fn first(&self) -> Option<&T> {
        self.get(0)
    }

    /// Gets a reference to the last element.
    ///
    /// Returns `None` if the vector is empty.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::PersistentVector;
    ///
    /// let vec = PersistentVector::from_slice(&[1, 2, 3]);
    /// assert_eq!(vec.last(), Some(&3));
    ///
    /// let empty: PersistentVector<i32> = PersistentVector::new();
    /// assert_eq!(empty.last(), None);
    /// ```
    pub fn last(&self) -> Option<&T> {
        if !self.is_empty() {
            self.get(self.len() - 1)
        } else {
            None
        }
    }

    /// Creates a new vector by applying a function and filtering out `None` results.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::PersistentVector;
    ///
    /// let vec = PersistentVector::from_slice(&["1", "2", "not_a_number", "4"]);
    /// let parsed: PersistentVector<i32> = vec.filter_map(|s| s.parse().ok());
    /// assert_eq!(parsed.to_vec(), vec![1, 2, 4]);
    /// ```
    pub fn filter_map<U: Clone, F>(&self, f: F) -> PersistentVector<U>
    where
        F: Fn(&T) -> Option<U>,
    {
        PersistentVector::from_iter(self.iter().filter_map(f))
    }

    /// Creates a new vector by applying a function that returns an iterator and flattening the results.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::PersistentVector;
    ///
    /// let vec = PersistentVector::from_slice(&[1, 2, 3]);
    /// let doubled = vec.flat_map(|&x| vec![x, x]);
    /// assert_eq!(doubled.to_vec(), vec![1, 1, 2, 2, 3, 3]);
    /// ```
    pub fn flat_map<U: Clone, F, I>(&self, f: F) -> PersistentVector<U>
    where
        F: Fn(&T) -> I,
        I: IntoIterator<Item = U>,
    {
        PersistentVector::from_iter(self.iter().flat_map(f))
    }

    /// Creates a new vector with consecutive duplicate elements removed.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::PersistentVector;
    ///
    /// let vec = PersistentVector::from_slice(&[1, 1, 2, 2, 3, 3]);
    /// let deduped = vec.dedup();
    /// assert_eq!(deduped.to_vec(), vec![1, 2, 3]);
    /// ```
    pub fn dedup(&self) -> Self
    where
        T: PartialEq,
    {
        let mut result = Vec::new();
        let mut last: Option<&T> = None;

        for item in self.iter() {
            if last != Some(item) {
                result.push(item.clone());
                last = Some(item);
            }
        }

        Self::from_iter(result)
    }

    /// Creates a new vector with elements sorted in ascending order.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::PersistentVector;
    ///
    /// let vec = PersistentVector::from_slice(&[3, 1, 4, 1, 5]);
    /// let sorted = vec.sorted();
    /// assert_eq!(sorted.to_vec(), vec![1, 1, 3, 4, 5]);
    /// ```
    pub fn sorted(&self) -> Self
    where
        T: Ord,
    {
        let mut items: Vec<T> = self.iter().cloned().collect();
        items.sort();
        Self::from_iter(items)
    }

    /// Applies a function to each element, accumulating the results.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::PersistentVector;
    ///
    /// let vec = PersistentVector::from_slice(&[1, 2, 3, 4]);
    /// let sum = vec.fold(0, |acc, &x| acc + x);
    /// assert_eq!(sum, 10);
    /// ```
    pub fn fold<B, F>(&self, init: B, f: F) -> B
    where
        F: Fn(B, &T) -> B,
    {
        self.iter().fold(init, f)
    }

    /// Creates a new vector by pairing elements from two vectors.
    ///
    /// The resulting vector has the length of the shorter input vector.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::PersistentVector;
    ///
    /// let vec1 = PersistentVector::from_slice(&[1, 2, 3]);
    /// let vec2 = PersistentVector::from_slice(&["a", "b", "c"]);
    /// let zipped = vec1.zip(&vec2);
    /// assert_eq!(zipped.to_vec(), vec![(1, "a"), (2, "b"), (3, "c")]);
    /// ```
    pub fn zip<U>(&self, other: &PersistentVector<U>) -> PersistentVector<(T, U)>
    where
        U: Clone,
    {
        PersistentVector::from_iter(
            self.iter()
                .zip(other.iter())
                .map(|(a, b)| (a.clone(), b.clone())),
        )
    }

    /// Partitions the vector into two vectors based on a predicate.
    ///
    /// Returns a tuple where the first vector contains elements that match
    /// the predicate and the second contains elements that don't.
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
    pub fn partition<F>(&self, predicate: F) -> (Self, Self)
    where
        F: Fn(&T) -> bool,
    {
        let mut true_items = Vec::new();
        let mut false_items = Vec::new();

        for item in self.iter() {
            if predicate(item) {
                true_items.push(item.clone());
            } else {
                false_items.push(item.clone());
            }
        }

        (Self::from_iter(true_items), Self::from_iter(false_items))
    }

    /// Splits the vector into chunks of the specified size.
    ///
    /// Returns a vector of vectors, where each inner vector contains at most `size` elements.
    /// If `size` is 0, returns an empty vector.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::PersistentVector;
    ///
    /// let vec = PersistentVector::from_slice(&[1, 2, 3, 4, 5]);
    /// let chunks = vec.chunk(2);
    /// assert_eq!(chunks.len(), 3);
    /// assert_eq!(chunks.get(0).unwrap().to_vec(), vec![1, 2]);
    /// assert_eq!(chunks.get(1).unwrap().to_vec(), vec![3, 4]);
    /// assert_eq!(chunks.get(2).unwrap().to_vec(), vec![5]);
    /// ```
    pub fn chunk(&self, size: usize) -> PersistentVector<PersistentVector<T>> {
        if size == 0 {
            return PersistentVector::new();
        }

        let mut iter = self.iter();
        PersistentVector::from_iter(std::iter::from_fn(move || {
            let chunk: Vec<T> = iter.by_ref().take(size).cloned().collect();
            (!chunk.is_empty()).then(|| PersistentVector::from_iter(chunk))
        }))
    }

    /// Creates a new vector with an element added to the end.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::PersistentVector;
    ///
    /// let vec = PersistentVector::new();
    /// let vec = vec.push_back(1).push_back(2);
    /// assert_eq!(vec.to_vec(), vec![1, 2]);
    /// ```
    pub fn push_back(&self, value: T) -> Self {
        match &self.inner {
            VectorImpl::Inline { elements } => {
                if elements.len() < ADAPTIVE_INLINE_SIZE {
                    let mut new_elements = elements.clone();
                    new_elements.push(value);
                    Self::inline(new_elements)
                } else {
                    self.transition_to_tree().push_back(value)
                }
            },
            VectorImpl::Tree { tree: _ } => self.tree_push_back(value),
        }
    }

    /// Creates a new vector with an element added to the beginning.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::PersistentVector;
    ///
    /// let vec = PersistentVector::new();
    /// let vec = vec.push_front(1).push_front(2);
    /// assert_eq!(vec.to_vec(), vec![2, 1]);
    /// ```
    pub fn push_front(&self, value: T) -> Self {
        match &self.inner {
            VectorImpl::Inline { elements } => {
                if elements.len() < ADAPTIVE_INLINE_SIZE {
                    let mut new_elements = SmallVec::with_capacity(elements.len() + 1);
                    new_elements.push(value);
                    new_elements.extend(elements.iter().cloned());
                    Self::inline(new_elements)
                } else {
                    self.transition_to_tree().push_front(value)
                }
            },
            VectorImpl::Tree { tree: _ } => self.tree_push_front(value),
        }
    }

    /// Creates a new vector with the element at the specified index updated, returning an error if out of bounds.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::PersistentVector;
    ///
    /// let vec = PersistentVector::from_slice(&[1, 2, 3]);
    /// let updated = vec.try_update(1, 42).unwrap();
    /// assert_eq!(updated.to_vec(), vec![1, 42, 3]);
    ///
    /// assert!(vec.try_update(10, 42).is_err());
    /// ```
    pub fn try_update(&self, index: usize, value: T) -> Result<Self, PVecError> {
        if index >= self.len() {
            return Err(PVecError::IndexOutOfBounds {
                index,
                len: self.len(),
            });
        }
        Ok(self.update(index, value))
    }

    /// Creates a new vector with the element at the specified index updated.
    ///
    /// # Error Handling
    ///
    /// If the index is out of bounds, returns a clone of the original vector
    /// without modification. This "silent failure" behavior is intentional for
    /// functional programming patterns where operations should be total functions.
    ///
    /// For explicit error handling, use [`try_update`] instead.
    ///
    /// [`try_update`]: Self::try_update
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::PersistentVector;
    ///
    /// let vec = PersistentVector::from_slice(&[1, 2, 3]);
    /// let updated = vec.update(1, 42);
    /// assert_eq!(updated.to_vec(), vec![1, 42, 3]);
    /// assert_eq!(vec.to_vec(), vec![1, 2, 3]); // Original unchanged
    ///
    /// // Out of bounds returns clone (no panic)
    /// let same = vec.update(100, 999);
    /// assert_eq!(same.to_vec(), vec![1, 2, 3]);
    /// ```
    pub fn update(&self, index: usize, value: T) -> Self {
        if index >= self.len() {
            return self.clone();
        }

        match &self.inner {
            VectorImpl::Inline { elements } => {
                let mut new_elements = elements.clone();
                new_elements[index] = value;
                Self::inline(new_elements)
            },
            VectorImpl::Tree { tree } => {
                let new_tree = tree.update(index, value);
                Self::tree(new_tree)
            },
        }
    }

    /// Transitions from inline storage to tree storage.
    fn transition_to_tree(&self) -> Self {
        match &self.inner {
            VectorImpl::Inline { elements } => {
                let tree = RRBTree::from_elements(elements.iter().cloned());
                Self::tree(tree)
            },
            VectorImpl::Tree { .. } => self.clone(),
        }
    }

    /// Pushes a value to the back of a tree-based vector.
    fn tree_push_back(&self, value: T) -> Self {
        match &self.inner {
            VectorImpl::Tree { tree } => {
                let new_tree = tree.push_back(value);
                Self::tree(new_tree)
            },
            _ => unreachable!(),
        }
    }

    /// Pushes a value to the front of a tree-based vector.
    fn tree_push_front(&self, value: T) -> Self {
        match &self.inner {
            VectorImpl::Tree { tree } => {
                let new_tree = tree.push_front(value);
                Self::tree(new_tree)
            },
            _ => unreachable!(),
        }
    }

    /// Creates a new vector by concatenating this vector with another.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::PersistentVector;
    ///
    /// let vec1 = PersistentVector::from_slice(&[1, 2]);
    /// let vec2 = PersistentVector::from_slice(&[3, 4]);
    /// let combined = vec1.concat(&vec2);
    /// assert_eq!(combined.to_vec(), vec![1, 2, 3, 4]);
    /// ```
    pub fn concat(&self, other: &Self) -> Self {
        match (&self.inner, &other.inner) {
            (VectorImpl::Inline { elements: left }, VectorImpl::Inline { elements: right }) => {
                let iter = left.iter().chain(right.iter()).cloned();
                Self::from_iter(iter)
            },
            (VectorImpl::Inline { elements }, VectorImpl::Tree { tree }) => {
                let left_tree = RRBTree::from_elements(elements.iter().cloned());
                let merged_tree = left_tree.concat(tree);
                Self::tree(merged_tree)
            },
            (VectorImpl::Tree { tree }, VectorImpl::Inline { elements }) => {
                let right_tree = RRBTree::from_elements(elements.iter().cloned());
                let merged_tree = tree.concat(&right_tree);
                Self::tree(merged_tree)
            },
            (VectorImpl::Tree { .. }, VectorImpl::Tree { .. }) => {
                let left_tree = self.ensure_tree();
                let right_tree = other.ensure_tree();
                let merged_tree = left_tree.concat(&right_tree);
                Self::tree(merged_tree)
            },
        }
    }

    /// Ensures the vector is in tree form, converting if necessary.
    fn ensure_tree(&self) -> RRBTree<T> {
        match &self.inner {
            VectorImpl::Inline { elements } => RRBTree::from_elements(elements.iter().cloned()),
            VectorImpl::Tree { tree } => (**tree).clone(),
        }
    }

    /// Removes and returns the last element along with the new vector.
    ///
    /// Returns `None` if the vector is empty.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::PersistentVector;
    ///
    /// let vec = PersistentVector::from_slice(&[1, 2, 3]);
    /// let (new_vec, last) = vec.pop_back().unwrap();
    /// assert_eq!(last, 3);
    /// assert_eq!(new_vec.to_vec(), vec![1, 2]);
    /// ```
    pub fn pop_back(&self) -> Option<(Self, T)> {
        if self.is_empty() {
            return None;
        }

        match &self.inner {
            VectorImpl::Inline { elements } => {
                if let Some(last) = elements.last().cloned() {
                    let mut new_elements = elements.clone();
                    new_elements.pop();
                    Some((Self::inline(new_elements), last))
                } else {
                    None
                }
            },
            VectorImpl::Tree { tree } => tree
                .pop_back()
                .map(|(new_tree, value)| (Self::tree(new_tree), value)),
        }
    }

    /// Removes and returns the first element along with the new vector.
    ///
    /// Returns `None` if the vector is empty.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::PersistentVector;
    ///
    /// let vec = PersistentVector::from_slice(&[1, 2, 3]);
    /// let (new_vec, first) = vec.pop_front().unwrap();
    /// assert_eq!(first, 1);
    /// assert_eq!(new_vec.to_vec(), vec![2, 3]);
    /// ```
    pub fn pop_front(&self) -> Option<(Self, T)> {
        if self.is_empty() {
            return None;
        }

        match &self.inner {
            VectorImpl::Inline { elements } => {
                if let Some(first) = elements.first().cloned() {
                    let new_elements = SmallVec::from_iter(elements.iter().skip(1).cloned());
                    Some((Self::inline(new_elements), first))
                } else {
                    None
                }
            },
            VectorImpl::Tree { tree } => tree
                .pop_front()
                .map(|(new_tree, value)| (Self::tree(new_tree), value)),
        }
    }

    /// Splits the vector at the specified index.
    ///
    /// Returns a tuple where the first vector contains elements before the index
    /// and the second contains elements from the index onwards.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::PersistentVector;
    ///
    /// let vec = PersistentVector::from_slice(&[1, 2, 3, 4, 5]);
    /// let (left, right) = vec.split_at(2);
    /// assert_eq!(left.to_vec(), vec![1, 2]);
    /// assert_eq!(right.to_vec(), vec![3, 4, 5]);
    /// ```
    pub fn split_at(&self, index: usize) -> (Self, Self) {
        if index >= self.len() {
            return (self.clone(), Self::new());
        }
        if index == 0 {
            return (Self::new(), self.clone());
        }

        match &self.inner {
            VectorImpl::Inline { elements } => {
                let left = SmallVec::from_iter(elements.iter().take(index).cloned());
                let right = SmallVec::from_iter(elements.iter().skip(index).cloned());
                (Self::inline(left), Self::inline(right))
            },
            VectorImpl::Tree { tree } => {
                let (left_tree, right_tree) = tree.split_at(index);
                (Self::tree(left_tree), Self::tree(right_tree))
            },
        }
    }

    /// Creates a new vector containing the first `n` elements.
    ///
    /// # Examples
    ///
    /// ```rust,ignore
    /// use rustica::pvec::PersistentVector;
    ///
    /// let vec = PersistentVector::from_slice(&[1, 2, 3, 4, 5]);
    /// let taken = vec.take(3);
    /// assert_eq!(taken.to_vec(), vec![1, 2, 3]);
    /// ```
    /// Inserts an element at the specified index, shifting all elements after it.
    ///
    /// If the index is greater than or equal to the length, the element is appended to the end.
    /// If the index is 0, the element is prepended to the beginning.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::PersistentVector;
    ///
    /// let vec = PersistentVector::from_slice(&[1, 2, 4]);
    /// let vec = vec.insert(2, 3);
    /// assert_eq!(vec.to_vec(), vec![1, 2, 3, 4]);
    ///
    /// // Insert at the beginning
    /// let vec = vec.insert(0, 0);
    /// assert_eq!(vec.to_vec(), vec![0, 1, 2, 3, 4]);
    ///
    /// // Insert beyond the end appends
    /// let vec = PersistentVector::from_slice(&[1, 2]);
    /// let vec = vec.insert(100, 3);
    /// assert_eq!(vec.to_vec(), vec![1, 2, 3]);
    /// ```
    pub fn insert(&self, index: usize, value: T) -> Self {
        if index >= self.len() {
            return self.push_back(value);
        }
        if index == 0 {
            return self.push_front(value);
        }

        let (left, right) = self.split_at(index);
        left.push_back(value).concat(&right)
    }

    /// Removes the element at the specified index, returning a new vector without that element.
    ///
    /// Returns `None` if the index is out of bounds.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::PersistentVector;
    ///
    /// let vec = PersistentVector::from_slice(&[1, 2, 3, 4]);
    /// let vec = vec.remove(1).unwrap();
    /// assert_eq!(vec.to_vec(), vec![1, 3, 4]);
    ///
    /// // Out of bounds returns None
    /// let vec = PersistentVector::from_slice(&[1, 2, 3]);
    /// assert!(vec.remove(10).is_none());
    /// ```
    pub fn remove(&self, index: usize) -> Option<Self> {
        if index >= self.len() {
            return None;
        }

        if self.len() == 1 {
            return Some(Self::new());
        }

        let (left, right) = self.split_at(index);
        let right_without_first = right.split_at(1).1;
        Some(left.concat(&right_without_first))
    }

    /// Converts the persistent vector to a standard `Vec<T>`.
    ///
    /// This creates a new `Vec` containing clones of all elements.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::PersistentVector;
    ///
    /// let pvec = PersistentVector::from_slice(&[1, 2, 3]);
    /// let vec: Vec<i32> = pvec.to_vec();
    /// assert_eq!(vec, vec![1, 2, 3]);
    /// ```
    pub fn to_vec(&self) -> Vec<T> {
        self.iter().cloned().collect()
    }

    /// Consumes the vector and extracts owned values. Unique inline/tree
    /// storage is moved directly; shared tree storage falls back to cloning
    /// the shared values to preserve persistent-vector semantics.
    pub fn into_vec(self) -> Vec<T>
    where
        T: Clone,
    {
        match self.inner {
            VectorImpl::Inline { elements } => elements.into_vec(),
            VectorImpl::Tree { tree } => match Arc::try_unwrap(tree) {
                Ok(tree) => tree.into_vec(),
                Err(tree) => (0..tree.len)
                    .map(|index| {
                        tree.get(index)
                            .expect("persistent vector tree length invariant")
                            .clone()
                    })
                    .collect(),
            },
        }
    }
}

impl<T> Default for PersistentVector<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T> FromIterator<T> for PersistentVector<T> {
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        let mut iter = iter.into_iter();
        let mut inline = SmallVec::<[T; ADAPTIVE_INLINE_SIZE]>::new();
        while inline.len() < ADAPTIVE_INLINE_SIZE {
            match iter.next() {
                Some(value) => inline.push(value),
                None => {
                    return Self::inline(inline);
                },
            }
        }

        let first = iter.next();
        match first {
            None => Self::inline(inline),
            Some(first) => {
                let elements = inline.into_iter().chain(std::iter::once(first)).chain(iter);
                let tree = RRBTree::from_elements_owned(elements);
                Self::tree(tree)
            },
        }
    }
}

impl<T: Clone> Extend<T> for PersistentVector<T> {
    fn extend<I: IntoIterator<Item = T>>(&mut self, iter: I) {
        let current = std::mem::take(self);
        *self = current.into_iter().chain(iter).collect();
    }
}

impl<T> From<Vec<T>> for PersistentVector<T> {
    fn from(vec: Vec<T>) -> Self {
        Self::from_iter(vec)
    }
}

impl<T: Clone> From<PersistentVector<T>> for Vec<T> {
    fn from(pvec: PersistentVector<T>) -> Self {
        pvec.into_vec()
    }
}

impl<T: Clone> IntoIterator for PersistentVector<T> {
    type Item = T;
    type IntoIter = PersistentVectorIntoIter<T>;

    fn into_iter(self) -> Self::IntoIter {
        PersistentVectorIntoIter {
            iter: self.into_vec().into_iter(),
        }
    }
}

impl<'a, T> IntoIterator for &'a PersistentVector<T> {
    type Item = &'a T;
    type IntoIter = PersistentVectorIter<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<T> std::ops::Index<usize> for PersistentVector<T> {
    type Output = T;

    fn index(&self, index: usize) -> &Self::Output {
        self.get(index).expect("index out of bounds")
    }
}

impl<T: Clone + Debug> Debug for PersistentVector<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.inner {
            VectorImpl::Inline { elements } => {
                write!(
                    f,
                    "PersistentVector(Inline, len={}, elements={:?})",
                    self.len(),
                    elements.as_slice()
                )
            },
            VectorImpl::Tree { .. } => {
                write!(f, "PersistentVector(Tree, len={})", self.len())
            },
        }
    }
}
