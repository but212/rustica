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

/// An immutable vector data structure with structural sharing.
///
/// Operations like `push_back`, `push_front`, and `update` return new vectors
/// that share unchanged nodes with the original.
///
/// Storage is adaptive: vectors with $\le 64$ elements reside in inline storage,
/// while larger vectors use an RRB (Relaxed Radix Balanced) tree.
#[derive(Clone)]
pub struct PersistentVector<T> {
    pub(crate) inner: VectorImpl<T>,
}

/// Internal representation of the vector data.
///
/// Uses an adaptive strategy where small vectors are stored inline
/// and larger vectors use a tree structure.
#[derive(Clone, Debug)]
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
        if self.len() != other.len() {
            return false;
        }
        if let (VectorImpl::Tree { tree: t1 }, VectorImpl::Tree { tree: t2 }) =
            (&self.inner, &other.inner)
            && Arc::ptr_eq(t1, t2)
        {
            return true;
        }
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
    pub fn new() -> Self {
        Self::inline(SmallVec::new())
    }

    /// Creates a new persistent vector containing a single element.
    #[inline]
    pub fn single(value: T) -> Self {
        Self::inline(SmallVec::from_iter([value]))
    }

    /// Creates a new persistent vector containing a single element.
    #[deprecated(since = "0.16.0", note = "use PersistentVector::single instead")]
    #[inline]
    pub fn unit(value: T) -> Self {
        Self::single(value)
    }

    /// Returns the number of elements in the vector.
    ///
    pub fn len(&self) -> usize {
        self.inner.len()
    }

    /// Returns `true` if the vector contains no elements.
    ///
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Returns an iterator over the vector elements.
    ///
    pub fn iter(&self) -> PersistentVectorIter<'_, T> {
        PersistentVectorIter::new(self)
    }
}

impl<T> PersistentVector<T> {
    /// Gets a reference to the element at the specified index.
    ///
    /// Returns `None` if the index is out of bounds.
    ///
    pub fn get(&self, index: usize) -> Option<&T> {
        if index >= self.len() {
            return None;
        }

        match &self.inner {
            VectorImpl::Inline { elements } => elements.get(index),
            VectorImpl::Tree { tree } => tree.as_ref().get(index),
        }
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
    pub fn first(&self) -> Option<&T> {
        self.get(0)
    }

    /// Gets a reference to the last element.
    ///
    /// Returns `None` if the vector is empty.
    pub fn last(&self) -> Option<&T> {
        if !self.is_empty() {
            self.get(self.len() - 1)
        } else {
            None
        }
    }

    /// Applies a function to each element, accumulating the results.
    pub fn fold<B, F>(&self, init: B, f: F) -> B
    where
        F: Fn(B, &T) -> B,
    {
        self.iter().fold(init, f)
    }
}

impl<T: Clone> PersistentVector<T> {
    /// Creates a persistent vector from a slice.
    ///
    pub fn from_slice(slice: &[T]) -> Self {
        Self::from_iter(slice.iter().cloned())
    }

    /// Creates a new vector by applying a function to each element.
    ///
    pub fn map<U, F>(&self, f: F) -> PersistentVector<U>
    where
        F: Fn(&T) -> U,
    {
        PersistentVector::from_iter(self.iter().map(f))
    }

    /// Creates a new vector containing only elements that match the predicate.
    ///
    pub fn filter<F>(&self, predicate: F) -> Self
    where
        F: Fn(&T) -> bool,
    {
        Self::from_iter(self.iter().filter(|x| predicate(x)).cloned())
    }

    /// Creates a new vector by applying a function and filtering out `None` results.
    ///
    pub fn filter_map<U, F>(&self, f: F) -> PersistentVector<U>
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
    pub fn flat_map<U, F, I>(&self, f: F) -> PersistentVector<U>
    where
        F: Fn(&T) -> I,
        I: IntoIterator<Item = U>,
    {
        PersistentVector::from_iter(self.iter().flat_map(f))
    }

    /// Creates a new vector with consecutive duplicate elements removed.
    ///
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
    pub fn sorted(&self) -> Self
    where
        T: Ord,
    {
        let mut items: Vec<T> = self.iter().cloned().collect();
        items.sort();
        Self::from_iter(items)
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
            let chunk: PersistentVector<T> = iter.by_ref().take(size).cloned().collect();
            (!chunk.is_empty()).then_some(chunk)
        }))
    }

    /// Creates a new vector with an element added to the end.
    ///
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
            VectorImpl::Tree { tree } => Self::tree(tree.push_back(value)),
        }
    }

    /// Creates a new vector with an element added to the beginning.
    ///
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
            VectorImpl::Tree { tree } => Self::tree(tree.push_front(value)),
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

    /// Creates a new vector by concatenating this vector with another.
    ///
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
            (VectorImpl::Tree { tree: left }, VectorImpl::Tree { tree: right }) => {
                Self::tree(left.concat(right))
            },
        }
    }

    /// Removes and returns the last element along with the new vector.
    ///
    /// Returns `None` if the vector is empty.
    ///
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

    /// Inserts an element at the specified index, shifting all elements after it.
    ///
    /// If the index is greater than or equal to the length, the element is appended to the end.
    /// If the index is 0, the element is prepended to the beginning.
    ///
    pub fn insert(&self, index: usize, value: T) -> Self {
        if index >= self.len() {
            return self.push_back(value);
        }
        if index == 0 {
            return self.push_front(value);
        }

        if let VectorImpl::Inline { elements } = &self.inner
            && elements.len() < ADAPTIVE_INLINE_SIZE
        {
            let mut new_elements = elements.clone();
            new_elements.insert(index, value);
            return Self::inline(new_elements);
        }

        let (left, right) = self.split_at(index);
        left.push_back(value).concat(&right)
    }

    /// Removes the element at the specified index, returning a new vector without that element.
    ///
    /// Returns `None` if the index is out of bounds.
    ///
    pub fn remove(&self, index: usize) -> Option<Self> {
        if index >= self.len() {
            return None;
        }

        if self.len() == 1 {
            return Some(Self::new());
        }

        if let VectorImpl::Inline { elements } = &self.inner {
            let mut new_elements = elements.clone();
            new_elements.remove(index);
            return Some(Self::inline(new_elements));
        }

        if index == 0 {
            return self.pop_front().map(|(v, _)| v);
        }
        if index == self.len() - 1 {
            return self.pop_back().map(|(v, _)| v);
        }

        let (left, right) = self.split_at(index);
        let right_without_first = right.split_at(1).1;
        Some(left.concat(&right_without_first))
    }

    /// Converts the persistent vector to a standard `Vec<T>`.
    ///
    /// This creates a new `Vec` containing clones of all elements.
    ///
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
                Err(tree) => {
                    let temp = PersistentVector {
                        inner: VectorImpl::Tree { tree },
                    };
                    temp.iter().cloned().collect()
                },
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
                let tree = RRBTree::from_elements(elements);
                Self::tree(tree)
            },
        }
    }
}

impl<T: Clone> Extend<T> for PersistentVector<T> {
    fn extend<I: IntoIterator<Item = T>>(&mut self, iter: I) {
        for item in iter {
            *self = self.push_back(item);
        }
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
        PersistentVectorIntoIter::new(self)
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

impl<T: Debug> Debug for PersistentVector<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_list().entries(self.iter()).finish()
    }
}

#[cfg(test)]
mod read_only_non_clone_tests {
    use super::*;

    struct NonClone(i32);

    #[test]
    fn non_clone_elements_support_read_only_methods() {
        let v = PersistentVector::single(NonClone(42));
        assert_eq!(v.first().map(|x| x.0), Some(42));
        assert_eq!(v.last().map(|x| x.0), Some(42));
        assert_eq!(v.try_get(0).map(|x| x.0), Ok(42));
        assert_eq!(v.fold(0, |acc, x| acc + x.0), 42);
    }

    #[test]
    fn mapping_supports_non_clone_output_type() {
        let v = PersistentVector::from_slice(&[1, 2, 3]);
        let mapped = v.map(|&x| NonClone(x));
        assert_eq!(mapped.len(), 3);
        assert_eq!(mapped.get(1).map(|x| x.0), Some(2));

        let filtered = v.filter_map(|&x| (x > 1).then_some(NonClone(x)));
        assert_eq!(filtered.len(), 2);
        assert_eq!(filtered.get(0).map(|x| x.0), Some(2));

        let flattened = v.flat_map(|&x| [NonClone(x), NonClone(x * 10)]);
        assert_eq!(flattened.len(), 6);
        assert_eq!(flattened.get(1).map(|x| x.0), Some(10));
    }

    #[derive(Debug, PartialEq, Eq)]
    struct NonCloneDebug(i32);

    #[test]
    fn test_debug_non_clone() {
        let v = PersistentVector::single(NonCloneDebug(42));
        assert_eq!(format!("{v:?}"), "[NonCloneDebug(42)]");
    }

    #[test]
    fn test_debug_tree_elements() {
        let v: PersistentVector<i32> = (0..100).collect();
        let expected = format!("{:?}", (0..100).collect::<Vec<_>>());
        assert_eq!(format!("{v:?}"), expected);
    }

    #[test]
    fn test_extend_preserves_elements() {
        let mut v: PersistentVector<i32> = (0..1000).collect();
        v.extend(1000..1005);
        assert_eq!(v.len(), 1005);
        assert_eq!(v.to_vec(), (0..1005).collect::<Vec<_>>());
    }

    #[test]
    fn test_inline_insert_fast_path() {
        let v = PersistentVector::from_slice(&[1, 2, 4, 5]);
        let inserted = v.insert(2, 3);
        assert_eq!(inserted.to_vec(), vec![1, 2, 3, 4, 5]);
        assert!(matches!(inserted.inner, VectorImpl::Inline { .. }));
    }

    #[test]
    fn test_inline_remove_fast_path() {
        let v = PersistentVector::from_slice(&[1, 2, 99, 3, 4]);
        let removed = v.remove(2).expect("valid index");
        assert_eq!(removed.to_vec(), vec![1, 2, 3, 4]);
        assert!(matches!(removed.inner, VectorImpl::Inline { .. }));
    }

    #[test]
    fn test_eq_fast_path() {
        let v1: PersistentVector<i32> = (0..100).collect();
        let v2 = v1.clone();
        assert_eq!(v1, v2);

        let v3: PersistentVector<i32> = (0..99).collect();
        assert_ne!(v1, v3);
    }

    #[test]
    fn test_chunk_direct() {
        let v: PersistentVector<i32> = (0..10).collect();
        let chunks = v.chunk(3);
        assert_eq!(chunks.len(), 4);
        assert_eq!(chunks[0].to_vec(), vec![0, 1, 2]);
        assert_eq!(chunks[1].to_vec(), vec![3, 4, 5]);
        assert_eq!(chunks[2].to_vec(), vec![6, 7, 8]);
        assert_eq!(chunks[3].to_vec(), vec![9]);

        let empty = PersistentVector::<i32>::new().chunk(5);
        assert!(empty.is_empty());
    }

    #[test]
    fn test_lazy_into_iter_interleaved() {
        let v: PersistentVector<i32> = (0..200).collect();
        let mut it = v.into_iter();
        assert_eq!(it.next(), Some(0));
        assert_eq!(it.next_back(), Some(199));
        assert_eq!(it.next(), Some(1));
        assert_eq!(it.next_back(), Some(198));
        assert_eq!(it.len(), 196);

        let remaining: Vec<i32> = it.collect();
        assert_eq!(remaining.len(), 196);
        assert_eq!(remaining, (2..198).collect::<Vec<_>>());
    }
}
