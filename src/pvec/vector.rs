//! Persistent Vector Implementation
//!
//! This module provides the main `PersistentVector` type, which is the primary 
//! interface for working with persistent vectors.

use std::iter::FromIterator;
use std::ops::{Index, RangeBounds};
use std::cmp::{min, max};
use std::fmt::{self, Debug, Formatter};
use std::hash::{Hash, Hasher};
use std::cmp::Ordering;
use std::convert::AsRef;

use crate::pvec::tree::RRBTree;
use crate::pvec::memory::MemoryManager;
use crate::pvec::iterator::{Iter, IntoIter, ChunksIter, SortedIter};
use crate::pvec::chunk::CHUNK_SIZE;

/// A persistent vector implementation.
///
/// This is an immutable sequence data structure that provides efficient
/// operations with structural sharing between versions. It's ideal for
/// functional programming patterns and concurrent applications.
#[derive(Clone)]
pub struct PersistentVector<T: Clone> {
    /// The internal tree structure
    tree: RRBTree<T>,
}

impl<T: Clone> PersistentVector<T> {
    /// Create a new empty vector.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::PersistentVector;
    ///
    /// let vector: PersistentVector<i32> = PersistentVector::new();
    /// assert!(vector.is_empty());
    /// ```
    pub fn new() -> Self {
        Self {
            tree: RRBTree::new(MemoryManager::default()),
        }
    }
    
    /// Create a new empty vector with a custom memory manager.
    ///
    /// This allows you to specify the allocation strategy and other memory-related
    /// parameters for better performance in specific use cases.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::{PersistentVector, MemoryManager, AllocationStrategy};
    ///
    /// let manager = MemoryManager::new(AllocationStrategy::Pooled);
    /// let vector: PersistentVector<i32> = PersistentVector::with_memory_manager(manager);
    /// ```
    pub fn with_memory_manager(manager: MemoryManager<T>) -> Self {
        Self {
            tree: RRBTree::new(manager),
        }
    }
    
    /// Create a vector with one element.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::PersistentVector;
    ///
    /// let vector = PersistentVector::unit(42);
    /// assert_eq!(vector.len(), 1);
    /// assert_eq!(vector.get(0), Some(&42));
    /// ```
    pub fn unit(value: T) -> Self {
        let mut vector = Self::new();
        vector = vector.push_back(value);
        vector
    }
    
    /// Get the number of elements in the vector.
    ///
    /// This operation is O(1) as the size is stored directly.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec;
    ///
    /// let vector = pvec![1, 2, 3, 4];
    /// assert_eq!(vector.len(), 4);
    /// ```
    pub fn len(&self) -> usize {
        self.tree.len()
    }
    
    /// Check if the vector is empty.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::PersistentVector;
    ///
    /// let vector: PersistentVector<i32> = PersistentVector::new();
    /// assert!(vector.is_empty());
    ///
    /// let vector = vector.push_back(42);
    /// assert!(!vector.is_empty());
    /// ```
    pub fn is_empty(&self) -> bool {
        self.tree.is_empty()
    }
    
    /// Get a reference to the element at the specified index.
    ///
    /// Returns `None` if the index is out of bounds.
    /// This operation is O(log n) in the worst case, but approaches O(1)
    /// for repeated access to the same region of the vector due to caching.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec;
    ///
    /// let vector = pvec![10, 20, 30, 40, 50];
    /// assert_eq!(vector.get(2), Some(&30));
    /// assert_eq!(vector.get(10), None); // Out of bounds
    /// ```
    pub fn get(&self, index: usize) -> Option<&T> {
        if index >= self.len() {
            return None;
        }

        // Directly delegate to the tree's get method which handles tail checking internally
        self.tree.get(index)
    }
    
    /// Add an element to the end of the vector.
    ///
    /// This operation is amortized O(1) due to the optimized tree structure
    /// and tail buffering.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec;
    ///
    /// let v1 = pvec![1, 2, 3];
    /// let v2 = v1.push_back(4);
    ///
    /// // Original vector is unchanged
    /// assert_eq!(v1.len(), 3);
    ///
    /// // New vector has the added element
    /// assert_eq!(v2.len(), 4);
    /// assert_eq!(v2.get(3), Some(&4));
    /// ```
    pub fn push_back(&self, value: T) -> Self {
        Self {
            tree: self.tree.push_back(value),
        }
    }
    
    /// Add an element to the beginning of the vector.
    ///
    /// This operation is amortized O(1) for small vectors but becomes
    /// O(log n) for larger ones.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec;
    ///
    /// let v1 = pvec![2, 3, 4];
    /// let v2 = v1.push_front(1);
    ///
    /// // Original vector is unchanged
    /// assert_eq!(v1.len(), 3);
    ///
    /// // New vector has the added element
    /// assert_eq!(v2.len(), 4);
    /// assert_eq!(v2.get(0), Some(&1));
    /// ```
    pub fn push_front(&self, value: T) -> Self {
        Self {
            tree: self.tree.push_front(value),
        }
    }
    
    /// Remove and return the last element from the vector.
    ///
    /// Returns `None` if the vector is empty.
    /// This operation is amortized O(1) due to the tail buffer.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec;
    ///
    /// let v1 = pvec![1, 2, 3, 4];
    /// let (v2, value) = v1.pop_back().unwrap();
    ///
    /// assert_eq!(value, 4);
    /// assert_eq!(v2.len(), 3);
    /// ```
    pub fn pop_back(&self) -> Option<(Self, T)> {
        if self.is_empty() {
            return None;
        }
        
        self.tree.pop_back().map(|(tree, value)| (Self { tree }, value))
    }
    
    /// Remove and return the first element from the vector.
    ///
    /// Returns `None` if the vector is empty.
    /// This operation is O(log n).
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec;
    ///
    /// let v1 = pvec![1, 2, 3, 4];
    /// let (v2, value) = v1.pop_front().unwrap();
    ///
    /// assert_eq!(value, 1);
    /// assert_eq!(v2.len(), 3);
    /// ```
    pub fn pop_front(&self) -> Option<(Self, T)> {
        if self.is_empty() {
            return None;
        }
        
        self.tree.pop_front().map(|(tree, value)| (Self { tree }, value))
    }
    
    /// Create a new vector with the element at the given index updated.
    ///
    /// Returns `None` if the index is out of bounds.
    /// This operation is O(log n).
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec;
    ///
    /// let v1 = pvec![1, 2, 3, 4];
    /// let v2 = v1.update(2, 30).unwrap();
    ///
    /// // Original vector is unchanged
    /// assert_eq!(v1.get(2), Some(&3));
    ///
    /// // New vector has the updated element
    /// assert_eq!(v2.get(2), Some(&30));
    /// ```
    pub fn update(&self, index: usize, value: T) -> Option<Self> {
        // Check index bounds before trying to update
        if index >= self.len() {
            return None;
        }
        
        // Safely update the tree and create a new vector
        self.tree.update(index, value).map(|tree| Self { tree })
    }
    
    /// Concatenate two vectors.
    ///
    /// This operation is O(log n) where n is the size of the larger vector.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec;
    ///
    /// let v1 = pvec![1, 2, 3];
    /// let v2 = pvec![4, 5, 6];
    /// let v3 = v1.concat(&v2);
    ///
    /// assert_eq!(v3.len(), 6);
    /// assert_eq!(v3.get(0), Some(&1));
    /// assert_eq!(v3.get(5), Some(&6));
    /// ```
    pub fn concat(&self, other: &Self) -> Self {
        // Handle empty vectors
        if self.is_empty() {
            return other.clone();
        }
        if other.is_empty() {
            return self.clone();
        }

        // Create a new vector by combining the tree structure
        Self {
            tree: self.tree.concat(&other.tree),
        }
    }
    
    /// Split the vector at the given index.
    ///
    /// Returns a tuple with two vectors: one containing elements before the index,
    /// and another containing elements from the index onwards.
    /// This operation is O(log n).
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec;
    ///
    /// let vector = pvec![1, 2, 3, 4, 5, 6];
    /// let (left, right) = vector.split_at(3);
    ///
    /// assert_eq!(left.len(), 3);
    /// assert_eq!(right.len(), 3);
    ///
    /// assert_eq!(left.get(2), Some(&3));
    /// assert_eq!(right.get(0), Some(&4));
    /// ```
    pub fn split_at(&self, index: usize) -> (Self, Self) {
        let (left_tree, right_tree) = self.tree.split_at(index);
        (Self { tree: left_tree }, Self { tree: right_tree })
    }
    
    /// Create a vector containing only the first n elements.
    ///
    /// If n is greater than the length of the vector, the entire vector is returned.
    /// This operation is O(log n).
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec;
    ///
    /// let vector = pvec![1, 2, 3, 4, 5];
    /// let prefix = vector.take(3);
    ///
    /// assert_eq!(prefix.len(), 3);
    /// assert_eq!(prefix.get(0), Some(&1));
    /// assert_eq!(prefix.get(2), Some(&3));
    /// ```
    pub fn take(&self, n: usize) -> Self {
        if n >= self.len() {
            return self.clone();
        }
        
        let (left, _) = self.split_at(n);
        left
    }
    
    /// Create a vector with the first n elements removed.
    ///
    /// If n is greater than the length of the vector, an empty vector is returned.
    /// This operation is O(log n).
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec;
    ///
    /// let vector = pvec![1, 2, 3, 4, 5];
    /// let suffix = vector.skip(2);
    ///
    /// assert_eq!(suffix.len(), 3);
    /// assert_eq!(suffix.get(0), Some(&3));
    /// assert_eq!(suffix.get(2), Some(&5));
    /// ```
    pub fn skip(&self, n: usize) -> Self {
        if n >= self.len() {
            return Self::new();
        }
        
        let (_, right) = self.split_at(n);
        right
    }
    
    /// Get an iterator over the elements of the vector.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec;
    ///
    /// let vector = pvec![1, 2, 3];
    /// let mut sum = 0;
    ///
    /// for &value in vector.iter() {
    ///     sum += value;
    /// }
    ///
    /// assert_eq!(sum, 6);
    /// ```
    pub fn iter(&self) -> Iter<'_, T> {
        Iter::new(self)
    }
    
    /// Get an iterator over chunks of elements.
    ///
    /// This is useful for parallel processing or when working with large vectors.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec;
    ///
    /// let vector = pvec![1, 2, 3, 4, 5, 6, 7, 8];
    /// let mut chunk_sizes = vec![];
    ///
    /// for chunk in vector.chunks() {
    ///     chunk_sizes.push(chunk.len());
    /// }
    ///
    /// // Exact chunk sizes depend on internal structure
    /// assert!(chunk_sizes.iter().sum::<usize>() == 8);
    /// ```
    pub fn chunks(&self) -> ChunksIter<'_, T> {
        ChunksIter::with_default_sizes(self)
    }
    
    /// Get an iterator over chunks with custom size parameters.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec;
    ///
    /// let vector = pvec![1, 2, 3, 4, 5, 6, 7, 8];
    /// let small_chunks = vector.chunks_sized(2, 3);
    /// ```
    pub fn chunks_sized(&self, min_size: usize, max_size: usize) -> ChunksIter<'_, T> {
        ChunksIter::new(self, min_size, max_size)
    }
    
    /// Get an iterator over elements in sorted order.
    ///
    /// This doesn't modify the vector but yields elements in sorted order.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec;
    ///
    /// let vector = pvec![3, 1, 4, 2];
    /// let sorted_elements: Vec<_> = vector.sorted_iter().cloned().collect();
    ///
    /// assert_eq!(sorted_elements, vec![1, 2, 3, 4]);
    /// // Original vector is unchanged
    /// assert_eq!(vector.get(0), Some(&3));
    /// ```
    pub fn sorted_iter(&self) -> SortedIter<'_, T>
    where
        T: Ord,
    {
        SortedIter::new(self)
    }
    
    /// Check if the vector contains a given value.
    ///
    /// This operation is O(n) as it needs to scan the entire vector.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec;
    ///
    /// let vector = pvec![1, 2, 3, 4, 5];
    /// assert!(vector.contains(&3));
    /// assert!(!vector.contains(&10));
    /// ```
    pub fn contains(&self, value: &T) -> bool
    where
        T: PartialEq,
    {
        self.iter().any(|item| item == value)
    }
    
    /// Find the first index of a given value in the vector.
    ///
    /// Returns `None` if the value is not found.
    /// This operation is O(n) as it needs to scan the vector.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec;
    ///
    /// let vector = pvec![10, 20, 30, 20, 40];
    /// assert_eq!(vector.index_of(&20), Some(1)); // First occurrence
    /// assert_eq!(vector.index_of(&50), None);     // Not found
    /// ```
    pub fn index_of(&self, value: &T) -> Option<usize>
    where
        T: PartialEq,
    {
        for (i, item) in self.iter().enumerate() {
            if item == value {
                return Some(i);
            }
        }
        None
    }
    
    /// Binary search for a value in a sorted vector.
    ///
    /// Returns `Ok(index)` if the value is found, or `Err(insertion_point)`
    /// if not found, indicating where the value should be inserted to maintain order.
    /// This operation is O(log n).
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec;
    ///
    /// let vector = pvec![10, 20, 30, 40, 50];
    /// assert_eq!(vector.binary_search(&30), Ok(2));
    /// assert_eq!(vector.binary_search(&25), Err(2)); // Would be inserted before 30
    /// ```
    pub fn binary_search(&self, value: &T) -> Result<usize, usize>
    where
        T: Ord,
    {
        self.binary_search_by(|item| item.cmp(value))
    }
    
    /// Binary search with a custom comparison function.
    ///
    /// This operation is O(log n).
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec;
    /// use std::cmp::Ordering;
    ///
    /// let vector = pvec![10, 20, 30, 40, 50];
    /// let result = vector.binary_search_by(|&x| {
    ///     if x < 25 { Ordering::Less }
    ///     else if x > 25 { Ordering::Greater }
    ///     else { Ordering::Equal }
    /// });
    /// assert_eq!(result, Err(2)); // 25 would be inserted before 30
    /// ```
    pub fn binary_search_by<F>(&self, mut f: F) -> Result<usize, usize>
    where
        F: FnMut(&T) -> Ordering,
    {
        let mut size = self.len();
        if size == 0 {
            return Err(0);
        }
        
        let mut base = 0;
        while size > 1 {
            let half = size / 2;
            let mid = base + half;
            base = match f(self.get(mid).unwrap()) {
                Ordering::Greater => base,
                _ => mid,
            };
            size -= half;
        }
        
        match f(self.get(base).unwrap()) {
            Ordering::Equal => Ok(base),
            Ordering::Greater => Err(base),
            Ordering::Less => Err(base + 1),
        }
    }
    
    /// Binary search by a key extracted from each element.
    ///
    /// This operation is O(log n).
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec;
    ///
    /// let vector = pvec![(0, "a"), (1, "b"), (2, "c"), (3, "d")];
    /// assert_eq!(vector.binary_search_by_key(&2, |&(k, _)| k), Ok(2));
    /// ```
    pub fn binary_search_by_key<B, F>(&self, key: &B, mut f: F) -> Result<usize, usize>
    where
        F: FnMut(&T) -> B,
        B: Ord,
    {
        self.binary_search_by(|item| f(item).cmp(key))
    }
    
    /// Get the optimal chunk size at the given index.
    ///
    /// This is an internal method used by the chunks iterator.
    pub(crate) fn get_chunk(&self, index: usize, min_size: usize, max_size: usize) -> usize {
        if index >= self.len() {
            return 0;
        }
        
        // Try to align with the tree's natural chunks for better performance
        let remaining = self.len() - index;
        let default_size = min(CHUNK_SIZE, remaining);
        
        // Ensure the chunk size is within the specified bounds
        min(max(min_size, default_size), max(max_size, min_size))
    }
}

impl<T: Clone> AsRef<[T]> for PersistentVector<T> {
    fn as_ref(&self) -> &[T] {
        let vec = self.iter().cloned().collect::<Vec<T>>();
        Box::leak(vec.into_boxed_slice())
    }
}

impl<T: Clone> Default for PersistentVector<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T: Clone + Debug> Debug for PersistentVector<T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> fmt::Result {
        f.write_str("pvec![")?;
        let mut first = true;
        for item in self.iter().take(10) {
            if !first {
                f.write_str(", ")?;
            }
            item.fmt(f)?;
            first = false;
        }
        if self.len() > 10 {
            f.write_str(", ...")?;
        }
        f.write_str("]")
    }
}

impl<T: Clone + PartialEq> PartialEq for PersistentVector<T> {
    fn eq(&self, other: &Self) -> bool {
        if self.len() != other.len() {
            return false;
        }
        
        for i in 0..self.len() {
            if self.get(i) != other.get(i) {
                return false;
            }
        }
        
        true
    }
}

impl<T: Clone + Eq> Eq for PersistentVector<T> {}

impl<T: Clone + PartialOrd> PartialOrd for PersistentVector<T> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        for i in 0..min(self.len(), other.len()) {
            match self.get(i).partial_cmp(&other.get(i)) {
                Some(Ordering::Equal) => {},
                non_eq => return non_eq,
            }
        }
        
        self.len().partial_cmp(&other.len())
    }
}

impl<T: Clone + Ord> Ord for PersistentVector<T> {
    fn cmp(&self, other: &Self) -> Ordering {
        for i in 0..min(self.len(), other.len()) {
            match self.get(i).cmp(&other.get(i)) {
                Ordering::Equal => {},
                non_eq => return non_eq,
            }
        }
        
        self.len().cmp(&other.len())
    }
}

impl<T: Clone + Hash> Hash for PersistentVector<T> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.len().hash(state);
        for item in self.iter() {
            item.hash(state);
        }
    }
}

impl<T: Clone> FromIterator<T> for PersistentVector<T> {
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        let mut vector = Self::new();
        for item in iter {
            vector = vector.push_back(item);
        }
        vector
    }
}

impl<T: Clone> IntoIterator for PersistentVector<T> {
    type Item = T;
    type IntoIter = IntoIter<T>;
    
    fn into_iter(self) -> Self::IntoIter {
        IntoIter::new(self)
    }
}

impl<'a, T: Clone> IntoIterator for &'a PersistentVector<T> {
    type Item = &'a T;
    type IntoIter = Iter<'a, T>;
    
    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<T: Clone> Index<usize> for PersistentVector<T> {
    type Output = T;
    
    fn index(&self, index: usize) -> &Self::Output {
        match self.get(index) {
            Some(value) => value,
            None => panic!("index out of bounds"),
        }
    }
}

impl<T: Clone> From<Vec<T>> for PersistentVector<T> {
    fn from(vec: Vec<T>) -> Self {
        if vec.is_empty() {
            return Self::new();
        }
        
        // Create a new vector and add all elements
        let mut result = Self::new();
        for item in vec {
            result = result.push_back(item);
        }
        result
    }
}

impl<T: Clone> From<&[T]> for PersistentVector<T> {
    fn from(slice: &[T]) -> Self {
        if slice.is_empty() {
            return Self::new();
        }
        
        // Create a new vector and add all elements
        let mut result = Self::new();
        for item in slice {
            result = result.push_back(item.clone());
        }
        result
    }
}

// Additional utility methods

impl<T: Clone> PersistentVector<T> {
    /// Create a new vector from a given range of this vector.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec;
    ///
    /// let vector = pvec![0, 1, 2, 3, 4, 5];
    /// let slice = vector.slice(2..5);
    ///
    /// assert_eq!(slice.len(), 3);
    /// assert_eq!(slice.get(0), Some(&2));
    /// assert_eq!(slice.get(2), Some(&4));
    /// ```
    pub fn slice<R>(&self, range: R) -> Self
    where
        R: RangeBounds<usize>
    {
        use std::ops::Bound;
        
        let start = match range.start_bound() {
            Bound::Included(&n) => n,
            Bound::Excluded(&n) => n + 1,
            Bound::Unbounded => 0,
        };
        
        let end = match range.end_bound() {
            Bound::Included(&n) => n + 1,
            Bound::Excluded(&n) => n,
            Bound::Unbounded => self.len(),
        };
        
        if start >= end || start >= self.len() {
            return Self::new();
        }
        
        let capped_end = min(end, self.len());
        let (_, right) = self.split_at(start);
        let (result, _) = right.split_at(capped_end - start);
        
        result
    }

    /// Map a function over all elements to create a new vector.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec;
    ///
    /// let vector = pvec![1, 2, 3, 4];
    /// let doubled = vector.map(|x| x * 2);
    ///
    /// assert_eq!(doubled.get(0), Some(&2));
    /// assert_eq!(doubled.get(3), Some(&8));
    /// ```
    pub fn map<F, B>(&self, mut f: F) -> PersistentVector<B>
    where
        F: FnMut(&T) -> B,
        B: Clone,
    {
        self.iter().map(|item| f(item)).collect()
    }
    
    /// Filter elements based on a predicate.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec;
    ///
    /// let vector = pvec![1, 2, 3, 4, 5, 6];
    /// let evens = vector.filter(|&x| x % 2 == 0);
    ///
    /// assert_eq!(evens.len(), 3);
    /// assert_eq!(evens.get(0), Some(&2));
    /// assert_eq!(evens.get(2), Some(&6));
    /// ```
    pub fn filter<F>(&self, mut predicate: F) -> Self
    where
        F: FnMut(&T) -> bool,
    {
        self.iter().filter(|item| predicate(item)).cloned().collect()
    }
    
    /// Create a new vector with an element inserted at the specified index.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec;
    ///
    /// let vector = pvec![1, 2, 4, 5];
    /// let inserted = vector.insert(2, 3);
    ///
    /// assert_eq!(inserted.len(), 5);
    /// assert_eq!(inserted.get(2), Some(&3));
    /// ```
    pub fn insert(&self, index: usize, value: T) -> Self {
        if index > self.len() {
            return self.clone(); // Index out of bounds, return unchanged
        }
        
        if index == 0 {
            return self.push_front(value);
        }
        
        if index == self.len() {
            return self.push_back(value);
        }
        
        // Split, insert, and concatenate
        let (left, right) = self.split_at(index);
        left.push_back(value).concat(&right)
    }
    
    /// Create a new vector with the element at the specified index removed.
    ///
    /// Returns the original vector if the index is out of bounds.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec;
    ///
    /// let vector = pvec![1, 2, 3, 4, 5];
    /// let removed = vector.remove(2);
    ///
    /// assert_eq!(removed.len(), 4);
    /// assert_eq!(removed.get(1), Some(&2));
    /// assert_eq!(removed.get(2), Some(&4));
    /// ```
    pub fn remove(&self, index: usize) -> Self {
        if index >= self.len() {
            return self.clone(); // Index out of bounds, return unchanged
        }
        
        if index == 0 {
            return match self.pop_front() {
                Some((new_vec, _)) => new_vec,
                None => self.clone(),
            };
        }
        
        if index == self.len() - 1 {
            return match self.pop_back() {
                Some((new_vec, _)) => new_vec,
                None => self.clone(),
            };
        }
        
        // Split, remove, and concatenate
        let (left, right) = self.split_at(index);
        let (right_without_first, _) = right.pop_front().unwrap();
        left.concat(&right_without_first)
    }
    
    /// Sort the vector using the natural ordering of its elements.
    ///
    /// This operation is O(n log n).
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec;
    ///
    /// let vector = pvec![3, 1, 4, 2, 5];
    /// let sorted = vector.sort();
    ///
    /// assert_eq!(sorted.get(0), Some(&1));
    /// assert_eq!(sorted.get(4), Some(&5));
    /// ```
    pub fn sort(&self) -> Self
    where
        T: Ord,
    {
        self.sort_by(|a, b| a.cmp(b))
    }
    
    /// Sort the vector using a custom comparison function.
    ///
    /// This operation is O(n log n).
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec;
    ///
    /// let vector = pvec![3, 1, 4, 2, 5];
    /// let reverse_sorted = vector.sort_by(|a, b| b.cmp(a));
    ///
    /// assert_eq!(reverse_sorted.get(0), Some(&5));
    /// assert_eq!(reverse_sorted.get(4), Some(&1));
    /// ```
    pub fn sort_by<F>(&self, mut compare: F) -> Self
    where
        F: FnMut(&T, &T) -> Ordering,
    {
        let mut elements: Vec<_> = self.iter().cloned().collect();
        elements.sort_by(|a, b| compare(a, b));
        elements.into_iter().collect()
    }
    
    /// Sort the vector by a key extracted from each element.
    ///
    /// This operation is O(n log n).
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec;
    ///
    /// let vector = pvec![(2, "b"), (1, "a"), (3, "c")];
    /// let sorted = vector.sort_by_key(|&(k, _)| k);
    ///
    /// assert_eq!(sorted.get(0), Some(&(1, "a")));
    /// assert_eq!(sorted.get(2), Some(&(3, "c")));
    /// ```
    pub fn sort_by_key<K, F>(&self, mut f: F) -> Self
    where
        F: FnMut(&T) -> K,
        K: Ord,
    {
        self.sort_by(|a, b| f(a).cmp(&f(b)))
    }
    
    /// Reverse the order of elements in the vector.
    ///
    /// This operation is O(n).
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec;
    ///
    /// let vector = pvec![1, 2, 3, 4, 5];
    /// let reversed = vector.reverse();
    ///
    /// assert_eq!(reversed.get(0), Some(&5));
    /// assert_eq!(reversed.get(4), Some(&1));
    /// ```
    pub fn reverse(&self) -> Self {
        let mut result = Self::new();
        for item in self.iter() {
            result = result.push_front(item.clone());
        }
        result
    }
    
    /// Find the first element that matches a predicate.
    ///
    /// Returns `None` if no element matches.
    /// This operation is O(n).
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec;
    ///
    /// let vector = pvec![1, 2, 3, 4, 5];
    /// let found = vector.find(|&x| x > 3);
    ///
    /// assert_eq!(found, Some(&4));
    /// ```
    pub fn find<P>(&self, mut predicate: P) -> Option<&T>
    where
        P: FnMut(&T) -> bool,
    {
        self.iter().find(|item| predicate(item))
    }
    
    /// Return the first element of the vector.
    ///
    /// Returns `None` if the vector is empty.
    /// This operation is O(log n).
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec;
    ///
    /// let vector = pvec![1, 2, 3];
    /// assert_eq!(vector.first(), Some(&1));
    ///
    /// let empty: PersistentVector<i32> = pvec![];
    /// assert_eq!(empty.first(), None);
    /// ```
    pub fn first(&self) -> Option<&T> {
        self.get(0)
    }
    
    /// Return the last element of the vector.
    ///
    /// Returns `None` if the vector is empty.
    /// This operation is O(log n).
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec;
    ///
    /// let vector = pvec![1, 2, 3];
    /// assert_eq!(vector.last(), Some(&3));
    ///
    /// let empty: PersistentVector<i32> = pvec![];
    /// assert_eq!(empty.last(), None);
    /// ```
    pub fn last(&self) -> Option<&T> {
        if self.is_empty() {
            None
        } else {
            self.get(self.len() - 1)
        }
    }
    
    /// Apply a function to each element and return a new vector with the results.
    ///
    /// This is similar to `map` but allows access to the element's index.
    /// This operation is O(n).
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec;
    ///
    /// let vector = pvec!["a", "b", "c"];
    /// let indexed = vector.enumerate_map(|i, &s| format!("{}-{}", i, s));
    ///
    /// assert_eq!(indexed.get(0), Some(&"0-a".to_string()));
    /// assert_eq!(indexed.get(2), Some(&"2-c".to_string()));
    /// ```
    pub fn enumerate_map<F, B>(&self, mut f: F) -> PersistentVector<B>
    where
        F: FnMut(usize, &T) -> B,
        B: Clone,
    {
        self.iter()
            .enumerate()
            .map(|(i, item)| f(i, item))
            .collect()
    }
    
    /// Fold the vector into a single value.
    ///
    /// This operation is O(n).
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec;
    ///
    /// let vector = pvec![1, 2, 3, 4, 5];
    /// let sum = vector.fold(0, |acc, &x| acc + x);
    ///
    /// assert_eq!(sum, 15);
    /// ```
    pub fn fold<B, F>(&self, init: B, mut f: F) -> B
    where
        F: FnMut(B, &T) -> B,
    {
        let mut result = init;
        for item in self.iter() {
            result = f(result, item);
        }
        result
    }
    
    /// Return a vector of all prefixes of the current vector.
    ///
    /// This operation is O(n log n).
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec;
    ///
    /// let vector = pvec![1, 2, 3];
    /// let prefixes = vector.prefixes();
    ///
    /// assert_eq!(prefixes.len(), 4);
    /// assert_eq!(prefixes.get(0).unwrap().len(), 0); // empty prefix
    /// assert_eq!(prefixes.get(1).unwrap().len(), 1);
    /// assert_eq!(prefixes.get(3).unwrap().len(), 3);
    /// ```
    pub fn prefixes(&self) -> PersistentVector<Self> {
        let mut result = PersistentVector::new();
        result = result.push_back(Self::new()); // Empty prefix
        
        let mut prefix = Self::new();
        for i in 0..self.len() {
            prefix = prefix.push_back(self.get(i).cloned().unwrap());
            result = result.push_back(prefix.clone());
        }
        
        result
    }
    
    /// Return a vector of all suffixes of the current vector.
    ///
    /// This operation is O(n log n).
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec;
    ///
    /// let vector = pvec![1, 2, 3];
    /// let suffixes = vector.suffixes();
    ///
    /// assert_eq!(suffixes.len(), 4);
    /// assert_eq!(suffixes.get(0).unwrap().len(), 3); // full vector
    /// assert_eq!(suffixes.get(1).unwrap().len(), 2);
    /// assert_eq!(suffixes.get(3).unwrap().len(), 0); // empty suffix
    /// ```
    pub fn suffixes(&self) -> PersistentVector<Self> {
        let mut result = PersistentVector::new();
        result = result.push_back(self.clone()); // Full vector
        
        for i in 1..=self.len() {
            result = result.push_back(self.skip(i));
        }
        
        result
    }
    
    /// Group elements by a key function.
    ///
    /// Returns a vector of (key, vector) pairs where each vector contains
    /// all elements with the same key.
    /// This operation is O(n log n).
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec;
    ///
    /// let vector = pvec![1, 2, 3, 4, 5, 6];
    /// let grouped = vector.group_by(|&x| x % 3);
    ///
    /// assert_eq!(grouped.len(), 3);
    ///
    /// // Find the group for key 0 (elements divisible by 3)
    /// let group_0 = grouped.iter().find(|&(k, _)| *k == 0).unwrap();
    /// assert_eq!(group_0.1.len(), 2); // [3, 6]
    /// ```
    pub fn group_by<K, F>(&self, mut key_fn: F) -> PersistentVector<(K, Self)>
    where
        F: FnMut(&T) -> K,
        K: Ord + Clone,
    {
        // Create a map of key -> vector
        let mut groups: std::collections::BTreeMap<K, Self> = std::collections::BTreeMap::new();
        
        for item in self.iter() {
            let key = key_fn(item);
            let group = groups.entry(key.clone()).or_insert_with(Self::new);
            *group = group.push_back(item.clone());
        }
        
        // Convert the map to a vector of pairs
        groups.into_iter().collect()
    }
}

// Additional utility functions

/// Create a vector from a given range of integers.
///
/// # Examples
///
/// ```
/// use rustica::{pvec_range, PersistentVector};
///
/// let vector = pvec_range(1..5);
/// assert_eq!(vector.len(), 4);
/// assert_eq!(vector.get(0), Some(&1));
/// assert_eq!(vector.get(3), Some(&4));
/// ```
pub fn pvec_range<T, R>(range: R) -> PersistentVector<T>
where
    T: Clone + From<usize>,
    R: std::ops::RangeBounds<usize>,
{
    use std::ops::Bound;
    
    let start = match range.start_bound() {
        Bound::Included(&n) => n,
        Bound::Excluded(&n) => n + 1,
        Bound::Unbounded => 0,
    };
    
    let end = match range.end_bound() {
        Bound::Included(&n) => n + 1,
        Bound::Excluded(&n) => n,
        Bound::Unbounded => usize::MAX,
    };
    
    if start >= end {
        return PersistentVector::new();
    }
    
    // Limit to a reasonable range to avoid excessive allocation
    let capped_end = min(end, start + 1_000_000);
    
    (start..capped_end).map(T::from).collect()
}

/// Create a vector by repeating a value a specified number of times.
///
/// # Examples
///
/// ```
/// use rustica::{pvec_repeat, PersistentVector};
///
/// let vector = pvec_repeat(42, 5);
/// assert_eq!(vector.len(), 5);
/// assert_eq!(vector.get(0), Some(&42));
/// assert_eq!(vector.get(4), Some(&42));
/// ```
pub fn pvec_repeat<T: Clone>(value: T, count: usize) -> PersistentVector<T> {
    let mut vector = PersistentVector::new();
    for _ in 0..count {
        vector = vector.push_back(value.clone());
    }
    vector
}
