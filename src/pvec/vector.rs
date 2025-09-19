//! Persistent Vector Implementation
//!
//! This module defines the `PersistentVector` type, which provides a high-level
//! interface for the persistent vector data structure. It is implemented using
//! a Relaxed Radix Balanced (RRB) tree for efficient operations.
//!
//! # API Philosophy
//!
//! - **Simple by default:** Most users do not need to care about cache policies.
//!   Use `PersistentVector::new()` or the `pvec![]` macro for idiomatic usage.
//! - **Advanced control:** For performance tuning, use `with_cache_policy`,
//!   `from_slice_with_cache_policy`, or pass a custom policy to advanced methods.
//! - **Extensible:** Implement the `CachePolicy` trait to define custom caching.
//!
//! # Examples
//!
//! Basic usage (internal/default cache policy):
//! ```
//! use rustica::pvec::PersistentVector;
//! let vec = PersistentVector::new().push_back(1).push_back(2);
//! ```
//!
//! Advanced usage (explicit cache policy):
//! ```
//! use rustica::pvec::{PersistentVector, AlwaysCache};
//! let vec: PersistentVector<i32> = PersistentVector::with_cache_policy(Box::new(AlwaysCache));
//! ```
//!
//! Custom policy:
//! ```
//! use rustica::pvec::{PersistentVector, CachePolicy, BoxedCachePolicy};
//! struct MyPolicy;
//! impl CachePolicy for MyPolicy {
//!     fn should_cache(&self, _index: usize) -> bool {
//!         // Cache indices divisible by 3
//!         _index % 3 == 0
//!     }
//!     
//!     fn clone_box(&self) -> BoxedCachePolicy {
//!         Box::new(MyPolicy)
//!     }
//! }
//! let vec: PersistentVector<i32> = PersistentVector::with_cache_policy(Box::new(MyPolicy));
//! ```
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
//! // Create a new empty vector
//! let vec = PersistentVector::<i32>::new();
//! assert_eq!(vec.len(), 0);
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
//!
//! # Chunk Size: API, Options, and Usage
//!
//! The `chunk_size` parameter directly affects the performance and memory efficiency of a `PersistentVector`.
//!
//! ## Key APIs
//!
//! - `PersistentVector::with_chunk_size(size)`: Create an empty vector with a custom chunk size.
//! - `PersistentVector::from_slice_with_chunk_size(slice, size)`: Create a vector from a slice with a specific chunk size.
//! - `vec.chunk_size()`: Query the current chunk size of a vector.
//! - `concat`, `extend`: When merging vectors, the resulting vector always inherits the chunk size of the left operand (`self`).
//! - `chunks()`: Iterate over the vector in blocks matching its chunk size.
//!
//! The default chunk size is 32, but you can tune this for large data or specific access patterns.
//!
//! ## Example Usage
//!
//! ```rust
//! use rustica::pvec::PersistentVector;
//!
//! // Create a vector with chunk_size 16
//! let vec: PersistentVector<i32> = PersistentVector::with_chunk_size(16);
//! assert_eq!(vec.chunk_size(), 16);
//!
//! // Create from slice with chunk_size 64
//! let from_slice: PersistentVector<i32> = PersistentVector::from_slice_with_chunk_size(&[1,2,3,4], 64);
//! assert_eq!(from_slice.chunk_size(), 64);
//!
//! // Merging preserves the left's chunk_size
//! let a = PersistentVector::with_chunk_size(8).extend([1,2]);
//! let b = PersistentVector::with_chunk_size(32).extend([3,4]);
//! let merged = a.concat(&b);
//! assert_eq!(merged.chunk_size(), 8); // inherits from `a`
//!
//! // Chunked iteration
//! let v = PersistentVector::from_slice_with_chunk_size(&(0..10).collect::<Vec<_>>(), 4);
//! let chunks: Vec<Vec<_>> = v.chunks().collect();
//! assert_eq!(chunks, vec![vec![0,1,2,3], vec![4,5,6,7], vec![8,9]]);
//! ```
//!
//! ## Performance Notes
//!
//! The chunk size impacts cache locality, memory usage, and potential for parallelism. For best performance, experiment with different chunk sizes based on your data and workload.
//!
//! # Chunk Size Options
//!
//! The `PersistentVector` supports configurable chunk sizes for advanced tuning.
//!
//! - Use [`PersistentVector::with_chunk_size`] to create a vector with a custom chunk size.
//! - Use [`PersistentVector::from_slice_with_chunk_size`] to construct from a slice with a specific chunk size.
//! - Most operations (push, update, concat, extend, etc.) preserve the current chunk size.
//! - When merging vectors with different chunk sizes, the result inherits the chunk size of the left operand (`self`).
//!
//! ## Example: Custom Chunk Size
//!
//! ```rust
//! use rustica::pvec::PersistentVector;
//! let vec: PersistentVector<i32> = PersistentVector::with_chunk_size(8);
//! let vec = vec.push_back(1).push_back(2);
//! assert_eq!(vec.chunk_size(), 8);
//! ```
//!
//! ## Example: Merging with Different Chunk Sizes
//!
//! ```rust
//! use rustica::pvec::PersistentVector;
//! let a: PersistentVector<i32> = PersistentVector::with_chunk_size(4).extend([1, 2]);
//! let b: PersistentVector<i32> = PersistentVector::with_chunk_size(8).extend([3, 4]);
//! let ab = a.concat(&b);
//! assert_eq!(ab.chunk_size(), 4); // Inherits from `a`
//! ```
//!
//! ## Notes
//!
//! - Smaller chunk sizes use less memory per chunk but may increase tree height and slow down some operations.
//! - Larger chunk sizes improve iteration and bulk operations, but may waste memory for small vectors.
//! - The default chunk size is 32 unless otherwise specified.
//!
//! See each method's documentation for more details and examples.

//! # PersistentVector: Chunk Size Policy
//!
//! The `chunk_size` parameter controls how many elements are grouped together in each chunk of the vector's internal tree.
//!
//! - **Default:** The default chunk size is 32 if not otherwise specified.
//! - **Custom:** You can freely specify any chunk size (e.g., 4, 16, 64, 128, etc.) when constructing a vector. There is no upper or lower clamp enforced by the implementation.
//! - **Performance:** Tuning chunk size can impact cache locality, memory usage, and iteration performance. For best results, experiment with different chunk sizes for your workload.
//!
//! ## Key APIs
//!
//! - `PersistentVector::with_chunk_size(size)`: Create an empty vector with a custom chunk size.
//! - `PersistentVector::from_slice_with_chunk_size(slice, size)`: Create a vector from a slice with a specific chunk size.
//! - `vec.chunk_size()`: Query the current chunk size of a vector.
//! - `concat`, `extend`: When merging vectors, the resulting vector always inherits the chunk size of the left operand (`self`).
//! - `chunks()`: Iterate over the vector in blocks matching its chunk size.
//!
//! ## Example Usage
//!
//! ```rust
//! use rustica::pvec::PersistentVector;
//!
//! // Create with custom chunk size 16
//! let vec: PersistentVector<i32> = PersistentVector::with_chunk_size(16);
//! assert!(vec.is_empty());
//! assert_eq!(vec.chunk_size(), 16);
//!
//! // From slice with chunk size 64
//! let from_slice = PersistentVector::from_slice_with_chunk_size(&[1,2,3,4], 64);
//! assert_eq!(from_slice.chunk_size(), 64);
//!
//! // Merging: left's chunk_size is preserved
//! let a: PersistentVector<i32> = PersistentVector::with_chunk_size(8).extend([1,2]);
//! let b: PersistentVector<i32> = PersistentVector::with_chunk_size(32).extend([3,4]);
//! let merged = a.concat(&b);
//! assert_eq!(merged.chunk_size(), 8); // inherits from `a`
//!
//! // Chunked iteration
//! let v = PersistentVector::from_slice_with_chunk_size(&(0..10).collect::<Vec<_>>(), 4);
//! let chunks: Vec<Vec<_>> = v.chunks().collect();
//! assert_eq!(chunks, vec![vec![0,1,2,3], vec![4,5,6,7], vec![8,9]]);
//! ```
//!
//! ## Notes
//!
//! - Smaller chunk sizes use less memory per chunk but may increase tree height and slow down some operations.
//! - Larger chunk sizes improve iteration and bulk operations, but may waste memory for small vectors.
//! - There is **no hard-coded limit**: you may specify any chunk size that makes sense for your use case.
//! - For best performance, experiment with different chunk sizes based on your data and workload.

use std::fmt::{self, Debug};
use std::iter::FromIterator;
use std::marker::PhantomData;
use std::ops::Index;
use std::sync::Arc;

use super::iterator::{ChunksIter, Iter, SortedIter};
use super::tree::Tree;
use crate::datatypes::lens::Lens;
use crate::pvec::memory::BoxedCachePolicy;
#[cfg(feature = "serde")]
use serde::de::{SeqAccess, Visitor};
#[cfg(feature = "serde")]
use serde::ser::SerializeSeq;

#[cfg(feature = "serde")]
use serde::{Deserialize, Deserializer, Serialize, Serializer};

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
/// assert_eq!(vec2.get(0), Some(&1));
/// ```
#[derive(Clone, PartialEq, Eq)]
pub struct PersistentVector<T> {
    /// The underlying implementation
    inner: VectorImpl<T>,
    /// The intended chunk size for this vector
    chunk_size: usize,
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
        tree: Box<Tree<T>>,
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
/// The implementation uses `MaybeUninit<T>` for each slot to allow for efficient
/// initialization and avoid the overhead of `Option<T>`.
use std::mem::MaybeUninit;
use std::ptr;

#[derive(Debug)]
pub struct SmallVec<T> {
    elements: [MaybeUninit<T>; SMALL_VECTOR_SIZE],
    len: usize,
}

impl<T> SmallVec<T> {
    /// Creates a new, empty SmallVec
    pub fn new() -> Self {
        SmallVec {
            elements: unsafe { MaybeUninit::uninit().assume_init() },
            len: 0,
        }
    }

    /// Returns a reference to the element at the given index, or None if out of bounds
    pub fn get(&self, index: usize) -> Option<&T> {
        if index < self.len {
            // SAFETY: index < len means the element is initialized
            Some(unsafe { &*self.elements[index].as_ptr() })
        } else {
            None
        }
    }

    /// Returns the number of elements in the vector
    #[inline(always)]
    pub fn len(&self) -> usize {
        self.len
    }

    /// Returns true if the vector is empty
    #[inline(always)]
    pub fn is_empty(&self) -> bool {
        self.len == 0
    }
}

impl<T> Default for SmallVec<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T> Drop for SmallVec<T> {
    fn drop(&mut self) {
        for i in 0..self.len {
            unsafe {
                ptr::drop_in_place(self.elements[i].as_mut_ptr());
            }
        }
    }
}

impl<T: Clone> Clone for SmallVec<T> {
    fn clone(&self) -> Self {
        let mut new = Self::new();
        for i in 0..self.len {
            unsafe {
                let ptr = self.elements[i].as_ptr();
                ptr::write(new.elements[i].as_mut_ptr(), (*ptr).clone());
            }
        }
        new.len = self.len;
        new
    }
}

impl<T: PartialEq> PartialEq for SmallVec<T> {
    fn eq(&self, other: &Self) -> bool {
        if self.len != other.len {
            return false;
        }
        for i in 0..self.len {
            unsafe {
                if *self.elements[i].as_ptr() != *other.elements[i].as_ptr() {
                    return false;
                }
            }
        }
        true
    }
}

impl<T: Eq> Eq for SmallVec<T> {}

impl<T: Clone> SmallVec<T> {
    /// Returns a new SmallVec with the given element appended
    pub fn push_back(&self, value: T) -> Self {
        assert!(self.len < SMALL_VECTOR_SIZE, "SmallVec overflow");
        let mut new = self.clone();
        unsafe {
            ptr::write(new.elements[self.len].as_mut_ptr(), value);
        }
        new.len += 1;
        new
    }

    /// Returns a new SmallVec with the element at the given index updated
    /// Uses efficient copying when possible and avoids unnecessary clones
    pub fn update(&self, index: usize, value: T) -> Self {
        if index >= self.len {
            // Out-of-bounds update preserves immutability semantics
            return self.clone();
        }
        let mut new = self.clone();
        unsafe {
            // Drop the existing value before overwriting
            ptr::drop_in_place(new.elements[index].as_mut_ptr());
            ptr::write(new.elements[index].as_mut_ptr(), value);
        }
        new
    }

    /// Create a new SmallVec with updated length using efficient copying
    #[inline(always)]
    pub fn with_updated_len(&self, new_len: usize) -> Self {
        let mut new = self.clone();
        new.len = new_len;
        new
    }

    /// Convert to a standard Vec
    pub fn to_vec(&self) -> std::vec::Vec<T> {
        let mut v = Vec::with_capacity(self.len);
        for i in 0..self.len {
            // SAFETY: 0 <= i < len, so initialized
            unsafe {
                v.push((*self.elements[i].as_ptr()).clone());
            }
        }
        v
    }

    /// Batch copy from slice for efficient initialization
    pub fn from_slice_batch(slice: &[T]) -> Self {
        assert!(
            slice.len() <= SMALL_VECTOR_SIZE,
            "Slice too large for SmallVec"
        );
        let mut new = Self::new();
        for (i, item) in slice.iter().enumerate() {
            unsafe {
                ptr::write(new.elements[i].as_mut_ptr(), item.clone());
            }
        }
        new.len = slice.len();
        new
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
                elements: SmallVec::from_slice_batch(slice),
            }
        } else {
            VectorImpl::Tree {
                tree: Box::new(Tree::from_slice(slice)),
            }
        }
    }

    /// Returns a reference to the element at the specified index, or None if the index is out of bounds.
    #[inline(always)]
    #[must_use]
    pub fn get(&self, index: usize) -> Option<&T> {
        match self {
            VectorImpl::Small { elements } => elements.get(index),
            VectorImpl::Tree { tree } => tree.as_ref().get(index),
        }
    }

    /// Returns the number of elements in the vector.
    #[inline(always)]
    #[must_use]
    pub fn len(&self) -> usize {
        match self {
            VectorImpl::Small { elements } => elements.len(),
            VectorImpl::Tree { tree } => tree.as_ref().len(),
        }
    }
}

impl<T: Clone> VectorImpl<T> {
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
                    tree: Box::new(Tree::from_slice(&v)),
                }
            },
            VectorImpl::Tree { tree } => VectorImpl::Tree {
                tree: Box::new(tree.as_ref().push_back(value)),
            },
        }
    }

    pub fn pop_back(&self) -> Option<(Self, T)> {
        match self {
            VectorImpl::Small { elements } if !elements.is_empty() => {
                let mut v = elements.clone();
                let val = unsafe { v.elements[v.len - 1].as_ptr().read() };
                v.len -= 1;
                Some((VectorImpl::Small { elements: v }, val))
            },
            VectorImpl::Tree { tree } => tree.as_ref().pop_back().map(|(new_tree, val)| {
                (
                    VectorImpl::Tree {
                        tree: Box::new(new_tree),
                    },
                    val,
                )
            }),
            _ => None,
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
                tree: Box::new(tree.as_ref().update(index, value)),
            },
        }
    }

    /// Convert to a standard Vec
    #[inline(always)]
    #[must_use]
    pub fn to_vec(&self) -> std::vec::Vec<T> {
        match self {
            VectorImpl::Small { elements } => elements.to_vec(),
            VectorImpl::Tree { tree } => tree.as_ref().to_vec(),
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
            VectorImpl::Tree { tree } => tree.as_ref().fmt(f),
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
            chunk_size: crate::pvec::memory::DEFAULT_CHUNK_SIZE,
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
            chunk_size: crate::pvec::memory::DEFAULT_CHUNK_SIZE,
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
            chunk_size: crate::pvec::memory::DEFAULT_CHUNK_SIZE,
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
        self.inner.len()
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

    pub fn update(&self, index: usize, value: T) -> Self {
        Self {
            inner: self.inner.update(index, value),
            chunk_size: self.chunk_size,
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
            chunk_size: self.chunk_size,
        }
    }

    /// Returns a new vector with the given element appended, using the cache policy if present.
    pub fn push_back_with_cache_policy(&self, value: T) -> Self {
        match &self.inner {
            VectorImpl::Small { elements } if elements.len() < SMALL_VECTOR_SIZE => Self {
                inner: VectorImpl::Small {
                    elements: elements.push_back(value),
                },
                chunk_size: self.chunk_size,
            },
            VectorImpl::Small { elements } => {
                let mut v: Vec<T> = elements.to_vec();
                v.push(value);
                Self {
                    inner: VectorImpl::Tree {
                        tree: Box::new(crate::pvec::tree::Tree::from_slice(&v)),
                    },
                    chunk_size: self.chunk_size,
                }
            },
            VectorImpl::Tree { tree } => Self {
                inner: VectorImpl::Tree {
                    tree: Box::new(tree.as_ref().push_back(value)),
                },
                chunk_size: self.chunk_size,
            },
        }
    }

    /// Returns a new vector with the element at the given index updated, using the cache policy if present.
    pub fn update_with_cache_policy(&self, index: usize, value: T) -> Self {
        match &self.inner {
            VectorImpl::Small { elements } => Self {
                inner: VectorImpl::Small {
                    elements: elements.update(index, value),
                },
                chunk_size: self.chunk_size,
            },
            VectorImpl::Tree { tree } => Self {
                inner: VectorImpl::Tree {
                    tree: Box::new(tree.as_ref().update(index, value)),
                },
                chunk_size: self.chunk_size,
            },
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
    /// # Chunk Size Policy
    ///
    /// The resulting vector's `chunk_size` is always inherited from `self`.
    /// If you need to control the chunk size of the result, use `with_chunk_size` or `from_slice_with_chunk_size`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::pvec::PersistentVector;
    /// let vec: PersistentVector<i32> = PersistentVector::with_chunk_size(4).extend([1, 2, 3]);
    /// let extended = vec.extend([4, 5, 6]);
    /// assert_eq!(extended.to_vec(), vec![1, 2, 3, 4, 5, 6]);
    /// assert_eq!(extended.chunk_size(), 4);
    /// ```
    #[inline(always)]
    #[must_use]
    pub fn extend(&self, values: impl IntoIterator<Item = T>) -> Self {
        let mut v = self.to_vec();
        v.extend(values);
        PersistentVector {
            inner: VectorImpl::from_slice(&v),
            chunk_size: self.chunk_size,
        }
    }

    /// Removes the last element from the vector and returns it, along with the updated vector.
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
        self.inner.pop_back().map(|(inner, val)| {
            (
                Self {
                    inner,
                    chunk_size: self.chunk_size,
                },
                val,
            )
        })
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
        (start..end)
            .filter_map(|i| self.lens_at(i).get(self))
            .fold(Self::new(), |acc, val| acc.push_back(val))
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
        let left = self.slice(0, at);
        let right = self.slice(at, self.len());
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
    ///
    /// let vec = PersistentVector::from_slice(&[1, 2, 3]);
    /// assert_eq!(vec.last(), Some(&3));
    ///
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
    /// let vec = PersistentVector::from_slice(&[1, 2, 3, 4, 5]);
    /// assert!(vec.contains(&2));
    /// assert!(!vec.contains(&6));
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
        let (left, right) = self.split_at(index);
        left.push_back(value).concat(&right)
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
        let (left, right) = self.split_at(index);
        let removed = right.get(0).cloned().expect("index out of bounds");
        (left.concat(&right.slice(1, right.len())), removed)
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
        match new_len.cmp(&old_len) {
            std::cmp::Ordering::Less => result = result.truncate(new_len),
            std::cmp::Ordering::Greater => {
                for _ in old_len..new_len {
                    result = result.push_back(value.clone());
                }
            },
            _ => {},
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
    /// # Chunk Size Policy
    ///
    /// The resulting vector's `chunk_size` is always inherited from `self`, regardless of `other`'s chunk size.
    /// If you need to control the chunk size of the result, use `with_chunk_size` or `from_slice_with_chunk_size`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::pvec::PersistentVector;
    /// let vec1: PersistentVector<i32> = PersistentVector::with_chunk_size(4).extend([1, 2, 3]);
    /// let vec2: PersistentVector<i32> = PersistentVector::with_chunk_size(8).extend([4, 5, 6]);
    /// let combined = vec1.concat(&vec2);
    /// assert_eq!(combined.to_vec(), vec![1, 2, 3, 4, 5, 6]);
    /// assert_eq!(combined.chunk_size(), 4); // Inherits from vec1
    /// ```
    pub fn concat(&self, other: &Self) -> Self {
        let mut v = self.to_vec();
        v.extend(other.iter().cloned());
        PersistentVector {
            inner: VectorImpl::from_slice(&v),
            chunk_size: self.chunk_size,
        }
    }

    /// Get a reference to the element at the specified index, using the index cache for fast access if possible.
    ///
    /// This method provides a mutable access path that leverages the internal cache for repeated access patterns.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::pvec::PersistentVector;
    /// let mut vec = PersistentVector::from_slice(&[10, 20, 30, 40]);
    /// let val = vec.get_with_cache(2);
    /// assert_eq!(val, Some(&30));
    /// ```
    #[inline(always)]
    #[must_use]
    pub fn get_with_cache(&mut self, index: usize) -> Option<&T> {
        match &mut self.inner {
            VectorImpl::Small { elements } => elements.get(index),
            VectorImpl::Tree { tree } => tree.as_mut().get_with_cache(index),
        }
    }

    /// Returns the cache hit/miss statistics as a tuple (hits, misses).
    ///
    /// This method allows users to profile the effectiveness of the cache when using `get_with_cache`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::pvec::PersistentVector;
    /// // Use 33 elements to ensure the Tree variant is used (CHUNK_SIZE is 32)
    /// let mut vec = PersistentVector::from_slice(&(0..33).collect::<Vec<_>>());
    /// vec.get_with_cache(0);
    /// vec.get_with_cache(1);
    /// let (hits, misses) = vec.cache_stats();
    /// assert_eq!((hits, misses), (0, 2));
    /// ```
    #[inline(always)]
    #[must_use]
    pub fn cache_stats(&self) -> (usize, usize) {
        match &self.inner {
            VectorImpl::Small { .. } => (0, 0),
            VectorImpl::Tree { tree } => tree.as_ref().cache_stats(),
        }
    }

    /// Returns the chunk size used for chunked storage.
    ///
    /// For vectors created with a custom chunk size (via `with_chunk_size` or `from_slice_with_chunk_size`),
    /// this returns the configured value. For small vectors, returns the default chunk size.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::pvec::PersistentVector;
    /// let vec: PersistentVector<i32> = PersistentVector::with_chunk_size(8);
    /// assert_eq!(vec.chunk_size(), 8);
    /// ```
    #[inline(always)]
    #[must_use]
    pub fn chunk_size(&self) -> usize {
        self.chunk_size
    }

    /// Maps elements in parallel using Rayon.
    ///
    /// Uses parallel chunks to improve performance for large vectors.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::PersistentVector;
    /// use rayon::prelude::*;
    ///
    /// let vec = PersistentVector::from_slice(&(0..1000).collect::<Vec<_>>());
    /// let mapped = vec.par_map(|x| x + 1);
    /// assert_eq!(mapped.get(0), Some(&1));
    /// ```
    #[cfg(feature = "async")]
    pub fn par_map<F, U>(&self, f: F) -> PersistentVector<U>
    where
        F: Fn(&T) -> U + Send + Sync,
        U: Clone + Send,
        T: Sync,
    {
        use rayon::prelude::*;

        let chunked: Vec<Vec<U>> = self
            .chunks()
            .collect::<Vec<_>>()
            .par_iter()
            .map(|chunk| chunk.iter().map(&f).collect())
            .collect();

        let mut result = PersistentVector::with_chunk_size(self.chunk_size());
        for chunk in chunked {
            for item in chunk {
                result = result.push_back(item);
            }
        }
        result
    }

    /// Creates a new persistent vector with a custom cache policy.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::pvec::{PersistentVector, NeverCache, EvenIndexCache};
    /// let vec = PersistentVector::<i32>::with_cache_policy(Box::new(NeverCache));
    /// assert_eq!(vec.len(), 0);
    /// let vec2 = PersistentVector::from_slice_with_cache_policy(&[1,2,3], Box::new(EvenIndexCache));
    /// assert_eq!(vec2.len(), 3);
    /// ```
    pub fn with_cache_policy(policy: BoxedCachePolicy) -> Self {
        Self {
            inner: VectorImpl::Tree {
                tree: Box::new(crate::pvec::tree::Tree::new().with_cache_policy(policy)),
            },
            chunk_size: crate::pvec::memory::DEFAULT_CHUNK_SIZE,
        }
    }

    /// Creates a new persistent vector from a slice with a custom cache policy.
    pub fn from_slice_with_cache_policy(slice: &[T], policy: BoxedCachePolicy) -> Self {
        if slice.len() <= SMALL_VECTOR_SIZE {
            let mut v = SmallVec::new();
            for x in slice {
                v = v.push_back(x.clone());
            }
            Self {
                inner: VectorImpl::Small { elements: v },
                chunk_size: crate::pvec::memory::DEFAULT_CHUNK_SIZE,
            }
        } else {
            Self {
                inner: VectorImpl::Tree {
                    tree: Box::new(
                        crate::pvec::tree::Tree::from_slice(slice).with_cache_policy(policy),
                    ),
                },
                chunk_size: crate::pvec::memory::DEFAULT_CHUNK_SIZE,
            }
        }
    }

    /// Creates a new, empty persistent vector with a custom chunk size.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::PersistentVector;
    /// let vec: PersistentVector<i32> = PersistentVector::with_chunk_size(16);
    /// assert!(vec.is_empty());
    /// assert_eq!(vec.len(), 0);
    /// ```
    pub fn with_chunk_size(chunk_size: usize) -> Self {
        Self {
            inner: VectorImpl::Tree {
                tree: Box::new(crate::pvec::tree::Tree::new_with_chunk_size(chunk_size)),
            },
            chunk_size,
        }
    }

    /// Creates a new persistent vector from a slice with a custom chunk size.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::pvec::PersistentVector;
    /// let vec = PersistentVector::from_slice_with_chunk_size(&[1, 2, 3], 16);
    /// assert_eq!(vec.len(), 3);
    /// assert_eq!(vec.get(2), Some(&3));
    /// ```
    pub fn from_slice_with_chunk_size(slice: &[T], chunk_size: usize) -> Self {
        if slice.len() <= SMALL_VECTOR_SIZE {
            let mut v = SmallVec::new();
            for x in slice {
                v = v.push_back(x.clone());
            }
            Self {
                inner: VectorImpl::Small { elements: v },
                chunk_size,
            }
        } else {
            Self {
                inner: VectorImpl::Tree {
                    tree: Box::new(crate::pvec::tree::Tree::from_slice_with_chunk_size(
                        slice, chunk_size,
                    )),
                },
                chunk_size,
            }
        }
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

type LensGetFn<T> = Box<dyn Fn(&PersistentVector<T>) -> Option<T>>;
type LensSetFn<T> = Box<dyn Fn(PersistentVector<T>, Option<T>) -> PersistentVector<T>>;

impl<T: Clone> PersistentVector<T> {
    /// Returns a lens focusing on the element at the given index.
    #[inline]
    pub fn lens_at(
        &self, index: usize,
    ) -> Lens<PersistentVector<T>, Option<T>, LensGetFn<T>, LensSetFn<T>> {
        let get: LensGetFn<T> = Box::new(move |vec: &PersistentVector<T>| vec.get(index).cloned());
        let set: LensSetFn<T> = Box::new(move |mut vec: PersistentVector<T>, opt: Option<T>| {
            if let Some(v) = opt {
                vec.inner = vec.inner.update(index, v);
            }
            vec
        });
        Lens::new(get, set)
    }
}

#[cfg(feature = "serde")]
impl<T: Serialize + Clone> Serialize for PersistentVector<T> {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: Serializer,
    {
        let mut seq = serializer.serialize_seq(Some(self.len()))?;
        for element in self.iter() {
            seq.serialize_element(element)?;
        }
        seq.end()
    }
}

struct PersistentVectorVisitor<T>(PhantomData<T>);

#[cfg(feature = "serde")]
impl<'de, T: Deserialize<'de> + Clone> Visitor<'de> for PersistentVectorVisitor<T> {
    type Value = PersistentVector<T>;

    fn expecting(&self, formatter: &mut fmt::Formatter) -> fmt::Result {
        formatter.write_str("a sequence")
    }

    fn visit_seq<A>(self, mut seq: A) -> Result<Self::Value, A::Error>
    where
        A: SeqAccess<'de>,
    {
        let mut pvec = PersistentVector::new();
        while let Some(value) = seq.next_element()? {
            pvec = pvec.push_back(value);
        }
        Ok(pvec)
    }
}

#[cfg(feature = "serde")]
impl<'de, T: Deserialize<'de> + Clone> Deserialize<'de> for PersistentVector<T> {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        deserializer.deserialize_seq(PersistentVectorVisitor(PhantomData))
    }
}
