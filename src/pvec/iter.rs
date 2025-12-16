//! Iterators for persistent vectors.
//!
//! This module provides iterator types for [`PersistentVector`], enabling
//! idiomatic Rust iteration patterns over persistent vector elements.
//!
//! # Iterator Types
//!
//! - [`PersistentVectorIter`]: Borrows the vector and yields references (`&T`)
//! - [`PersistentVectorIntoIter`]: Consumes the vector and yields owned values (`T`)
//!
//! # Examples
//!
//! ```
//! use rustica::pvec::PersistentVector;
//!
//! let vec = PersistentVector::from_slice(&[1, 2, 3]);
//!
//! // Iterate by reference
//! for item in vec.iter() {
//!     println!("{}", item);
//! }
//!
//! // Iterate by value (consumes the vector)
//! let sum: i32 = vec.into_iter().sum();
//! assert_eq!(sum, 6);
//! ```

use super::core::PersistentVector;

/// An iterator over references to elements in a persistent vector.
///
/// This iterator is created by the [`iter`] method on [`PersistentVector`].
/// It borrows the vector and yields references to each element.
///
/// # Note
///
/// This iterator requires `T: Clone` because the underlying `get` method
/// may need to traverse the tree structure.
///
/// [`iter`]: super::core::PersistentVector::iter
///
/// # Examples
///
/// ```
/// use rustica::pvec::PersistentVector;
///
/// let vec = PersistentVector::from_slice(&[1, 2, 3]);
/// let mut iter = vec.iter();
///
/// assert_eq!(iter.next(), Some(&1));
/// assert_eq!(iter.next(), Some(&2));
/// assert_eq!(iter.next(), Some(&3));
/// assert_eq!(iter.next(), None);
/// ```
pub struct PersistentVectorIter<'a, T> {
    pub(crate) vector: &'a PersistentVector<T>,
    pub(crate) position: usize,
}

/// An iterator that yields owned elements from a persistent vector.
///
/// This iterator consumes the vector and yields owned values. Note that
/// because `PersistentVector` uses structural sharing, "consuming" the vector
/// doesn't necessarily deallocate the underlying data if other vectors share it.
///
/// # Note
///
/// This iterator requires `T: Clone` because elements are cloned from the
/// underlying storage.
///
/// This iterator is created by the [`into_iter`] method on [`PersistentVector`]
/// (provided by the [`IntoIterator`] trait).
///
/// [`into_iter`]: std::iter::IntoIterator::into_iter
///
/// # Examples
///
/// ```
/// use rustica::pvec::PersistentVector;
///
/// let vec = PersistentVector::from_slice(&[1, 2, 3]);
/// let collected: Vec<i32> = vec.into_iter().collect();
/// assert_eq!(collected, vec![1, 2, 3]);
/// ```
pub struct PersistentVectorIntoIter<T> {
    pub(crate) vector: PersistentVector<T>,
    pub(crate) position: usize,
}

impl<'a, T: Clone> Iterator for PersistentVectorIter<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        if self.position < self.vector.len() {
            let item = self.vector.get(self.position);
            self.position += 1;
            item
        } else {
            None
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let remaining = self.vector.len() - self.position;
        (remaining, Some(remaining))
    }
}

impl<'a, T: Clone> ExactSizeIterator for PersistentVectorIter<'a, T> {}

impl<T: Clone> Iterator for PersistentVectorIntoIter<T> {
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        if self.position < self.vector.len() {
            let item = self.vector.get(self.position).cloned();
            self.position += 1;
            item
        } else {
            None
        }
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        let remaining = self.vector.len() - self.position;
        (remaining, Some(remaining))
    }
}

impl<T: Clone> ExactSizeIterator for PersistentVectorIntoIter<T> {}
