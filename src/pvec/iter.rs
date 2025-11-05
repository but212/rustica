//! Iterators for persistent vectors.

use super::core::PersistentVector;

/// An iterator over references to elements in a persistent vector.
///
/// This iterator is created by the [`iter`] method on [`PersistentVector`].
///
/// [`iter`]: super::core::PersistentVector::iter
pub struct PersistentVectorIter<'a, T> {
    pub(crate) vector: &'a PersistentVector<T>,
    pub(crate) position: usize,
}

/// An iterator that moves elements out of a persistent vector.
///
/// This iterator is created by the [`into_iter`] method on [`PersistentVector`]
/// (provided by the [`IntoIterator`] trait).
///
/// [`into_iter`]: std::iter::IntoIterator::into_iter
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
