use super::core::PersistentVector;

pub struct PersistentVectorIter<'a, T> {
    pub(crate) vector: &'a PersistentVector<T>,
    pub(crate) position: usize,
}

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
