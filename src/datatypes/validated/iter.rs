use crate::datatypes::validated::core::Validated;

/// Iterator over a Validated value (0 or 1 item)
pub struct Iter<'a, A> {
    inner: Option<&'a A>,
}

impl<'a, A> Iterator for Iter<'a, A> {
    type Item = &'a A;

    fn next(&mut self) -> Option<Self::Item> {
        self.inner.take()
    }
}

/// Mutable iterator over a Validated value (0 or 1 item)
pub struct IterMut<'a, A> {
    inner: Option<&'a mut A>,
}

impl<'a, A> Iterator for IterMut<'a, A> {
    type Item = &'a mut A;

    fn next(&mut self) -> Option<Self::Item> {
        self.inner.take()
    }
}

/// Iterator over errors in a Validated
pub enum ErrorsIter<'a, E> {
    Empty,
    Multi(smallvec::alloc::slice::Iter<'a, E>),
}

impl<'a, E> Iterator for ErrorsIter<'a, E> {
    type Item = &'a E;

    fn next(&mut self) -> Option<Self::Item> {
        match self {
            ErrorsIter::Empty => None,
            ErrorsIter::Multi(it) => it.next(),
        }
    }
}

/// Mutable iterator over errors in a Validated
pub enum ErrorsIterMut<'a, E> {
    Empty,
    Multi(smallvec::alloc::slice::IterMut<'a, E>),
}

impl<'a, E> Iterator for ErrorsIterMut<'a, E> {
    type Item = &'a mut E;

    fn next(&mut self) -> Option<Self::Item> {
        match self {
            ErrorsIterMut::Empty => None,
            ErrorsIterMut::Multi(it) => it.next(),
        }
    }
}

impl<E, A> IntoIterator for Validated<E, A> {
    type Item = A;
    type IntoIter = IntoIter<A>;

    fn into_iter(self) -> Self::IntoIter {
        match self {
            Validated::Valid(a) => IntoIter { inner: Some(a) },
            _ => IntoIter { inner: None },
        }
    }
}

pub struct IntoIter<A> {
    inner: Option<A>,
}

impl<A> Iterator for IntoIter<A> {
    type Item = A;

    fn next(&mut self) -> Option<Self::Item> {
        self.inner.take()
    }
}

impl<'a, E: Clone, A: Clone> IntoIterator for &'a Validated<E, A> {
    type Item = &'a A;
    type IntoIter = Iter<'a, A>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<'a, E: Clone, A: Clone> IntoIterator for &'a mut Validated<E, A> {
    type Item = &'a mut A;
    type IntoIter = IterMut<'a, A>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter_mut()
    }
}

impl<E: Clone, A: Clone> Validated<E, A> {
    /// Returns an iterator over the valid value (0 or 1 item).
    pub fn iter(&self) -> Iter<'_, A> {
        match self {
            Validated::Valid(a) => Iter { inner: Some(a) },
            _ => Iter { inner: None },
        }
    }

    /// Returns a mutable iterator over the valid value (0 or 1 item).
    pub fn iter_mut(&mut self) -> IterMut<'_, A> {
        match self {
            Validated::Valid(a) => IterMut { inner: Some(a) },
            _ => IterMut { inner: None },
        }
    }

    /// Returns a mutable iterator over the error(s) (0 or many).
    pub fn iter_errors_mut(&mut self) -> ErrorsIterMut<'_, E> {
        match self {
            Validated::Invalid(es) => ErrorsIterMut::Multi(es.iter_mut()),
            _ => ErrorsIterMut::Empty,
        }
    }
}
