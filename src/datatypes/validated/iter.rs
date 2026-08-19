use crate::datatypes::validated::core::Validated;

pub type Iter<'a, A> = std::option::IntoIter<&'a A>;
pub type IterMut<'a, A> = std::option::IntoIter<&'a mut A>;

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
            Validated::Valid(a) => Some(a).into_iter(),
            _ => None.into_iter(),
        }
    }
}
pub type IntoIter<A> = std::option::IntoIter<A>;

impl<'a, E, A> IntoIterator for &'a Validated<E, A> {
    type Item = &'a A;
    type IntoIter = Iter<'a, A>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<'a, E, A> IntoIterator for &'a mut Validated<E, A> {
    type Item = &'a mut A;
    type IntoIter = IterMut<'a, A>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter_mut()
    }
}

impl<E, A> Validated<E, A> {
    /// Returns an iterator over the valid value (0 or 1 item).
    pub fn iter(&self) -> Iter<'_, A> {
        match self {
            Validated::Valid(a) => Some(a).into_iter(),
            _ => None.into_iter(),
        }
    }

    /// Returns a mutable iterator over the valid value (0 or 1 item).
    pub fn iter_mut(&mut self) -> IterMut<'_, A> {
        match self {
            Validated::Valid(a) => Some(a).into_iter(),
            _ => None.into_iter(),
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
