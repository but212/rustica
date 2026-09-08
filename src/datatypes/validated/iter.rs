use crate::datatypes::validated::core::{NonEmptyErrors, Validated};

pub type Iter<'a, A> = std::option::IntoIter<&'a A>;
pub type IterMut<'a, A> = std::option::IntoIter<&'a mut A>;
pub type IntoIter<A> = std::option::IntoIter<A>;

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
    #[inline]
    pub fn iter(&self) -> Iter<'_, A> {
        match self {
            Validated::Valid(a) => Some(a).into_iter(),
            _ => None.into_iter(),
        }
    }

    /// Returns a mutable iterator over the valid value (0 or 1 item).
    #[inline]
    pub fn iter_mut(&mut self) -> IterMut<'_, A> {
        match self {
            Validated::Valid(a) => Some(a).into_iter(),
            _ => None.into_iter(),
        }
    }

    /// Returns a slice view over the accumulated errors without cloning.
    ///
    /// When this `Validated` is `Valid`, an empty slice is returned.
    #[inline]
    pub fn error_slice(&self) -> &[E] {
        match self {
            Validated::Valid(_) => &[],
            Validated::Invalid(es) => es.as_slice(),
        }
    }

    /// Returns an iterator over all errors if this is invalid, or an empty iterator if valid.
    #[inline]
    pub fn iter_errors(&self) -> ErrorsIter<'_, E> {
        match self {
            Validated::Invalid(es) => ErrorsIter::Multi(es.iter()),
            _ => ErrorsIter::Empty,
        }
    }

    /// Returns a mutable iterator over the error(s) (0 or many).
    #[inline]
    pub fn iter_errors_mut(&mut self) -> ErrorsIterMut<'_, E> {
        match self {
            Validated::Invalid(es) => ErrorsIterMut::Multi(es.iter_mut()),
            _ => ErrorsIterMut::Empty,
        }
    }

    /// Returns a reference to the error collection if `Invalid`, otherwise `None`.
    #[inline]
    pub fn error_payload(&self) -> Option<&NonEmptyErrors<E>> {
        match self {
            Validated::Valid(_) => None,
            Validated::Invalid(es) => Some(es),
        }
    }

    /// Returns all errors if this is invalid, or an empty collection if valid.
    #[deprecated(since = "0.16.0", note = "Use `error_slice` or `iter_errors` instead.")]
    #[inline]
    pub fn errors(&self) -> Vec<E>
    where
        E: Clone,
    {
        self.iter_errors().cloned().collect()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_valid_iterators() {
        let mut v: Validated<&str, i32> = Validated::valid(42);
        assert_eq!(v.iter().next(), Some(&42));
        if let Some(item) = v.iter_mut().next() {
            *item = 43;
        }
        assert_eq!(v, Validated::valid(43));
        assert_eq!(v.into_iter().collect::<Vec<_>>(), vec![43]);
    }

    #[test]
    fn test_invalid_iterators_and_slices() {
        let mut invalid: Validated<String, i32> =
            Validated::invalid_many(["e1".to_string(), "e2".to_string()]);

        assert_eq!(invalid.error_slice(), &["e1", "e2"]);
        assert_eq!(invalid.iter_errors().count(), 2);
        assert_eq!(invalid.error_payload().map(|p| p.len()), Some(2));

        for err in invalid.iter_errors_mut() {
            err.push('!');
        }
        assert_eq!(invalid.error_slice(), &["e1!", "e2!"]);

        #[allow(deprecated)]
        {
            assert_eq!(invalid.errors(), vec!["e1!".to_string(), "e2!".to_string()]);
        }
    }
}
