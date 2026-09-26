use crate::datatypes::validated::core::{NonEmptyErrors, Validated};

pub type Iter<'a, T> = std::option::IntoIter<&'a T>;
pub type IterMut<'a, T> = std::option::IntoIter<&'a mut T>;
pub type IntoIter<T> = std::option::IntoIter<T>;

impl<T, E> IntoIterator for Validated<T, E> {
    type Item = T;
    type IntoIter = IntoIter<T>;

    fn into_iter(self) -> Self::IntoIter {
        match self {
            Validated::Valid(a) => Some(a).into_iter(),
            _ => None.into_iter(),
        }
    }
}

impl<'a, T, E> IntoIterator for &'a Validated<T, E> {
    type Item = &'a T;
    type IntoIter = Iter<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<'a, T, E> IntoIterator for &'a mut Validated<T, E> {
    type Item = &'a mut T;
    type IntoIter = IterMut<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter_mut()
    }
}

impl<T, E, C> FromIterator<Validated<T, E>> for Validated<C, E>
where
    C: FromIterator<T>,
{
    /// Collects an iterator of `Validated<T, E>` into `Validated<C, E>`.
    ///
    /// If all items are `Valid`, collects all inner values into container `C`.
    /// If any items are `Invalid`, accumulates all errors across all items in encounter order.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::validated::Validated;
    ///
    /// let items = vec![Validated::<i32, &str>::valid(1), Validated::valid(2)];
    /// let collected: Validated<Vec<i32>, &str> = items.into_iter().collect();
    /// assert_eq!(collected, Validated::valid(vec![1, 2]));
    ///
    /// let mixed = vec![
    ///     Validated::<i32, &str>::valid(1),
    ///     Validated::invalid("err1"),
    ///     Validated::invalid("err2"),
    /// ];
    /// let failed: Validated<Vec<i32>, &str> = mixed.into_iter().collect();
    /// assert_eq!(failed.error_slice(), &["err1", "err2"]);
    /// ```
    #[inline]
    fn from_iter<I: IntoIterator<Item = Validated<T, E>>>(iter: I) -> Self {
        Validated::<T, E>::collect(iter.into_iter())
    }
}

impl<T, E> Validated<T, E> {
    /// Returns an iterator over the valid value (0 or 1 item).
    #[inline]
    pub fn iter(&self) -> Iter<'_, T> {
        match self {
            Validated::Valid(a) => Some(a).into_iter(),
            _ => None.into_iter(),
        }
    }

    /// Returns a mutable iterator over the valid value (0 or 1 item).
    #[inline]
    pub fn iter_mut(&mut self) -> IterMut<'_, T> {
        match self {
            Validated::Valid(a) => Some(a).into_iter(),
            _ => None.into_iter(),
        }
    }

    /// Returns a slice view over the accumulated errors without cloning.
    ///
    /// When this `Validated` is `Valid`, an empty slice is returned.
    #[inline]
    pub const fn error_slice(&self) -> &[E] {
        match self {
            Validated::Valid(_) => &[],
            Validated::Invalid(es) => es.as_slice(),
        }
    }

    /// Returns an iterator over all errors if this is invalid, or an empty iterator if valid.
    #[inline]
    pub fn iter_errors(&self) -> std::slice::Iter<'_, E> {
        self.error_slice().iter()
    }

    /// Returns a mutable iterator over the error(s) (0 or many).
    #[inline]
    pub fn iter_errors_mut(&mut self) -> std::slice::IterMut<'_, E> {
        match self {
            Validated::Invalid(es) => es.iter_mut(),
            _ => [].iter_mut(),
        }
    }

    /// Returns a reference to the error collection if `Invalid`, otherwise `None`.
    #[inline]
    pub const fn error_payload(&self) -> Option<&NonEmptyErrors<E>> {
        match self {
            Validated::Valid(_) => None,
            Validated::Invalid(es) => Some(es),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_valid_iterators() {
        let mut v: Validated<i32, &str> = Validated::valid(42);
        assert_eq!(v.iter().next(), Some(&42));
        if let Some(item) = v.iter_mut().next() {
            *item = 43;
        }
        assert_eq!(v, Validated::valid(43));
        assert_eq!(v.into_iter().collect::<Vec<_>>(), vec![43]);
    }

    #[test]
    fn test_invalid_iterators_and_slices() {
        let mut invalid: Validated<i32, String> =
            Validated::invalid_many(["e1".to_string(), "e2".to_string()]);

        assert_eq!(invalid.error_slice(), &["e1", "e2"]);
        assert_eq!(invalid.iter_errors().count(), 2);
        assert_eq!(invalid.error_payload().map(|p| p.len()), Some(2));

        for err in invalid.iter_errors_mut() {
            err.push('!');
        }
        assert_eq!(invalid.error_slice(), &["e1!", "e2!"]);
    }

    #[test]
    fn test_const_fn_capability() {
        const fn inspect_error_slice<'a, T, E>(v: &'a Validated<T, E>) -> &'a [E] {
            v.error_slice()
        }

        const fn inspect_error_payload<'a, T, E>(
            v: &'a Validated<T, E>,
        ) -> Option<&'a NonEmptyErrors<E>> {
            v.error_payload()
        }

        let valid: Validated<i32, &'static str> = Validated::valid(42);
        assert_eq!(inspect_error_slice(&valid), &[] as &[&'static str]);
        assert!(inspect_error_payload(&valid).is_none());

        let invalid: Validated<i32, &'static str> = Validated::invalid("fail");
        assert_eq!(inspect_error_slice(&invalid), &["fail"]);
        assert!(inspect_error_payload(&invalid).is_some());
    }
}
