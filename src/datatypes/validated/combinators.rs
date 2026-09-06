use super::core::ErrorAccumulator;
use crate::datatypes::validated::Validated;

impl<E, A> Validated<E, A> {
    /// Maps a function over the error values if `Invalid`, or returns the `Valid` value.
    ///
    /// If this `Validated` is `Invalid`, applies the function `f` to transform each error.
    /// If `Valid`, the original valid value `A` is returned in a new `Validated::Valid`.
    ///
    /// # Type Parameters
    ///
    /// * `G`: The result type of the mapping function
    /// * `F`: The type of the mapping function
    ///
    /// # Arguments
    ///
    /// * `f` - Function to apply to each error
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::validated::Validated;
    ///
    /// let invalid: Validated<&str, i32> = Validated::invalid("error");
    /// let mapped = invalid.fmap_invalid(|e| format!("Error: {}", e));
    /// assert_eq!(mapped, Validated::invalid("Error: error".to_string()));
    /// ```
    pub fn fmap_invalid<G, F>(self, f: F) -> Validated<G, A>
    where
        F: FnMut(E) -> G,
    {
        match self {
            Validated::Valid(x) => Validated::Valid(x),
            Validated::Invalid(es) => Validated::invalid_many(es.into_iter().map(f)),
        }
    }

    /// Maps a function over the error values if `Invalid`, consuming self.
    #[inline]
    #[deprecated(since = "0.15.0", note = "use `fmap_invalid` instead")]
    pub fn fmap_invalid_owned<G, F>(self, f: F) -> Validated<G, A>
    where
        F: FnMut(E) -> G,
    {
        self.fmap_invalid(f)
    }

    /// Combines errors from two `Validated` instances, consuming both.
    ///
    /// Returns `Some(Validated::Invalid(...))` with accumulated errors if either or both
    /// instances are `Invalid`. Returns `None` if both instances are `Valid` (meaning there
    /// are no validation errors to combine).
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::validated::Validated;
    ///
    /// let invalid1: Validated<&str, i32> = Validated::invalid("error1");
    /// let invalid2: Validated<&str, i32> = Validated::invalid("error2");
    /// let combined = invalid1.combine_errors(invalid2).unwrap();
    /// assert_eq!(combined.error_slice(), &["error1", "error2"]);
    ///
    /// let valid1: Validated<&str, i32> = Validated::valid(1);
    /// let valid2: Validated<&str, i32> = Validated::valid(2);
    /// assert_eq!(valid1.combine_errors(valid2), None);
    /// ```
    #[inline]
    pub fn combine_errors(self, other: Self) -> Option<Self> {
        match (self, other) {
            (Validated::Valid(_), Validated::Valid(_)) => None,
            (Validated::Valid(_), invalid @ Validated::Invalid(_)) => Some(invalid),
            (invalid @ Validated::Invalid(_), Validated::Valid(_)) => Some(invalid),
            (Validated::Invalid(mut e1), Validated::Invalid(e2)) => {
                e1.extend(e2);
                Some(Validated::Invalid(e1))
            },
        }
    }

    /// Combines errors from two `Validated` instances, consuming both.
    #[inline]
    #[deprecated(since = "0.15.0", note = "use `combine_errors` instead")]
    pub fn combine_errors_owned(self, other: Self) -> Option<Self> {
        self.combine_errors(other)
    }

    /// Sequences owned Validated values into a single Validated value.
    ///
    /// # Type Parameters
    ///
    /// * `B`: The output value type
    /// * `F`: The function type to transform collected valid values
    ///
    /// # Arguments
    ///
    /// * `values`: A vector of owned `Validated` values to sequence
    /// * `f`: A function to transform the collected valid values
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::validated::Validated;
    ///
    /// let values = vec![
    ///     Validated::<&str, i32>::valid(1),
    ///     Validated::<&str, i32>::valid(2),
    /// ];
    /// let result = Validated::sequence(values, |vals| vals.len());
    /// assert_eq!(result, Validated::valid(2));
    /// ```
    #[inline]
    pub fn sequence<B, F>(values: Vec<Self>, f: F) -> Validated<E, B>
    where
        F: FnOnce(Vec<A>) -> B,
    {
        if values.is_empty() {
            return Validated::Valid(f(Vec::new()));
        }

        if values.iter().all(|v| matches!(v, Validated::Valid(_))) {
            let valid_values: Vec<A> = values
                .into_iter()
                .filter_map(|v| match v {
                    Validated::Valid(x) => Some(x),
                    _ => None,
                })
                .collect();
            return Validated::Valid(f(valid_values));
        }

        let mut acc = ErrorAccumulator::new();
        for value in values {
            if let Validated::Invalid(es) = value {
                acc.extend(es);
            }
        }

        Validated::invalid_from_accumulator(acc)
    }

    /// Collects an iterator of Validated values into a single Validated value.
    ///
    /// If all values in the iterator are valid, returns a Valid value containing a collection of all values.
    /// If any values are invalid, returns an Invalid value containing all errors.
    ///
    /// # Type Parameters
    ///
    /// * `I`: The iterator type yielding `Validated<E, A>` items
    /// * `C`: The collection type to collect valid values into (must implement `FromIterator<A>`)
    ///
    /// # Arguments
    ///
    /// * `iter` - Iterator of Validated values
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::validated::Validated;
    ///
    /// let values = [Validated::valid(1), Validated::valid(2)];
    /// let collected: Validated<&str, Vec<i32>> = Validated::collect(values.into_iter());
    /// assert_eq!(collected, Validated::valid(vec![1, 2]));
    /// ```
    pub fn collect<I, C>(iter: I) -> Validated<E, C>
    where
        I: Iterator<Item = Validated<E, A>>,
        C: FromIterator<A>,
    {
        let mut values = Vec::new();
        let mut errors = ErrorAccumulator::new();

        for item in iter {
            match item {
                Validated::Valid(a) => values.push(a),
                Validated::Invalid(es) => errors.extend(es),
            }
        }

        match errors.into_non_empty() {
            Some(errors) => Validated::Invalid(errors),
            None => Validated::Valid(C::from_iter(values)),
        }
    }

    /// Sequences owned Validated values into a single Validated value.
    #[inline]
    #[deprecated(since = "0.15.0", note = "use `Validated::sequence` instead")]
    pub fn sequence_owned<B, F>(values: Vec<Self>, f: F) -> Validated<E, B>
    where
        F: FnOnce(Vec<A>) -> B,
    {
        Self::sequence(values, f)
    }

    /// Collects an iterator of Validated values into a single Validated value.
    #[inline]
    #[deprecated(since = "0.15.0", note = "use `Validated::collect` instead")]
    pub fn collect_owned<I, C>(iter: I) -> Validated<E, C>
    where
        I: IntoIterator<Item = Validated<E, A>>,
        C: FromIterator<A>,
    {
        Self::collect(iter.into_iter())
    }
}

#[cfg(test)]
mod tests {
    use super::Validated;

    #[test]
    fn sequence_covers_accumulation_and_empty_input() {
        let first = Validated::<&str, i32>::invalid("first");
        let second = Validated::valid(2);
        let third = Validated::invalid("third");
        let values = vec![first, second, third];
        let result = Validated::sequence(values, |items: Vec<i32>| items.iter().sum::<i32>());
        assert_eq!(result.error_slice(), &["first", "third"]);

        let empty: Vec<Validated<&str, i32>> = Vec::new();
        assert_eq!(
            Validated::sequence(empty, |items: Vec<i32>| items.len()),
            Validated::valid(0)
        );
    }

    #[test]
    fn combine_errors_handles_each_validity_case() {
        let invalid = Validated::<&str, i32>::invalid("error1");
        let other = Validated::invalid_many(["error2", "error3"]);
        assert_eq!(
            invalid
                .clone()
                .combine_errors(other.clone())
                .unwrap()
                .error_slice(),
            &["error1", "error2", "error3"]
        );
        assert_eq!(
            Validated::valid(1)
                .combine_errors(other)
                .unwrap()
                .error_slice(),
            &["error2", "error3"]
        );
        assert_eq!(
            invalid
                .combine_errors(Validated::valid(1))
                .unwrap()
                .error_slice(),
            &["error1"]
        );
    }

    #[test]
    fn combine_errors_returns_none_for_two_valid_values() {
        let result = Validated::<&str, i32>::valid(1).combine_errors(Validated::valid(2));
        assert_eq!(result, None);
    }

    #[test]
    fn deprecated_owned_combinators_work() {
        #[allow(deprecated)]
        let mapped = Validated::<&str, i32>::invalid("e").fmap_invalid_owned(|e| format!("{e}!"));
        assert_eq!(mapped.error_slice(), &["e!"]);

        #[allow(deprecated)]
        let combined = Validated::<&str, i32>::invalid("e1")
            .combine_errors_owned(Validated::invalid("e2"))
            .unwrap();
        assert_eq!(combined.error_slice(), &["e1", "e2"]);

        #[allow(deprecated)]
        let seq = Validated::sequence_owned(vec![Validated::<&str, i32>::valid(1)], |v| v[0]);
        assert_eq!(seq, Validated::valid(1));

        #[allow(deprecated)]
        let collected: Validated<&str, Vec<i32>> =
            Validated::collect_owned(vec![Validated::valid(10)]);
        assert_eq!(collected, Validated::valid(vec![10]));
    }
}
