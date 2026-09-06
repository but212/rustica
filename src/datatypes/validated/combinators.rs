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

    /// Combines errors from two `Validated` instances, consuming both.
    ///
    /// # Panics
    ///
    /// Panics if both `Validated` instances are `Valid`. This is a programmer error
    /// as there are no errors to combine.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::validated::Validated;
    ///
    /// let invalid1: Validated<&str, i32> = Validated::invalid("error1");
    /// let invalid2: Validated<&str, i32> = Validated::invalid("error2");
    /// let combined = invalid1.combine_errors(invalid2);
    /// assert_eq!(combined.error_slice(), &["error1", "error2"]);
    /// ```
    #[inline]
    pub fn combine_errors(self, other: Self) -> Self {
        match (self, other) {
            (Validated::Valid(_), Validated::Valid(_)) => unreachable!(),
            (Validated::Valid(_), invalid) => invalid,
            (invalid, Validated::Valid(_)) => invalid,
            (Validated::Invalid(mut e1), Validated::Invalid(e2)) => {
                e1.extend(e2);
                Validated::Invalid(e1)
            },
        }
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
            invalid.clone().combine_errors(other.clone()).error_slice(),
            &["error1", "error2", "error3"]
        );
        assert_eq!(
            Validated::valid(1).combine_errors(other).error_slice(),
            &["error2", "error3"]
        );
        assert_eq!(
            invalid.combine_errors(Validated::valid(1)).error_slice(),
            &["error1"]
        );
    }

    #[test]
    #[should_panic]
    fn combine_errors_rejects_two_valid_values() {
        let _ = Validated::<&str, i32>::valid(1).combine_errors(Validated::valid(2));
    }
}
