use super::core::{ErrorAccumulator, NonEmptyErrors};
use crate::datatypes::validated::Validated;

impl<E, A> Validated<E, A> {
    /// Maps a function over the error values if `Invalid`, or returns the `Valid` value (cloned).
    ///
    /// If this `Validated` is `Invalid`, applies the function `f` to transform each error.
    /// If `Valid`, the original valid value `A` is cloned and returned in a new `Validated::Valid`.
    /// This method is suitable when you only have a reference (`&self`) to the `Validated` value.
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
    pub fn fmap_invalid<G, F>(&self, f: F) -> Validated<G, A>
    where
        F: Fn(&E) -> G,
        G: Clone,
        A: Clone,
    {
        match self {
            Validated::Valid(x) => Validated::Valid(x.clone()),
            Validated::Invalid(_) => {
                let mut transformed = self.iter_errors().map(f);
                let first = transformed.next().expect("invalid values have errors");
                Validated::Invalid(NonEmptyErrors::from_first_and_iter(first, transformed))
            },
        }
    }

    /// Maps a function over the error values if `Invalid` (taking ownership), or returns the `Valid` value (moved).
    ///
    /// If this `Validated` is `Invalid`, applies the function `f` to transform each error (errors `E` are moved into `f`).
    /// If `Valid`, the original valid value `A` is moved and returned in a new `Validated::Valid`.
    /// This method takes `self` by ownership, which can be more efficient as it avoids cloning the value `A` if it's `Valid`.
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
    /// let mapped = invalid.fmap_invalid_owned(|e| format!("Error: {}", e));
    /// assert_eq!(mapped, Validated::invalid("Error: error".to_string()));
    /// ```
    pub fn fmap_invalid_owned<G, F>(self, f: F) -> Validated<G, A>
    where
        F: Fn(E) -> G,
        G: Clone,
    {
        match self {
            Validated::Valid(x) => Validated::Valid(x),
            Validated::Invalid(es) => Validated::invalid_many(es.into_iter().map(f)),
        }
    }

    /// Combines errors from two Validated values.
    ///
    /// This is used internally to combine errors when both values are invalid.
    /// The function assumes at least one of the values is invalid.
    ///
    /// # Arguments
    ///
    /// * `other` - Another Validated instance to combine errors with
    ///
    /// # Panics
    ///
    /// Panics if both values are valid, as this function should only be called when
    /// at least one value is invalid.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::validated::Validated;
    ///
    /// let invalid1: Validated<&str, i32> = Validated::invalid("error1");
    /// let invalid2: Validated<&str, i32> = Validated::invalid_many(["error2", "error3"]);
    ///
    /// // Case 1: self is Invalid, other is Invalid
    /// let combined1 = invalid1.clone().combine_errors(&invalid2);
    /// assert!(combined1.is_invalid());
    /// if let Validated::Invalid(errors) = combined1 {
    ///     assert_eq!(errors.as_slice(), &["error1", "error2", "error3"]);
    /// }
    ///
    /// // Case 2: self is Valid, other is Invalid
    /// let valid1: Validated<&str, i32> = Validated::valid(1);
    /// let combined2 = valid1.clone().combine_errors(&invalid2);
    /// assert!(combined2.is_invalid());
    /// if let Validated::Invalid(errors) = combined2 {
    ///     assert_eq!(errors.as_slice(), &["error2", "error3"]);
    /// }
    ///
    /// // Case 3: self is Invalid, other is Valid
    /// let combined3 = invalid1.clone().combine_errors(&valid1);
    /// assert!(combined3.is_invalid());
    /// if let Validated::Invalid(errors) = combined3 {
    ///     assert_eq!(errors.as_slice(), &["error1"]);
    /// }
    /// ```
    ///
    /// ```rust,should_panic
    /// use rustica::datatypes::validated::Validated;
    ///
    /// // Panics if both are Valid
    /// let valid1: Validated<&str, i32> = Validated::valid(1);
    /// let valid2: Validated<&str, i32> = Validated::valid(2);
    /// let _combined_panic = valid1.combine_errors(&valid2);
    /// ```
    pub fn combine_errors(&self, other: &Self) -> Self
    where
        A: Clone,
        E: Clone,
    {
        match (self, other) {
            (Validated::Valid(_), Validated::Valid(_)) => unreachable!(),
            (Validated::Valid(_), invalid) => invalid.clone(),
            (invalid, Validated::Valid(_)) => invalid.clone(),
            (Validated::Invalid(e1), Validated::Invalid(e2)) => {
                let mut acc = ErrorAccumulator::with_capacity(e1.len() + e2.len());
                acc.extend_cloned(e1);
                acc.extend_cloned(e2);
                Validated::invalid_from_accumulator(acc)
            },
        }
    }

    /// Combines errors from two `Validated` instances, taking ownership of both.
    ///
    /// This method is more efficient than `combine_errors` when you can consume
    /// both `Validated` instances, as it avoids cloning the error collections.
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
    /// let combined = invalid1.combine_errors_owned(invalid2);
    /// assert_eq!(combined.error_slice(), &["error1", "error2"]);
    /// ```
    #[inline]
    pub fn combine_errors_owned(self, other: Self) -> Self {
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

    /// Combines multiple Validated values using a function.
    ///
    /// This is similar to `lift2` but works with a slice of Validated values.
    /// If all values are valid, applies the function to combine them.
    /// If any values are invalid, collects all errors.
    ///
    /// # Type Parameters
    ///
    /// * `B`: The result type of the combining function
    /// * `F`: The type of the combining function
    ///
    /// # Arguments
    ///
    /// * `values` - Slice of Validated values
    /// * `f` - Function to combine valid values
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::validated::Validated;
    ///
    /// let a: Validated<&str, i32> = Validated::valid(1);
    /// let b: Validated<&str, i32> = Validated::valid(2);
    /// let c: Validated<&str, i32> = Validated::valid(3);
    ///
    /// let values = [&a, &b, &c];
    /// let sum = Validated::sequence(&values, &|vs: &[i32]| {
    ///     vs.iter().sum()
    /// });
    /// assert_eq!(sum, Validated::valid(6));
    ///
    /// // Example with invalid inputs
    /// let d: Validated<&str, i32> = Validated::invalid("error1");
    /// let e: Validated<&str, i32> = Validated::valid(5);
    /// let f: Validated<&str, i32> = Validated::invalid("error2");
    /// let mixed_values = [&d, &e, &f];
    /// let mixed_result = Validated::sequence(&mixed_values, &|vs: &[i32]| vs.iter().sum::<i32>());
    /// assert!(mixed_result.is_invalid());
    /// if let Validated::Invalid(errors) = mixed_result {
    ///     assert_eq!(errors.as_slice(), &["error1", "error2"]);
    /// }
    ///
    /// // Example with empty input
    /// let empty_values: &[&Validated<&str, i32>; 0] = &[];
    /// let empty_result = Validated::sequence(empty_values, &|vs: &[i32]| vs.iter().sum::<i32>());
    /// assert_eq!(empty_result, Validated::valid(0));
    /// ```
    pub fn sequence<B, F>(values: &[&Validated<E, A>], f: &F) -> Validated<E, B>
    where
        F: Fn(&[A]) -> B,
        B: Clone,
        A: Clone,
        E: Clone,
    {
        // Early check for empty slice
        if values.is_empty() {
            return Validated::Valid(f(&[]));
        }

        // First pass to check if all are valid (fast path)
        if values.iter().all(|v| matches!(v, Validated::Valid(_))) {
            let valid_values: Vec<A> = values
                .iter()
                .filter_map(|v| match v {
                    Validated::Valid(x) => Some(x.clone()),
                    _ => None,
                })
                .collect();
            return Validated::Valid(f(&valid_values));
        }

        // Collect all errors using iterator methods
        let mut acc = ErrorAccumulator::new();
        for value in values {
            if let Validated::Invalid(es) = value {
                acc.extend_cloned(es);
            }
        }

        Validated::invalid_from_accumulator(acc)
    }

    /// Sequences owned Validated values into a single Validated value.
    ///
    /// This method is more efficient than `sequence` when you can consume the
    /// Validated instances, as it avoids cloning error collections.
    ///
    /// # Type Parameters
    ///
    /// * `B`: The output value type (must implement `Clone`)
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
    /// let result = Validated::sequence_owned(values, |vals| vals.len());
    /// assert_eq!(result, Validated::valid(2));
    /// ```
    #[inline]
    pub fn sequence_owned<B, F>(values: Vec<Self>, f: F) -> Validated<E, B>
    where
        F: Fn(Vec<A>) -> B,
        B: Clone,
    {
        // Early check for empty vec
        if values.is_empty() {
            return Validated::Valid(f(Vec::new()));
        }

        // First pass to check if all are valid (fast path)
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

        // Collect all errors using extend_owned for efficiency
        let mut acc = ErrorAccumulator::new();
        for value in values {
            if let Validated::Invalid(es) = value {
                acc.extend_owned(es);
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
    /// # Trait Bounds
    ///
    /// * `I: Iterator<Item = Validated<E, A>>` - The iterator must yield `Validated<E, A>` items
    /// * `C: FromIterator<A> + Clone` - The collection must be constructible from an iterator of `A` values
    /// * `A: Clone` - The value type must be cloneable
    /// * `E: Clone` - The error type must be cloneable
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
    /// let values = vec![
    ///     Validated::<&str, i32>::valid(1),
    ///     Validated::<&str, i32>::valid(2),
    ///     Validated::<&str, i32>::valid(3),
    /// ];
    ///
    /// let collected: Validated<&str, Vec<i32>> = Validated::collect(values.iter().cloned());
    /// assert_eq!(collected, Validated::valid(vec![1, 2, 3]));
    ///
    /// let mixed = vec![
    ///     Validated::<&str, i32>::valid(1),
    ///     Validated::<&str, i32>::invalid("error"),
    ///     Validated::<&str, i32>::valid(3),
    /// ];
    ///
    /// let collected: Validated<&str, Vec<i32>> = Validated::collect(mixed.iter().cloned());
    /// assert!(collected.is_invalid());
    /// if let Validated::Invalid(errors) = collected {
    ///     assert_eq!(errors.as_slice(), &["error"]);
    /// }
    ///
    /// // Example with all invalid inputs
    /// let all_invalid = vec![
    ///     Validated::<&str, i32>::invalid("err1"),
    ///     Validated::<&str, i32>::invalid("err2"),
    /// ];
    /// let collected_all_invalid: Validated<&str, Vec<i32>> = Validated::collect(all_invalid.iter().cloned());
    /// assert!(collected_all_invalid.is_invalid());
    /// if let Validated::Invalid(errors) = collected_all_invalid {
    ///     assert_eq!(errors.as_slice(), &["err1", "err2"]);
    /// }
    ///
    /// // Example with an empty iterator
    /// let empty_iter: std::vec::IntoIter<Validated<&str, i32>> = vec![].into_iter();
    /// let collected_empty: Validated<&str, Vec<i32>> = Validated::collect(empty_iter);
    /// assert_eq!(collected_empty, Validated::valid(Vec::<i32>::new()));
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
                Validated::Invalid(es) => errors.extend_owned(es),
            }
        }

        match errors.into_non_empty() {
            Some(errors) => Validated::Invalid(errors),
            None => Validated::Valid(C::from_iter(values)),
        }
    }

    /// Collects owned Validated values from an iterator into a single Validated value.
    ///
    /// This method is more efficient than `collect` when working with owned Validated
    /// instances, as it can move errors instead of cloning them.
    ///
    /// # Type Parameters
    ///
    /// * `I`: The iterator type yielding `Validated<E, A>` items
    /// * `C`: The collection type to collect valid values into (must implement `FromIterator<A>`)
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
    /// let result: Validated<&str, Vec<i32>> = Validated::collect_owned(values.into_iter());
    /// assert_eq!(result, Validated::valid(vec![1, 2]));
    /// ```
    #[inline]
    pub fn collect_owned<I, C>(iter: I) -> Validated<E, C>
    where
        I: Iterator<Item = Validated<E, A>>,
        C: FromIterator<A>,
    {
        let mut acc = ErrorAccumulator::new();
        let mut values = Vec::new();

        for item in iter {
            match item {
                Validated::Valid(a) => values.push(a),
                Validated::Invalid(es) => acc.extend_owned(es),
            }
        }

        match acc.into_non_empty() {
            Some(errors) => Validated::Invalid(errors),
            None => Validated::Valid(C::from_iter(values)),
        }
    }
}
