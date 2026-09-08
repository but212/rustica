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

    // --- Recovery Operations ---

    /// Attempts recovery for accumulated errors, in order.
    ///
    /// Unlike fail-fast `Result::or_else`, this method feeds each accumulated error to the
    /// recovery function. Errors are processed left-to-right. If any recovery returns
    /// `Validated::Valid(v)`, evaluation stops early and that `Valid(v)` is returned.
    /// If no recovery returns `Valid`, all errors produced by recoveries are accumulated.
    pub fn recover_all<F>(self, mut recovery: F) -> Self
    where
        F: FnMut(E) -> Self,
    {
        match self {
            Validated::Valid(v) => Validated::Valid(v),
            Validated::Invalid(errors) => {
                let mut accumulated = Vec::new();

                for error in errors {
                    match recovery(error) {
                        Validated::Valid(v) => return Validated::Valid(v),
                        Validated::Invalid(more_errors) => {
                            accumulated.extend(more_errors);
                        },
                    }
                }

                Validated::invalid_many(accumulated)
            },
        }
    }

    /// Recovers with a function that receives all errors at once.
    pub fn recover_all_at_once<F>(self, recovery: F) -> Self
    where
        F: FnOnce(Vec<E>) -> Self,
    {
        match self {
            Validated::Valid(v) => Validated::Valid(v),
            Validated::Invalid(errors) => recovery(errors.into_iter().collect()),
        }
    }

    /// Attempts to recover from errors with a fallback value.
    #[inline]
    pub fn recover_with(self, default: A) -> Self {
        match self {
            Validated::Valid(v) => Validated::Valid(v),
            Validated::Invalid(_) => Validated::Valid(default),
        }
    }
}

#[cfg(feature = "async")]
impl<E, A> Validated<E, A> {
    /// Maps an async function over the valid value, taking ownership.
    pub async fn fmap_valid_async<B, F, Fut>(self, f: F) -> Validated<E, B>
    where
        F: FnOnce(A) -> Fut + Send + 'static,
        Fut: std::future::Future<Output = B> + Send,
        B: Send + 'static,
    {
        match self {
            Validated::Valid(x) => {
                let result = f(x).await;
                Validated::Valid(result)
            },
            Validated::Invalid(e) => Validated::Invalid(e),
        }
    }

    /// Maps an async function over the error values, taking ownership.
    pub async fn fmap_invalid_async<G, F, Fut>(self, f: F) -> Validated<G, A>
    where
        F: Fn(E) -> Fut + Send + 'static,
        Fut: std::future::Future<Output = G> + Send,
        G: Send + 'static,
    {
        match self {
            Validated::Valid(x) => Validated::Valid(x),
            Validated::Invalid(es) => {
                let futures = es.into_iter().map(f);
                let results = futures::future::join_all(futures).await;
                Validated::invalid_many(results)
            },
        }
    }

    /// Chains an async validation operation, taking ownership.
    pub async fn and_then_async<B, F, Fut>(self, f: F) -> Validated<E, B>
    where
        F: FnOnce(A) -> Fut + Send + 'static,
        Fut: std::future::Future<Output = Validated<E, B>> + Send,
        B: Send + 'static,
    {
        match self {
            Validated::Valid(x) => f(x).await,
            Validated::Invalid(e) => Validated::Invalid(e),
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
    fn test_recovery_combinators() {
        let invalid: Validated<String, i32> =
            Validated::invalid_many(["e1".to_string(), "e2".to_string()]);

        let recovered = invalid.clone().recover_with(0);
        assert_eq!(recovered.unwrap(), 0);

        let early_recovery = invalid.clone().recover_all(|e| {
            if e == "e2" {
                Validated::valid(99)
            } else {
                Validated::invalid(e)
            }
        });
        assert_eq!(early_recovery.unwrap(), 99);

        let batch_recovery = invalid.clone().recover_all_at_once(|errs| {
            if errs.len() == 2 {
                Validated::valid(100)
            } else {
                Validated::invalid("unhandled".to_string())
            }
        });
        assert_eq!(batch_recovery.unwrap(), 100);

        let accumulated: Validated<String, i32> =
            invalid.recover_all(|e| Validated::invalid(format!("r:{e}")));
        assert_eq!(accumulated.error_slice(), &["r:e1", "r:e2"]);
    }
}
