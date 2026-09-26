use super::core::NonEmptyErrors;
use crate::datatypes::validated::Validated;

impl<T, E> Validated<T, E> {
    /// Maps a function over the valid value if `Valid`, or returns the `Invalid` value unchanged.
    ///
    /// # Type Parameters
    ///
    /// * `U`: The result type of the mapping function
    /// * `F`: The type of the mapping function
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::validated::Validated;
    ///
    /// let valid: Validated<i32, &str> = Validated::valid(10);
    /// assert_eq!(valid.map(|v| v * 2), Validated::valid(20));
    ///
    /// let invalid: Validated<i32, &str> = Validated::invalid("error");
    /// assert_eq!(invalid.map(|v| v * 2), Validated::invalid("error"));
    /// ```
    #[inline]
    pub fn map<U, F>(self, mut f: F) -> Validated<U, E>
    where
        F: FnMut(T) -> U,
    {
        match self {
            Validated::Valid(x) => Validated::Valid(f(x)),
            Validated::Invalid(es) => Validated::Invalid(es),
        }
    }

    /// Functional alias for [`map`](Self::map).
    ///
    /// Maps a function over the valid value if `Valid`, or returns the `Invalid` value unchanged.
    #[deprecated(
        since = "0.19.0",
        note = "use `map` instead; scheduled for removal in 0.20.0"
    )]
    #[inline]
    pub fn fmap<U, F>(self, f: F) -> Validated<U, E>
    where
        F: FnMut(T) -> U,
    {
        self.map(f)
    }

    /// Maps a function over each error value if `Invalid`, or returns the `Valid` value unchanged.
    ///
    /// # Type Parameters
    ///
    /// * `F`: The result error type of the mapping function
    /// * `G`: The type of the mapping function
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::validated::Validated;
    ///
    /// let invalid: Validated<i32, &str> = Validated::invalid("error");
    /// assert_eq!(invalid.map_err(|e| format!("{e}!")), Validated::invalid("error!".to_string()));
    /// ```
    #[inline]
    pub fn map_err<F, G>(self, g: G) -> Validated<T, F>
    where
        G: FnMut(E) -> F,
    {
        match self {
            Validated::Valid(x) => Validated::Valid(x),
            Validated::Invalid(es) => Validated::invalid_many(es.into_iter().map(g)),
        }
    }

    /// Maps both the valid value and the error values simultaneously.
    ///
    /// If `Valid(a)`, applies `f` to produce `Valid(f(a))`.
    /// If `Invalid(errors)`, applies `g` to each error in the collection.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::validated::Validated;
    ///
    /// let valid: Validated<i32, &str> = Validated::valid(10);
    /// let result = valid.bimap(|v| v * 2, |e| format!("Err: {e}"));
    /// assert_eq!(result, Validated::valid(20));
    ///
    /// let invalid: Validated<i32, &str> = Validated::invalid("failed");
    /// let result = invalid.bimap(|v| v * 2, |e| format!("Err: {e}"));
    /// assert_eq!(result, Validated::invalid("Err: failed".to_string()));
    /// ```
    #[inline]
    pub fn bimap<U, F, FVal, FErr>(self, mut f: FVal, g: FErr) -> Validated<U, F>
    where
        FVal: FnMut(T) -> U,
        FErr: FnMut(E) -> F,
    {
        match self {
            Validated::Valid(x) => Validated::Valid(f(x)),
            Validated::Invalid(es) => Validated::invalid_many(es.into_iter().map(g)),
        }
    }

    /// Chains a validation operation, short-circuiting if `Invalid`.
    ///
    /// Unlike `Applicative::apply` which accumulates errors across independent validations,
    /// `and_then` models dependent validations where the second validation depends on the
    /// success of the first.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::validated::Validated;
    ///
    /// let parse_positive = |s: &str| -> Validated<i32, String> {
    ///     s.parse::<i32>()
    ///         .map_err(|e| e.to_string())
    ///         .into()
    /// };
    ///
    /// let step1: Validated<&str, String> = Validated::valid("42");
    /// let step2 = step1.and_then(parse_positive);
    /// assert_eq!(step2, Validated::valid(42));
    ///
    /// let fail_step1: Validated<&str, String> = Validated::invalid("bad input".to_string());
    /// assert_eq!(fail_step1.and_then(parse_positive), Validated::invalid("bad input".to_string()));
    /// ```
    #[inline]
    pub fn and_then<U, F>(self, f: F) -> Validated<U, E>
    where
        F: FnOnce(T) -> Validated<U, E>,
    {
        match self {
            Validated::Valid(x) => f(x),
            Validated::Invalid(es) => Validated::Invalid(es),
        }
    }

    /// Combines two `Validated` values using a binary function, accumulating all errors if any.
    ///
    /// If both are `Valid`, invokes `f(a, b)` and returns `Valid`.
    /// If either or both are `Invalid`, accumulates all errors in encounter order.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::validated::Validated;
    ///
    /// let v1: Validated<i32, &str> = Validated::valid(10);
    /// let v2: Validated<i32, &str> = Validated::valid(20);
    /// assert_eq!(v1.zip_with(v2, |a, b| a + b), Validated::valid(30));
    ///
    /// let e1: Validated<i32, &str> = Validated::invalid("err1");
    /// let e2: Validated<i32, &str> = Validated::invalid("err2");
    /// let res = e1.zip_with(e2, |a, b| a + b);
    /// assert_eq!(res.error_slice(), &["err1", "err2"]);
    /// ```
    #[inline]
    pub fn zip_with<U, R, F>(self, other: Validated<U, E>, f: F) -> Validated<R, E>
    where
        F: FnOnce(T, U) -> R,
    {
        match (self, other) {
            (Validated::Valid(a), Validated::Valid(b)) => Validated::Valid(f(a, b)),
            (Validated::Valid(_), Validated::Invalid(es)) => Validated::Invalid(es),
            (Validated::Invalid(es), Validated::Valid(_)) => Validated::Invalid(es),
            (Validated::Invalid(mut es1), Validated::Invalid(es2)) => {
                es1.extend(es2);
                Validated::Invalid(es1)
            },
        }
    }

    /// Combines two `Validated` values into a pair, accumulating all errors if any.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::validated::Validated;
    ///
    /// let v1: Validated<i32, &str> = Validated::valid(1);
    /// let v2: Validated<&str, &str> = Validated::valid("ok");
    /// assert_eq!(v1.zip(v2), Validated::valid((1, "ok")));
    /// ```
    #[inline]
    pub fn zip<U>(self, other: Validated<U, E>) -> Validated<(T, U), E> {
        self.zip_with(other, |a, b| (a, b))
    }

    /// Applies a function wrapped in `Validated` to a value wrapped in `Validated`,
    /// accumulating all errors if any.
    ///
    /// If both are `Valid`, applies `f(a)`. If either or both are `Invalid`,
    /// accumulates all errors in encounter order.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::validated::Validated;
    ///
    /// let f: Validated<fn(i32) -> i32, &str> = Validated::valid(|x| x * 2);
    /// let v: Validated<i32, &str> = Validated::valid(10);
    /// assert_eq!(f.apply(v), Validated::valid(20));
    ///
    /// let err_fn: Validated<fn(i32) -> i32, &str> = Validated::invalid("fn error");
    /// let err_val: Validated<i32, &str> = Validated::invalid("val error");
    /// let result = err_fn.apply(err_val);
    /// assert_eq!(result.error_slice(), &["fn error", "val error"]);
    /// ```
    #[inline]
    pub fn apply<A, B>(self, value: Validated<A, E>) -> Validated<B, E>
    where
        T: FnOnce(A) -> B,
    {
        self.zip_with(value, |f, a| f(a))
    }

    /// Combines three `Validated` values using a ternary function, accumulating all errors if any.
    #[inline]
    pub fn zip_with3<T2, T3, R, F>(
        self, second: Validated<T2, E>, third: Validated<T3, E>, f: F,
    ) -> Validated<R, E>
    where
        F: FnOnce(T, T2, T3) -> R,
    {
        self.zip(second).zip_with(third, |(a, b), c| f(a, b, c))
    }

    /// Combines three `Validated` values into a 3-tuple, accumulating all errors if any.
    #[inline]
    pub fn zip3<T2, T3>(
        self, second: Validated<T2, E>, third: Validated<T3, E>,
    ) -> Validated<(T, T2, T3), E> {
        self.zip_with3(second, third, |a, b, c| (a, b, c))
    }

    /// Lifts a binary function over two `Validated` values, accumulating all errors if any.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::validated::Validated;
    ///
    /// let v1: Validated<i32, &str> = Validated::valid(10);
    /// let v2: Validated<i32, &str> = Validated::valid(20);
    /// let sum = Validated::lift2(|a, b| a + b, v1, v2);
    /// assert_eq!(sum, Validated::valid(30));
    /// ```
    #[inline]
    pub fn lift2<T1, T2, F>(f: F, v1: Validated<T1, E>, v2: Validated<T2, E>) -> Validated<T, E>
    where
        F: FnOnce(T1, T2) -> T,
    {
        v1.zip_with(v2, f)
    }

    /// Lifts a ternary function over three `Validated` values, accumulating all errors if any.
    #[inline]
    pub fn lift3<T1, T2, T3, F>(
        f: F, v1: Validated<T1, E>, v2: Validated<T2, E>, v3: Validated<T3, E>,
    ) -> Validated<T, E>
    where
        F: FnOnce(T1, T2, T3) -> T,
    {
        v1.zip_with3(v2, v3, f)
    }

    /// Combines errors from two `Validated` instances, consuming both.
    ///
    /// Returns `Some(NonEmptyErrors<E>)` with accumulated errors if either or both
    /// instances are `Invalid`. Returns `None` if both instances are `Valid` (meaning there
    /// are no validation errors to combine).
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::validated::Validated;
    ///
    /// let invalid1: Validated<i32, &str> = Validated::invalid("error1");
    /// let invalid2: Validated<i32, &str> = Validated::invalid("error2");
    /// let combined = invalid1.combine_errors(invalid2).unwrap();
    /// assert_eq!(combined.as_slice(), &["error1", "error2"]);
    ///
    /// let valid1: Validated<i32, &str> = Validated::valid(1);
    /// let valid2: Validated<i32, &str> = Validated::valid(2);
    /// assert_eq!(valid1.combine_errors(valid2), None);
    /// ```
    #[inline]
    pub fn combine_errors(self, other: Self) -> Option<NonEmptyErrors<E>> {
        match (self, other) {
            (Validated::Valid(_), Validated::Valid(_)) => None,
            (Validated::Valid(_), Validated::Invalid(es)) => Some(es),
            (Validated::Invalid(es), Validated::Valid(_)) => Some(es),
            (Validated::Invalid(mut e1), Validated::Invalid(e2)) => {
                e1.extend(e2);
                Some(e1)
            },
        }
    }

    /// Sequences owned Validated values into a single Validated value.
    ///
    /// # Type Parameters
    ///
    /// * `U`: The output value type
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
    ///     Validated::<i32, &str>::valid(1),
    ///     Validated::<i32, &str>::valid(2),
    /// ];
    /// let result = Validated::sequence(values, |vals| vals.len());
    /// assert_eq!(result, Validated::valid(2));
    /// ```
    #[inline]
    pub fn sequence<U, F>(values: Vec<Self>, f: F) -> Validated<U, E>
    where
        F: FnOnce(Vec<T>) -> U,
    {
        match Self::collect::<_, Vec<T>>(values.into_iter()) {
            Validated::Valid(valid_values) => Validated::Valid(f(valid_values)),
            Validated::Invalid(errors) => Validated::Invalid(errors),
        }
    }

    /// Collects an iterator of Validated values into a single Validated value.
    ///
    /// If all values in the iterator are valid, returns a Valid value containing a collection of all values.
    /// If any values are invalid, returns an Invalid value containing all errors.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::validated::Validated;
    ///
    /// let values = [Validated::<i32, &str>::valid(1), Validated::valid(2)];
    /// let collected: Validated<Vec<i32>, &str> = Validated::collect(values.into_iter());
    /// assert_eq!(collected, Validated::valid(vec![1, 2]));
    /// ```
    pub fn collect<I, C>(iter: I) -> Validated<C, E>
    where
        I: Iterator<Item = Validated<T, E>>,
        C: FromIterator<T>,
    {
        let mut values = Vec::new();
        let mut errors = Vec::new();

        for item in iter {
            match item {
                Validated::Valid(a) => values.push(a),
                Validated::Invalid(es) => errors.extend(es),
            }
        }

        match NonEmptyErrors::try_from_vec(errors) {
            Some(errors) => Validated::Invalid(errors),
            None => Validated::Valid(C::from_iter(values)),
        }
    }

    // --- Recovery Operations ---

    /// Attempts recovery for accumulated errors, in order.
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

                // Invariant: `errors` (NonEmptyErrors) has ≥1 element,
                // and each recovery call returning Invalid yields NonEmptyErrors (≥1 element).
                // Thus `accumulated` is guaranteed to be non-empty at this point.
                debug_assert!(
                    !accumulated.is_empty(),
                    "NonEmptyErrors invariant violated: accumulated errors empty after processing non-empty input"
                );
                Validated::Invalid(
                    NonEmptyErrors::try_from_vec(accumulated)
                        .expect("invariant: accumulated errors non-empty (see debug_assert above)"),
                )
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
    pub fn recover_with(self, default: T) -> Self {
        match self {
            Validated::Valid(v) => Validated::Valid(v),
            Validated::Invalid(_) => Validated::Valid(default),
        }
    }
}

#[cfg(feature = "async")]
impl<T, E> Validated<T, E> {
    /// Maps an async function over the valid value, taking ownership.
    #[deprecated(
        since = "0.19.0",
        note = "use native async/await and pattern matching; scheduled for removal in 0.20.0"
    )]
    pub async fn map_async<U, F, Fut>(self, f: F) -> Validated<U, E>
    where
        F: FnOnce(T) -> Fut,
        Fut: std::future::Future<Output = U>,
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
    #[deprecated(
        since = "0.19.0",
        note = "use native async/await and pattern matching or iteration; scheduled for removal in 0.20.0"
    )]
    pub async fn map_err_async<F, G, Fut>(self, f: G) -> Validated<T, F>
    where
        G: Fn(E) -> Fut,
        Fut: std::future::Future<Output = F>,
    {
        match self {
            Validated::Valid(x) => Validated::Valid(x),
            Validated::Invalid(es) => {
                let mut results = Vec::with_capacity(es.len());
                for err in es {
                    results.push(f(err).await);
                }
                Validated::invalid_many(results)
            },
        }
    }

    /// Chains an async validation operation, taking ownership.
    #[deprecated(
        since = "0.19.0",
        note = "use native async/await and pattern matching; scheduled for removal in 0.20.0"
    )]
    pub async fn and_then_async<U, F, Fut>(self, f: F) -> Validated<U, E>
    where
        F: FnOnce(T) -> Fut,
        Fut: std::future::Future<Output = Validated<U, E>>,
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
        let first = Validated::<i32, &str>::invalid("first");
        let second = Validated::valid(2);
        let third = Validated::invalid("third");
        let values = vec![first, second, third];
        let result = Validated::sequence(values, |items: Vec<i32>| items.iter().sum::<i32>());
        assert_eq!(result.error_slice(), &["first", "third"]);

        let empty: Vec<Validated<i32, &str>> = Vec::new();
        assert_eq!(
            Validated::sequence(empty, |items: Vec<i32>| items.len()),
            Validated::valid(0)
        );
    }

    #[test]
    fn combine_errors_handles_each_validity_case() {
        let invalid = Validated::<i32, &str>::invalid("error1");
        let other = Validated::invalid_many(["error2", "error3"]);
        assert_eq!(
            invalid
                .clone()
                .combine_errors(other.clone())
                .unwrap()
                .as_slice(),
            &["error1", "error2", "error3"]
        );
        assert_eq!(
            Validated::valid(1)
                .combine_errors(other)
                .unwrap()
                .as_slice(),
            &["error2", "error3"]
        );
        assert_eq!(
            invalid
                .combine_errors(Validated::valid(1))
                .unwrap()
                .as_slice(),
            &["error1"]
        );
    }

    #[test]
    fn combine_errors_returns_none_for_two_valid_values() {
        let result = Validated::<i32, &str>::valid(1).combine_errors(Validated::valid(2));
        assert_eq!(result, None);
    }

    #[test]
    fn test_recovery_combinators() {
        let invalid: Validated<i32, String> =
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

        let accumulated: Validated<i32, String> =
            invalid.recover_all(|e| Validated::invalid(format!("r:{e}")));
        assert_eq!(accumulated.error_slice(), &["r:e1", "r:e2"]);
    }

    #[cfg(feature = "async")]
    #[tokio::test]
    #[allow(deprecated)]
    async fn test_map_err_async_sequential() {
        let invalid: Validated<String, i32> = Validated::invalid_many([1, 2, 3]);
        let mapped = invalid
            .map_err_async(|e| async move { format!("err_{}", e * 10) })
            .await;
        assert_eq!(mapped.error_slice(), &["err_10", "err_20", "err_30"]);
    }

    #[test]
    fn test_inherent_map_and_bimap() {
        let valid: Validated<i32, &str> = Validated::valid(10);
        let mapped_val = valid.clone().map(|v| v * 3);
        assert_eq!(mapped_val, Validated::valid(30));

        let bimapped_val = valid.bimap(|v| v + 5, |e| format!("E: {e}"));
        assert_eq!(bimapped_val, Validated::valid(15));

        let invalid: Validated<i32, &str> = Validated::invalid_many(["err1", "err2"]);
        let mapped_err = invalid.clone().map_err(|e| format!("{e}!"));
        assert_eq!(
            mapped_err,
            Validated::invalid_many(["err1!".to_string(), "err2!".to_string()])
        );

        let bimapped_err = invalid.bimap(|v| v * 2, |e| format!("E: {e}"));
        assert_eq!(
            bimapped_err,
            Validated::invalid_many(["E: err1".to_string(), "E: err2".to_string()])
        );
    }

    #[test]
    fn test_sync_and_then() {
        let valid: Validated<i32, &str> = Validated::valid(10);
        let stepped = valid.and_then(|x| Validated::valid(x * 2));
        assert_eq!(stepped, Validated::valid(20));

        let fail_step: Validated<i32, &str> =
            Validated::valid(10).and_then(|_| Validated::invalid("fail"));
        assert_eq!(fail_step, Validated::invalid("fail"));

        let initial_invalid: Validated<i32, &str> = Validated::invalid("initial");
        let never_called = initial_invalid.and_then(|x| Validated::valid(x * 2));
        assert_eq!(never_called, Validated::invalid("initial"));
    }
}
