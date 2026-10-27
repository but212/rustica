use super::core::NonEmptyErrors;
use crate::datatypes::validated::Validated;
use crate::traits::semigroup::Semigroup;

fn merge_errors<E>(
    a: Option<NonEmptyErrors<E>>, b: Option<NonEmptyErrors<E>>,
) -> Option<NonEmptyErrors<E>> {
    match (a, b) {
        (Some(x), Some(y)) => Some(x.combine(y)),
        (x, y) => x.or(y),
    }
}

impl<T, E> Validated<T, E> {
    /// Maps `f` over the valid value, leaving errors unchanged.
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
    pub fn map<U, F>(self, mut f: F) -> Validated<U, E>
    where
        F: FnMut(T) -> U,
    {
        match self {
            Self::Valid(x) => Validated::Valid(f(x)),
            Self::Invalid(es) => Validated::Invalid(es),
        }
    }

    /// Maps `g` over each error, leaving a valid value unchanged.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::validated::Validated;
    ///
    /// let invalid: Validated<i32, &str> = Validated::invalid("error");
    /// assert_eq!(invalid.map_err(|e| format!("{e}!")), Validated::invalid("error!".to_string()));
    /// ```
    pub fn map_err<F, G>(self, g: G) -> Validated<T, F>
    where
        G: FnMut(E) -> F,
    {
        match self {
            Self::Valid(x) => Validated::Valid(x),
            Self::Invalid(es) => Validated::Invalid(es.map(g)),
        }
    }

    /// Maps `f` over a valid value or `g` over each error.
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
    pub fn bimap<U, F, FVal, FErr>(self, mut f: FVal, g: FErr) -> Validated<U, F>
    where
        FVal: FnMut(T) -> U,
        FErr: FnMut(E) -> F,
    {
        match self {
            Self::Valid(x) => Validated::Valid(f(x)),
            Self::Invalid(es) => Validated::Invalid(es.map(g)),
        }
    }

    /// Sequences dependent validations, short-circuiting on the first error.
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
    pub fn and_then<U, F>(self, f: F) -> Validated<U, E>
    where
        F: FnOnce(T) -> Validated<U, E>,
    {
        match self {
            Self::Valid(x) => f(x),
            Self::Invalid(es) => Validated::Invalid(es),
        }
    }

    /// Combines two `Validated` values with `f`, accumulating all errors in encounter order.
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
    pub fn zip_with<U, R, F>(self, other: Validated<U, E>, f: F) -> Validated<R, E>
    where
        F: FnOnce(T, U) -> R,
    {
        match (self, other) {
            (Self::Valid(a), Validated::Valid(b)) => Validated::Valid(f(a, b)),
            (Self::Valid(_), Validated::Invalid(es)) => Validated::Invalid(es),
            (Self::Invalid(es), Validated::Valid(_)) => Validated::Invalid(es),
            (Self::Invalid(es1), Validated::Invalid(es2)) => Validated::Invalid(es1.combine(es2)),
        }
    }

    /// Combines two `Validated` values into a pair, accumulating errors.
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
    pub fn zip<U>(self, other: Validated<U, E>) -> Validated<(T, U), E> {
        self.zip_with(other, |a, b| (a, b))
    }

    /// Applies a wrapped function to a wrapped value, accumulating errors in encounter order.
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
    pub fn apply<A, B>(self, value: Validated<A, E>) -> Validated<B, E>
    where
        T: FnOnce(A) -> B,
    {
        self.zip_with(value, |f, a| f(a))
    }

    /// Combines three `Validated` values with `f`, accumulating errors.
    pub fn zip_with3<T2, T3, R, F>(
        self, second: Validated<T2, E>, third: Validated<T3, E>, f: F,
    ) -> Validated<R, E>
    where
        F: FnOnce(T, T2, T3) -> R,
    {
        match (self, second, third) {
            (Self::Valid(a), Validated::Valid(b), Validated::Valid(c)) => {
                Validated::Valid(f(a, b, c))
            },
            (v1, v2, v3) => {
                let errs = [
                    v1.into_error_opt(),
                    v2.into_error_opt(),
                    v3.into_error_opt(),
                ];
                let combined = NonEmptyErrors::combine_multiple(errs)
                    .expect("at least one error must be present in invalid arm");
                Validated::Invalid(combined)
            },
        }
    }

    /// Combines three `Validated` values into a 3-tuple, accumulating errors.
    pub fn zip3<T2, T3>(
        self, second: Validated<T2, E>, third: Validated<T3, E>,
    ) -> Validated<(T, T2, T3), E> {
        self.zip_with3(second, third, |a, b, c| (a, b, c))
    }

    /// Returns accumulated errors if either instance is invalid, or `None` if both are valid.
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
    pub fn combine_errors(self, other: Self) -> Option<NonEmptyErrors<E>> {
        merge_errors(self.into_error_opt(), other.into_error_opt())
    }

    /// Recovers using a closure given all accumulated errors.
    ///
    /// The callback receives [`NonEmptyErrors`], preserving the guarantee that
    /// an invalid value always contains at least one error.
    pub fn recover_all_at_once<F>(self, recovery: F) -> Self
    where
        F: FnOnce(NonEmptyErrors<E>) -> Self,
    {
        match self {
            Self::Valid(v) => Self::Valid(v),
            Self::Invalid(errors) => recovery(errors),
        }
    }

    /// Replaces errors with a `default` fallback value.
    pub fn recover_with(self, default: T) -> Self {
        match self {
            Self::Valid(v) => Self::Valid(v),
            Self::Invalid(_) => Self::Valid(default),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::Validated;
    use crate::datatypes::validated::NonEmptyErrors;
    use alloc::string::{String, ToString};
    use alloc::vec::Vec;
    use alloc::{format, vec};

    #[test]
    fn sequence_covers_accumulation_and_empty_input() {
        let first = Validated::<i32, &str>::invalid("first");
        let second = Validated::valid(2);
        let third = Validated::invalid("third");
        let values = vec![first, second, third];
        let result = values
            .into_iter()
            .collect::<Validated<Vec<i32>, &str>>()
            .map(|items| items.iter().sum::<i32>());
        assert_eq!(result.error_slice(), &["first", "third"]);

        let empty: Vec<Validated<i32, &str>> = Vec::new();
        assert_eq!(
            empty
                .into_iter()
                .collect::<Validated<Vec<i32>, &str>>()
                .map(|items| items.len()),
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
    fn test_collect_accepts_array_into_iterator() {
        let items = [Validated::<i32, &str>::valid(1), Validated::valid(2)];
        let collected: Validated<Vec<i32>, &str> = items.into_iter().collect();
        assert_eq!(collected, Validated::valid(vec![1, 2]));
    }

    #[test]
    fn test_recovery_combinators() {
        let invalid: Validated<i32, String> =
            Validated::invalid_many(["e1".to_string(), "e2".to_string()]);

        let recovered = invalid.clone().recover_with(0);
        assert_eq!(recovered.unwrap(), 0);

        let batch_recovery = invalid.recover_all_at_once(|errs: NonEmptyErrors<String>| {
            if errs.len() == 2 {
                Validated::valid(100)
            } else {
                Validated::invalid("unhandled".to_string())
            }
        });
        assert_eq!(batch_recovery.unwrap(), 100);

        let valid =
            Validated::<i32, String>::valid(7).recover_all_at_once(|_: NonEmptyErrors<String>| {
                panic!("recovery callback must not run for valid values")
            });
        assert_eq!(valid, Validated::valid(7));

        let preserved = Validated::<i32, String>::invalid("still invalid".to_string())
            .recover_all_at_once(|errors: NonEmptyErrors<String>| Validated::invalid_many(errors));
        assert_eq!(preserved.error_slice(), &["still invalid"]);
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

    #[test]
    fn test_zip3_all_combinations() {
        // Oracle: reference implementation by composing binary zip
        let oracle = |v1: Validated<i32, &'static str>,
                      v2: Validated<i32, &'static str>,
                      v3: Validated<i32, &'static str>|
         -> Validated<(i32, i32, i32), &'static str> {
            v1.zip(v2).zip_with(v3, |(a, b), c| (a, b, c))
        };

        let cases = [
            (
                Validated::valid(1),
                Validated::valid(2),
                Validated::valid(3),
            ),
            (
                Validated::valid(1),
                Validated::valid(2),
                Validated::invalid("e3"),
            ),
            (
                Validated::valid(1),
                Validated::invalid("e2"),
                Validated::valid(3),
            ),
            (
                Validated::valid(1),
                Validated::invalid("e2"),
                Validated::invalid("e3"),
            ),
            (
                Validated::invalid("e1"),
                Validated::valid(2),
                Validated::valid(3),
            ),
            (
                Validated::invalid("e1"),
                Validated::valid(2),
                Validated::invalid("e3"),
            ),
            (
                Validated::invalid("e1"),
                Validated::invalid("e2"),
                Validated::valid(3),
            ),
            (
                Validated::invalid("e1"),
                Validated::invalid("e2"),
                Validated::invalid("e3"),
            ),
        ];

        for (v1, v2, v3) in cases {
            let expected = oracle(v1.clone(), v2.clone(), v3.clone());
            let actual = v1.zip3(v2, v3);
            assert_eq!(actual, expected);
        }
    }
}
