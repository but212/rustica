//! # Core Error Category Theory Abstractions
//!
//! This module extends the existing `WithError` trait and provides
//! foundational abstractions for composable, type-safe error management.

use crate::datatypes::validated::{Validated, core::ErrorAccumulator};
use crate::traits::hkt::HKT;

pub trait WithError<E>: HKT {
    type Success;
    type ErrorOutput<G>;

    fn fmap_error<F, G>(self, f: F) -> Self::ErrorOutput<G>
    where
        F: Fn(E) -> G;

    fn into_result(self) -> Result<Self::Success, E>;

    #[deprecated(since = "0.16.0", note = "Use `into_result` instead.")]
    fn to_result(self) -> Result<Self::Success, E>
    where
        Self: Sized,
    {
        self.into_result()
    }
}

pub fn traverse_validated<A, B, E, F>(
    collection: impl IntoIterator<Item = A>, mut f: F,
) -> Validated<E, Vec<B>>
where
    F: FnMut(A) -> Result<B, E>,
{
    let mut values = Vec::new();
    let mut errors = ErrorAccumulator::new();

    for item in collection {
        match f(item) {
            Ok(value) => values.push(value),
            Err(error) => errors.push(error),
        }
    }

    match errors.into_non_empty() {
        Some(errors) => Validated::Invalid(errors),
        None => Validated::Valid(values),
    }
}

#[inline]
pub fn sequence_with_error<C, T, E>(collection: Vec<C>) -> Result<Vec<T>, E>
where
    C: WithError<E>,
    C::Success: Into<T>,
{
    collection
        .into_iter()
        .map(|item| item.into_result().map(Into::into))
        .collect()
}

impl<T, E> WithError<E> for Result<T, E> {
    type Success = T;
    type ErrorOutput<G> = Result<T, G>;

    fn fmap_error<F, G>(self, f: F) -> Self::ErrorOutput<G>
    where
        F: Fn(E) -> G,
    {
        match self {
            Ok(t) => Ok(t),
            Err(e) => Err(f(e)),
        }
    }

    fn into_result(self) -> Result<Self::Success, E> {
        self
    }
}

impl<T, E> WithError<E> for Validated<E, T> {
    type Success = T;
    type ErrorOutput<G> = Validated<G, T>;

    fn fmap_error<F, G>(self, f: F) -> Self::ErrorOutput<G>
    where
        F: Fn(E) -> G,
    {
        match self {
            Validated::Valid(t) => Validated::Valid(t),
            Validated::Invalid(e) => Validated::invalid_many(e.into_iter().map(f)),
        }
    }

    fn into_result(self) -> Result<Self::Success, E> {
        match self {
            Validated::Valid(t) => Ok(t),
            Validated::Invalid(e) => Err(e
                .into_iter()
                .next()
                .expect("Validated errors cannot be empty")),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::traverse_validated;
    use crate::datatypes::validated::Validated;

    #[test]
    fn traverse_validated_accumulates_errors_in_input_order() {
        let result = traverse_validated([1, 2, 3], |value| {
            if value % 2 == 0 {
                Ok(value * 10)
            } else {
                Err(format!("odd:{value}"))
            }
        });

        assert_eq!(
            result,
            Validated::invalid_many(["odd:1".to_string(), "odd:3".to_string()])
        );
    }

    #[test]
    fn traverse_validated_keeps_all_successes() {
        let result = traverse_validated([1, 2, 3], |value| Ok::<_, String>(value * 10));

        assert_eq!(result, Validated::valid(vec![10, 20, 30]));
    }
}

#[cfg(test)]
mod unit_tests {
    use super::sequence_with_error;
    use crate::datatypes::validated::Validated;

    #[test]
    fn sequence_with_error_accepts_non_clone_values() {
        struct NoClone(&'static str);
        let result: Result<Vec<NoClone>, NoClone> =
            sequence_with_error(vec![Validated::Valid(NoClone("value"))]);
        match result {
            Ok(values) => assert_eq!(values[0].0, "value"),
            Err(_) => panic!("expected success"),
        }
    }

    #[test]
    fn sequence_with_error_preserves_order_and_returns_first_error() {
        let values: Vec<Result<i32, &str>> = vec![Ok(1), Ok(2)];
        assert_eq!(sequence_with_error(values), Ok(vec![1, 2]));
        let values = vec![Ok(1), Err("first"), Err("second")];
        let result: Result<Vec<i32>, &str> = sequence_with_error(values);
        assert_eq!(result, Err("first"));
        let values: Vec<Result<i32, &str>> = Vec::new();
        assert_eq!(sequence_with_error(values), Ok(Vec::<i32>::new()));
        let validated = vec![
            Validated::valid(1),
            Validated::invalid("first"),
            Validated::invalid("second"),
        ];
        let result: Result<Vec<i32>, &str> = sequence_with_error(validated);
        assert_eq!(result, Err("first"));
    }

    #[test]
    fn with_error_into_result_and_deprecated_to_result() {
        use super::WithError;

        let res: Result<i32, &str> = Ok(10);
        assert_eq!(res.into_result(), Ok(10));

        let res_err: Result<i32, &str> = Err("err");
        assert_eq!(res_err.into_result(), Err("err"));

        let val_valid: Validated<&str, i32> = Validated::valid(20);
        assert_eq!(val_valid.into_result(), Ok(20));

        let val_invalid: Validated<&str, i32> = Validated::invalid("invalid");
        assert_eq!(val_invalid.into_result(), Err("invalid"));

        #[allow(deprecated)]
        {
            let res: Result<i32, &str> = Ok(10);
            assert_eq!(res.to_result(), Ok(10));

            let val_valid: Validated<&str, i32> = Validated::valid(20);
            assert_eq!(val_valid.to_result(), Ok(20));
        }
    }
}
