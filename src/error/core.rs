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
        F: Fn(E) -> G,
        G: Clone;

    fn to_result(self) -> Result<Self::Success, E>;
}

#[inline]
pub fn sequence<A, E>(collection: Vec<Result<A, E>>) -> Result<Vec<A>, E> {
    collection.into_iter().collect()
}

#[inline]
pub fn traverse<A, B, E, F>(collection: impl IntoIterator<Item = A>, f: F) -> Result<Vec<B>, E>
where
    F: FnMut(A) -> Result<B, E>,
{
    collection.into_iter().map(f).collect()
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
        .map(|item| item.to_result().map(Into::into))
        .collect()
}

impl<T, E: Clone> WithError<E> for Result<T, E> {
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

    fn to_result(self) -> Result<Self::Success, E> {
        self
    }
}

impl<T, E> WithError<E> for Validated<E, T> {
    type Success = T;
    type ErrorOutput<G> = Validated<G, T>;

    fn fmap_error<F, G>(self, f: F) -> Self::ErrorOutput<G>
    where
        F: Fn(E) -> G,
        G: Clone,
    {
        match self {
            Validated::Valid(t) => Validated::Valid(t),
            Validated::Invalid(e) => Validated::invalid_many(e.into_iter().map(f)),
        }
    }

    fn to_result(self) -> Result<Self::Success, E> {
        match self {
            Validated::Valid(t) => Ok(t),
            Validated::Invalid(e) => Err(e
                .into_iter()
                .next()
                .expect("Validated errors cannot be empty")),
        }
    }
}

/// Extended error handling operations for enhanced composability.
///
/// This trait provides additional operations that build upon `WithError`
/// to enable more sophisticated error handling patterns while maintaining
/// categorical properties.
pub trait ErrorOps<E>: WithError<E> {
    /// Applies a recovery function if this contains an error.
    ///
    /// This is the error-handling equivalent of `Option::or_else` or
    /// `Result::or_else`, allowing for error recovery and alternative
    /// computation paths.
    ///
    /// # Type Parameters
    ///
    /// * `F`: The recovery function type
    ///
    /// # Arguments
    ///
    /// * `recovery`: Function to apply if an error is present
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::error::ErrorOps;
    ///
    /// let error_result: Result<i32, &str> = Err("failed");
    /// let recovered = error_result.recover(|_| Ok(42));
    /// assert_eq!(recovered, Ok(42));
    /// ```
    fn recover<F>(self, recovery: F) -> Self
    where
        F: FnOnce(E) -> Self,
        Self: Sized;

    /// Maps over both success and error cases simultaneously.
    ///
    /// This provides a way to transform both the success value and error
    /// in a single operation, which is useful for type conversions and
    /// context transformations.
    ///
    /// # Type Parameters
    ///
    /// * `B`: The new success type
    /// * `F`: The new error type  
    /// * `SuccessF`: The success transformation function type
    /// * `ErrorF`: The error transformation function type
    ///
    /// # Arguments
    ///
    /// * `success_f`: Function to apply to success values
    /// * `error_f`: Function to apply to error values
    fn bimap_result<B, F, SuccessF, ErrorF>(
        self, success_f: SuccessF, error_f: ErrorF,
    ) -> Result<B, F>
    where
        SuccessF: FnOnce(Self::Success) -> B,
        ErrorF: FnOnce(E) -> F,
        Self: Sized;
}

/// Implementation of ErrorOps for Result<T, E>
impl<T: Clone, E: Clone> ErrorOps<E> for Result<T, E> {
    #[inline]
    fn recover<F>(self, recovery: F) -> Self
    where
        F: FnOnce(E) -> Self,
    {
        match self {
            Ok(value) => Ok(value),
            Err(error) => recovery(error),
        }
    }

    #[inline]
    fn bimap_result<B, F, SuccessF, ErrorF>(
        self, success_f: SuccessF, error_f: ErrorF,
    ) -> Result<B, F>
    where
        SuccessF: FnOnce(T) -> B,
        ErrorF: FnOnce(E) -> F,
    {
        match self {
            Ok(value) => Ok(success_f(value)),
            Err(error) => Err(error_f(error)),
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
