//! # Core Error Category Theory Abstractions
//!
//! This module extends the existing `WithError` trait and introduces the `ErrorCategory`
//! trait for category-theoretic error handling. It provides the foundational abstractions
//! for composable, type-safe error management.

use crate::datatypes::either::Either;
use crate::datatypes::validated::Validated;
use crate::utils::error_utils::WithError;
use smallvec::smallvec;

/// A category-theoretic abstraction for error handling types.
///
/// `ErrorCategory` provides a unified interface for different error handling patterns,
/// ensuring that all error transformations follow categorical laws and maintain
/// functional purity.
///
/// # Type Parameters
///
/// * `E`: The error type that this category handles
///
/// # Laws
///
/// Implementations must satisfy the following categorical laws:
///
/// ## Identity Law
/// ```text
/// lift(x).handle_error() == lift(x)
/// ```
///
/// ## Composition Law  
/// ```text
/// fmap_error(f . g) == fmap_error(f) . fmap_error(g)
/// ```
///
/// # Examples
///
/// ```rust
/// use rustica::error::ErrorCategory;
///
/// // Result implements ErrorCategory
/// let success = <Result<(), String> as ErrorCategory<String>>::lift(42);
/// assert_eq!(success, Ok(42));
///
/// let error = <Result<(), String> as ErrorCategory<String>>::handle_error("failed".to_string());
/// assert_eq!(error, Err("failed".to_string()));
/// ```
pub trait ErrorCategory<E> {
    /// The error functor type that wraps values and errors
    type ErrorFunctor<T: Clone>: WithError<E>;

    /// Lifts a pure value into the error context.
    ///
    /// This operation represents the "success" case and should never fail.
    /// It's the categorical identity for successful computations.
    ///
    /// # Arguments
    ///
    /// * `value`: The value to lift into the error context
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::error::ErrorCategory;
    ///
    /// let lifted: Result<i32, String> = <Result<(), String> as ErrorCategory<String>>::lift(42);
    /// assert_eq!(lifted, Ok(42));
    /// ```
    fn lift<T: Clone>(value: T) -> Self::ErrorFunctor<T>;

    /// Creates an error instance in the error context.
    ///
    /// This operation represents the "failure" case and encapsulates
    /// the error according to the specific error handling strategy.
    ///
    /// # Arguments
    ///
    /// * `error`: The error to wrap in the error context
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::error::ErrorCategory;
    ///
    /// let error: Result<i32, String> = <Result<(), String> as ErrorCategory<String>>::handle_error("failed".to_string());
    /// assert_eq!(error, Err("failed".to_string()));
    /// ```
    fn handle_error<T: Clone>(error: E) -> Self::ErrorFunctor<T>;
}

/// Implementation of ErrorCategory for Result<T, E>
///
/// Result represents the most common error handling pattern in Rust,
/// providing fail-fast semantics where the first error stops computation.
impl<E: Clone> ErrorCategory<E> for Result<(), E> {
    type ErrorFunctor<T: Clone> = Result<T, E>;

    #[inline]
    fn lift<T>(value: T) -> Result<T, E> {
        Ok(value)
    }

    #[inline]
    fn handle_error<T>(error: E) -> Result<T, E> {
        Err(error)
    }
}

/// Implementation of ErrorCategory for Either<E, T>
///
/// Either provides a more general two-possibility type without the
/// semantic baggage of success/failure, making it suitable for
/// representing alternative computations.
impl<E> ErrorCategory<E> for Either<E, ()> {
    type ErrorFunctor<T: Clone> = Either<E, T>;

    #[inline]
    fn lift<T>(value: T) -> Either<E, T> {
        Either::Right(value)
    }

    #[inline]
    fn handle_error<T>(error: E) -> Either<E, T> {
        Either::Left(error)
    }
}

/// Implementation of ErrorCategory for Validated<E, T>
///
/// Validated provides error accumulation semantics, collecting all
/// errors rather than failing fast. This is particularly useful
/// for form validation and data parsing scenarios.
impl<E: Clone> ErrorCategory<E> for Validated<E, ()> {
    type ErrorFunctor<T: Clone> = Validated<E, T>;

    #[inline]
    fn lift<T>(value: T) -> Validated<E, T> {
        Validated::Valid(value)
    }

    #[inline]
    fn handle_error<T: Clone>(error: E) -> Validated<E, T> {
        Validated::invalid(error)
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
    ///
    /// Maps over both success and error cases simultaneously.
    ///
    /// This provides a way to transform both the success value and error
    /// in a single operation, which is useful for type conversions and
    /// context transformations.
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

/// Implementation of ErrorOps for Either<E, T>
impl<E: Clone, T: Clone> ErrorOps<E> for Either<E, T> {
    #[inline]
    fn recover<F>(self, recovery: F) -> Self
    where
        F: FnOnce(E) -> Self,
    {
        match self {
            Either::Right(value) => Either::Right(value),
            Either::Left(error) => recovery(error),
        }
    }

    fn bimap_result<B, F, SuccessF, ErrorF>(
        self, success_f: SuccessF, error_f: ErrorF,
    ) -> Result<B, F>
    where
        SuccessF: FnOnce(Self::Success) -> B,
        ErrorF: FnOnce(E) -> F,
        Self: Sized,
    {
        match self {
            Either::Right(value) => Ok(success_f(value)),
            Either::Left(error) => Err(error_f(error)),
        }
    }
}

/// Implementation of ErrorOps for Validated<E, T>
impl<E: Clone, T: Clone> ErrorOps<E> for Validated<E, T> {
    #[inline]
    fn recover<F>(self, recovery: F) -> Self
    where
        F: FnOnce(E) -> Self,
    {
        match self {
            Validated::Valid(value) => Validated::Valid(value),
            Validated::Invalid(errors) => {
                // For Validated, we recover from the first error
                // This maintains the error accumulation semantics
                if let Some(first_error) = errors.into_iter().next() {
                    recovery(first_error)
                } else {
                    // Empty error case - should not happen in well-formed Validated
                    Validated::Invalid(smallvec![])
                }
            },
        }
    }

    fn bimap_result<B, F, SuccessF, ErrorF>(
        self, success_f: SuccessF, error_f: ErrorF,
    ) -> Result<B, F>
    where
        SuccessF: FnOnce(Self::Success) -> B,
        ErrorF: FnOnce(E) -> F,
        Self: Sized,
    {
        match self {
            Validated::Valid(value) => Ok(success_f(value)),
            Validated::Invalid(errors) => {
                let first_error = errors
                    .into_iter()
                    .next()
                    .expect("Validated::Invalid should contain at least one error");
                Err(error_f(first_error))
            },
        }
    }
}
