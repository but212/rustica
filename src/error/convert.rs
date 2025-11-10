//! # Error Type Conversion Utilities
//!
//! This module provides conversion functions between different error handling types,
//! enabling seamless interoperability between Result, Either, Validated, and
//! ComposableError types while preserving categorical properties.

use crate::datatypes::either::Either;
use crate::datatypes::validated::Validated;
use crate::error::types::{BoxedComposableResult, ComposableError};

/// Converts an `Either<E, T>` to a `Result<T, E>`.
///
/// This is a lossless conversion that maps `Either::Left(e)` to `Err(e)`
/// and `Either::Right(t)` to `Ok(t)`.
///
/// # Type Parameters
///
/// * `T`: The success type
/// * `E`: The error type
///
/// # Arguments
///
/// * `either`: The Either value to convert
///
/// # Examples
///
/// ```rust
/// use rustica::error::either_to_result;
/// use rustica::datatypes::either::Either;
///
/// let success: Either<String, i32> = Either::Right(42);
/// assert_eq!(either_to_result(success), Ok(42));
///
/// let error: Either<String, i32> = Either::Left("failed".to_string());
/// assert_eq!(either_to_result(error), Err("failed".to_string()));
/// ```
#[inline]
pub fn either_to_result<T, E>(either: Either<E, T>) -> Result<T, E> {
    match either {
        Either::Left(error) => Err(error),
        Either::Right(value) => Ok(value),
    }
}

/// Converts a `Result<T, E>` to an `Either<E, T>`.
///
/// This is a lossless conversion that maps `Err(e)` to `Either::Left(e)`
/// and `Ok(t)` to `Either::Right(t)`.
///
/// # Type Parameters
///
/// * `T`: The success type
/// * `E`: The error type
///
/// # Arguments
///
/// * `result`: The Result value to convert
///
/// # Examples
///
/// ```rust
/// use rustica::error::result_to_either;
/// use rustica::datatypes::either::Either;
///
/// let success: Result<i32, String> = Ok(42);
/// assert_eq!(result_to_either(success), Either::Right(42));
///
/// let error: Result<i32, String> = Err("failed".to_string());
/// assert_eq!(result_to_either(error), Either::Left("failed".to_string()));
/// ```
#[inline]
pub fn result_to_either<T, E>(result: Result<T, E>) -> Either<E, T> {
    match result {
        Ok(value) => Either::Right(value),
        Err(error) => Either::Left(error),
    }
}

/// Converts a `Validated<E, T>` to a `Result<T, E>`.
///
/// This conversion takes the first error from the Validated if it's invalid,
/// or returns the success value if valid. Note that this is a lossy conversion
/// when multiple errors are present, as Result can only hold one error.
///
/// # Type Parameters
///
/// * `T`: The success type
/// * `E`: The error type
///
/// # Arguments
///
/// * `validated`: The Validated value to convert
///
/// # Examples
///
/// ```rust
/// use rustica::error::validated_to_result;
/// use rustica::datatypes::validated::Validated;
///
/// let valid: Validated<String, i32> = Validated::valid(42);
/// assert_eq!(validated_to_result(valid), Ok(42));
///
/// let invalid: Validated<String, i32> = Validated::invalid("error".to_string());
/// assert_eq!(validated_to_result(invalid), Err("error".to_string()));
/// ```
#[inline]
pub fn validated_to_result<T, E>(validated: Validated<E, T>) -> Result<T, E>
where
    E: Clone,
{
    match validated {
        Validated::Valid(value) => Ok(value),
        Validated::Invalid(errors) => {
            // Take the first error, or create a default if somehow empty
            Err(errors
                .into_iter()
                .next()
                .expect("Validated::Invalid should contain at least one error"))
        },
    }
}

/// Converts a `Result<T, E>` to a `Validated<E, T>`.
///
/// This is a lossless conversion that maps `Ok(t)` to `Validated::Valid(t)`
/// and `Err(e)` to `Validated::Invalid` containing a single error.
///
/// # Type Parameters
///
/// * `T`: The success type
/// * `E`: The error type
///
/// # Arguments
///
/// * `result`: The Result value to convert
///
/// # Examples
///
/// ```rust
/// use rustica::error::result_to_validated;
/// use rustica::datatypes::validated::Validated;
///
/// let success: Result<i32, String> = Ok(42);
/// assert_eq!(result_to_validated(success), Validated::valid(42));
///
/// let error: Result<i32, String> = Err("failed".to_string());
/// let validated = result_to_validated(error);
/// assert!(validated.is_invalid());
/// assert_eq!(validated.errors().len(), 1);
/// ```
#[inline]
pub fn result_to_validated<T, E>(result: Result<T, E>) -> Validated<E, T>
where
    E: Clone,
    T: Clone,
{
    match result {
        Ok(value) => Validated::Valid(value),
        Err(error) => Validated::invalid(error),
    }
}

/// Converts an `Either<E, T>` to a `Validated<E, T>`.
///
/// This is a lossless conversion that maps `Either::Right(t)` to `Validated::Valid(t)`
/// and `Either::Left(e)` to `Validated::Invalid` containing a single error.
///
/// # Type Parameters
///
/// * `T`: The success type
/// * `E`: The error type
///
/// # Arguments
///
/// * `either`: The Either value to convert
///
/// # Examples
///
/// ```rust
/// use rustica::error::either_to_validated;
/// use rustica::datatypes::either::Either;
/// use rustica::datatypes::validated::Validated;
///
/// let success: Either<String, i32> = Either::Right(42);
/// assert_eq!(either_to_validated(success), Validated::valid(42));
///
/// let error: Either<String, i32> = Either::Left("failed".to_string());
/// let validated = either_to_validated(error);
/// assert!(validated.is_invalid());
/// ```
#[inline]
pub fn either_to_validated<T, E>(either: Either<E, T>) -> Validated<E, T>
where
    E: Clone,
    T: Clone,
{
    match either {
        Either::Right(value) => Validated::Valid(value),
        Either::Left(error) => Validated::invalid(error),
    }
}

/// Converts a `Validated<E, T>` to an `Either<E, T>`.
///
/// This conversion takes the first error from the Validated if it's invalid,
/// or returns the success value if valid. This is a lossy conversion when
/// multiple errors are present.
///
/// # Type Parameters
///
/// * `T`: The success type
/// * `E`: The error type
///
/// # Arguments
///
/// * `validated`: The Validated value to convert
///
/// # Examples
///
/// ```rust
/// use rustica::error::validated_to_either;
/// use rustica::datatypes::validated::Validated;
/// use rustica::datatypes::either::Either;
///
/// let valid: Validated<String, i32> = Validated::valid(42);
/// assert_eq!(validated_to_either(valid), Either::Right(42));
///
/// let invalid: Validated<String, i32> = Validated::invalid("error".to_string());
/// assert_eq!(validated_to_either(invalid), Either::Left("error".to_string()));
/// ```
#[inline]
pub fn validated_to_either<T, E>(validated: Validated<E, T>) -> Either<E, T>
where
    E: Clone,
{
    match validated {
        Validated::Valid(value) => Either::Right(value),
        Validated::Invalid(errors) => Either::Left(
            errors
                .into_iter()
                .next()
                .expect("Validated::Invalid should contain at least one error"),
        ),
    }
}

/// Converts a `ComposableError<E>` to a regular error type `E`.
///
/// This extracts the core error from a ComposableError, discarding all
/// context information. Use this when you need to interface with APIs
/// that expect the raw error type.
///
/// # Type Parameters
///
/// * `E`: The core error type
///
/// # Arguments
///
/// * `composable`: The ComposableError to extract from
///
/// # Examples
///
/// ```rust
/// use rustica::error::{ComposableError, composable_to_core};
///
/// let error = ComposableError::new("core error")
///     .with_context("additional context".to_string());
///
/// assert_eq!(composable_to_core(error), "core error");
/// ```
#[inline]
pub fn composable_to_core<E>(composable: ComposableError<E>) -> E {
    composable.core_error
}

/// Converts a regular error type `E` to a `ComposableError<E>`.
///
/// This wraps a simple error in a ComposableError structure, allowing
/// for future context addition and error composition.
///
/// # Type Parameters
///
/// * `E`: The core error type
///
/// # Arguments
///
/// * `error`: The error to wrap
///
/// # Examples
///
/// ```rust
/// use rustica::error::{ComposableError, core_to_composable};
///
/// let simple_error = "file not found";
/// let composable = core_to_composable(simple_error);
///
/// assert_eq!(composable.core_error(), &"file not found");
/// assert!(composable.context().is_empty());
/// ```
#[inline]
pub fn core_to_composable<E>(error: E) -> ComposableError<E> {
    ComposableError::new(error)
}

/// Converts a `Result<T, ComposableError<E>>` to a `Result<T, E>`.
///
/// This extracts the core error from a ComposableError within a Result,
/// effectively "flattening" the error structure. Context information is lost.
///
/// # Type Parameters
///
/// * `T`: The success type
/// * `E`: The core error type
///
/// # Arguments
///
/// * `result`: The Result with ComposableError to flatten
///
/// # Examples
///
/// ```rust
/// use rustica::error::{ComposableError, flatten_composable_result};
///
/// let error = ComposableError::new("core issue")
///     .with_context("operation failed".to_string());
/// let result: Result<i32, ComposableError<&str>> = Err(error);
///
/// let flattened = flatten_composable_result(result);
/// assert_eq!(flattened, Err("core issue"));
/// ```
#[inline]
pub fn flatten_composable_result<T, E>(result: Result<T, ComposableError<E>>) -> Result<T, E> {
    result.map_err(composable_to_core)
}

/// Converts a `Result<T, E>` to a `Result<T, ComposableError<E>>`.
///
/// This wraps the error in a ComposableError structure, enabling future
/// context addition and error composition.
///
/// # Type Parameters
///
/// * `T`: The success type
/// * `E`: The core error type
///
/// # Arguments
///
/// * `result`: The Result to wrap
///
/// # Examples
///
/// ```rust
/// use rustica::error::{ComposableError, wrap_in_composable_result};
///
/// let result: Result<i32, &str> = Err("simple error");
/// let wrapped = wrap_in_composable_result(result);
///
/// match wrapped {
///     Ok(_) => panic!("Expected error"),
///     Err(composable) => {
///         assert_eq!(composable.core_error(), &"simple error");
///         assert!(composable.context().is_empty());
///     }
/// }
/// ```
#[inline]
#[allow(clippy::result_large_err)]
pub fn wrap_in_composable_result<T, E>(result: Result<T, E>) -> Result<T, ComposableError<E>> {
    result.map_err(core_to_composable)
}

/// Converts a `Result<T, E>` to a `BoxedComposableResult<T, E>`.
///
/// This is similar to `wrap_in_composable_result` but returns a boxed
/// ComposableError to avoid clippy warnings about large error types.
///
/// # Type Parameters
///
/// * `T`: The success type
/// * `E`: The core error type
///
/// # Arguments
///
/// * `result`: The Result to wrap
///
/// # Examples
///
/// ```rust
/// use rustica::error::{ComposableError, wrap_in_composable_result_boxed};
///
/// let result: Result<i32, &str> = Err("simple error");
/// let wrapped = wrap_in_composable_result_boxed(result);
///
/// match wrapped {
///     Ok(_) => panic!("Expected error"),
///     Err(boxed_composable) => {
///         assert_eq!(boxed_composable.core_error(), &"simple error");
///         assert!(boxed_composable.context().is_empty());
///     }
/// }
/// ```
#[inline]
pub fn wrap_in_composable_result_boxed<T, E>(result: Result<T, E>) -> BoxedComposableResult<T, E> {
    result.map_err(|e| Box::new(core_to_composable(e)))
}

/// Converts multiple errors into a single `Validated` containing all errors.
///
/// This function takes an iterator of errors and creates a `Validated::Invalid`
/// containing all of them. This is useful for collecting errors from multiple
/// validation steps.
///
/// # Type Parameters
///
/// * `E`: The error type
/// * `I`: The iterator type
///
/// # Arguments
///
/// * `errors`: An iterator of errors to collect
///
/// # Examples
///
/// ```rust
/// use rustica::error::collect_errors;
/// use rustica::datatypes::validated::Validated;
///
/// let errors = vec!["error1", "error2", "error3"];
/// let validated: Validated<&str, ()> = collect_errors(errors);
///
/// assert!(validated.is_invalid());
/// assert_eq!(validated.errors().len(), 3);
/// ```
#[inline]
pub fn collect_errors<E, I>(errors: I) -> Validated<E, ()>
where
    E: Clone,
    I: IntoIterator<Item = E>,
{
    let error_vec: Vec<E> = errors.into_iter().collect();
    if error_vec.is_empty() {
        Validated::Valid(())
    } else {
        Validated::invalid_many(error_vec)
    }
}

/// Splits a `Validated` with multiple errors into separate `Result`s.
///
/// This function takes a `Validated` and returns a vector of `Result`s,
/// where each error becomes a separate `Err` result. If the `Validated`
/// is valid, returns a single `Ok` result.
///
/// # Type Parameters
///
/// * `T`: The success type
/// * `E`: The error type
///
/// # Arguments
///
/// * `validated`: The Validated to split
///
/// # Examples
///
/// ```rust
/// use rustica::error::split_validated_errors;
/// use rustica::datatypes::validated::Validated;
///
/// let invalid: Validated<String, i32> = Validated::invalid_many(vec![
///     "error1".to_string(),
///     "error2".to_string()
/// ]);
///
/// let results = split_validated_errors(invalid);
/// assert_eq!(results.len(), 2);
/// assert!(results[0].is_err());
/// assert!(results[1].is_err());
/// ```
pub fn split_validated_errors<T, E>(validated: Validated<E, T>) -> Vec<Result<T, E>>
where
    T: Clone,
    E: Clone,
{
    match validated {
        Validated::Valid(value) => vec![Ok(value)],
        Validated::Invalid(errors) => errors.into_iter().map(|e| Err(e)).collect(),
    }
}
