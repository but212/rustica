//! # Error Handling Utilities
//!
//! This module provides standardized error handling utilities for working with
//! functional programming patterns in Rust. It builds upon the abstractions in
//! the rest of the library, particularly focusing on error handling.
//!
//! ## Key Features
//!
//! - **Error Transformation**: Convert between different error representations
//! - **Error Collection**: Accumulate all errors or short-circuit on first error
//! - **Standardized Error Interface**: The `WithError` trait provides a unified
//!   approach to handling errors
//! - **Custom Error Types**: Create application-specific error types with context
//!
//! ## Categories of Utilities
//!
//! - **Core Error Traits**: `WithError` trait and its implementations
//! - **Sequence/Traverse Functions**: Collect and transform collections of fallible operations
//! - **Error Type Conversions**: Convert between `Result`, `Either`, and `Validated`
//! - **Chainable Error Handling**: Extension methods for smoother error handling
//! - **Custom Error Types**: Tools for creating application-specific errors
//!
//! ## Getting Started
//!
//! The most commonly used functions in this module are:
//!
//! - `sequence`: Convert a collection of `Result`s into a `Result` of collection
//! - `traverse`: Apply a fallible function to every element in a collection
//! - `traverse_validated`: Apply a fallible function and collect all errors
//! - `error_with_context`: Create contextualized error messages
//!
//! ## Deprecation Notice
//!
//! Error conversion helpers are now provided by [`crate::error`] for better
//! discoverability. The legacy helpers in this module forward to the new
//! implementations and are marked as deprecated.

use crate::datatypes::either::Either;
use crate::datatypes::validated::Validated;
use crate::prelude::HKT;
use smallvec::SmallVec;

// ===== Core Error Traits =====

/// Error handling trait for types that can fail with a specific error type.
///
/// This trait provides a common interface for working with different error handling
/// types such as `Result`, `Either`, and `Validated`. It defines methods for
/// transforming errors and converting to standard Rust `Result` types.
///
/// # Type Parameters
///
/// * `E`: The error type that can occur in the fallible computation
///
/// # Examples
///
/// Using `WithError` with `Result`:
///
/// ```rust
/// use rustica::utils::error_utils::WithError;
/// use std::io;
///
/// // Define a function that works with any type implementing WithError
/// fn log_and_transform_error<T, E>(value: T) -> T::ErrorOutput<String>
/// where
///     T: WithError<E>,
///     E: std::fmt::Display + Clone,
/// {
///     value.fmap_error(|e| format!("Error occurred: {}", e))
/// }
///
/// // Use with a Result
/// let result: Result<i32, String> = Err("file not found".to_string());
/// let transformed = log_and_transform_error(result);
/// assert!(transformed.is_err());
/// ```
pub trait WithError<E>: HKT {
    /// The successful value type
    type Success;

    /// The output type when mapping the error to a new type
    type ErrorOutput<G>;

    /// Maps a function over the error, transforming the error type.
    ///
    /// This is similar to `map_err` for `Result`, but generalized to work with
    /// any error handling type.
    ///
    /// # Type Parameters
    ///
    /// * `F`: Function type that transforms error `E` to error `G`
    /// * `G`: The new error type after transformation
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::utils::error_utils::WithError;
    ///
    /// let result: Result<i32, &str> = Err("not found");
    /// let transformed = result.fmap_error(|e| format!("Error: {}", e));
    /// assert_eq!(transformed, Err("Error: not found".to_string()));
    /// ```
    fn fmap_error<F, G>(self, f: F) -> Self::ErrorOutput<G>
    where
        F: Fn(E) -> G,
        G: Clone;

    /// Converts this type to a Result.
    ///
    /// This provides a way to standardize error handling by converting any
    /// error handling type to a Rust `Result`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::utils::error_utils::WithError;
    /// use rustica::datatypes::either::Either;
    ///
    /// let either: Either<&str, i32> = Either::left("error");
    /// let result = either.to_result();
    /// assert_eq!(result, Err("error"));
    /// ```
    fn to_result(self) -> Result<Self::Success, E>;
}

impl<T, E: Clone> WithError<E> for Result<T, E> {
    type Success = T;
    type ErrorOutput<G> = Result<T, G>;

    fn fmap_error<F, G>(self, f: F) -> Self::ErrorOutput<G>
    where
        F: FnOnce(E) -> G,
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

impl<T, E> WithError<E> for Either<E, T> {
    type Success = T;
    type ErrorOutput<G> = Either<G, T>;

    fn fmap_error<F, G>(self, f: F) -> Self::ErrorOutput<G>
    where
        F: FnOnce(E) -> G,
    {
        match self {
            Either::Left(e) => Either::Left(f(e)),
            Either::Right(t) => Either::Right(t),
        }
    }

    fn to_result(self) -> Result<Self::Success, E> {
        match self {
            Either::Left(e) => Err(e),
            Either::Right(t) => Ok(t),
        }
    }
}

impl<T: Clone, E: Clone> WithError<E> for Validated<E, T> {
    type Success = T;
    type ErrorOutput<G> = Validated<G, T>;

    fn fmap_error<F, G>(self, f: F) -> Self::ErrorOutput<G>
    where
        F: Fn(E) -> G,
        G: Clone,
        T: Clone,
    {
        match self {
            Validated::Valid(t) => Validated::Valid(t),
            Validated::Invalid(e) => Validated::Invalid(e.into_iter().map(f).collect()),
        }
    }

    fn to_result(self) -> Result<Self::Success, E> {
        match self {
            Validated::Valid(t) => Ok(t),
            Validated::Invalid(e) => Err(e.into_iter().next().unwrap()),
        }
    }
}

// ===== Sequence and Traverse Functions =====

/// Specialization of `sequence_result` for standardizing error handling.
///
/// This function converts a collection of results into a result containing
/// a collection of values, short-circuiting on the first error encountered.
///
/// # Type Parameters
///
/// * `A`: The success type in the Result
/// * `E`: The error type in the Result
///
/// # Examples
///
/// ```rust
/// use rustica::utils::error_utils::sequence;
///
/// // All results are Ok, so the final result is Ok containing all values
/// let results: Vec<Result<i32, &str>> = vec![Ok(1), Ok(2), Ok(3)];
/// assert_eq!(sequence(results), Ok(vec![1, 2, 3]));
///
/// // One result is Err, so the final result is Err containing that error
/// let results: Vec<Result<i32, &str>> = vec![Ok(1), Err("error"), Ok(3)];
/// assert_eq!(sequence(results), Err("error"));
///
/// // Empty collection gives an empty success collection
/// let empty_results: Vec<Result<i32, &str>> = vec![];
/// assert_eq!(sequence(empty_results), Ok(vec![]));
/// ```
#[inline]
pub fn sequence<A, E>(collection: Vec<Result<A, E>>) -> Result<Vec<A>, E> {
    sequence_result(collection)
}

/// Specialization of `traverse_result` for standardizing error handling.
///
/// This function applies a function that might fail to each element of a collection,
/// collecting the results if everything succeeds, or returning the first error.
///
/// # Type Parameters
///
/// * `A`: The input item type
/// * `B`: The success type in the Result
/// * `E`: The error type in the Result
/// * `F`: The transformation function type
///
/// # Examples
///
/// ```rust
/// use rustica::utils::error_utils::traverse;
///
/// // Define a fallible parsing function with explicit error type
/// let parse_int = |s: &str| s.parse::<i32>().map_err(|_| "parse error");
///
/// // When all inputs are valid, returns a collection of successful results
/// let inputs: Vec<&str> = vec!["1", "2", "3"];
/// let result: Result<Vec<i32>, &str> = traverse(inputs, parse_int);
/// assert_eq!(result, Ok(vec![1, 2, 3]));
///
/// // When any input is invalid, returns the first error
/// let inputs: Vec<&str> = vec!["1", "not_a_number", "3"];
/// let result: Result<Vec<i32>, &str> = traverse(inputs, parse_int);
/// assert_eq!(result, Err("parse error"));
///
/// // Empty collection gives an empty success collection
/// let empty_inputs: Vec<&str> = vec![];
/// let result: Result<Vec<i32>, &str> = traverse(empty_inputs, parse_int);
/// assert_eq!(result, Ok(vec![]));
/// ```
#[inline]
pub fn traverse<A, B, E, F>(collection: impl IntoIterator<Item = A>, f: F) -> Result<Vec<B>, E>
where
    F: FnMut(A) -> Result<B, E>,
{
    traverse_result(collection, f)
}

/// Applies a function that might fail to each element, collecting all errors.
///
/// Unlike `traverse`, this continues processing even after encountering errors,
/// collecting all errors that occur throughout the entire collection.
///
/// # Type Parameters
///
/// * `A`: The input item type
/// * `B`: The success type in the Validated
/// * `E`: The error type in the Validated
/// * `F`: The transformation function type
///
/// # Examples
///
/// ```rust
/// use rustica::utils::error_utils::traverse_validated;
/// use rustica::datatypes::validated::Validated;
///
/// // Define a fallible parsing function
/// let parse_int = |s: &str| -> Result<i32, String> {
///     s.parse::<i32>().map_err(|_| format!("'{}' is not a valid number", s))
/// };
///
/// // Process a collection with multiple errors
/// let inputs: Vec<&str> = vec!["1", "not_a_number", "3", "also_not_a_number"];
/// let result: Validated<String, Vec<i32>> = traverse_validated(inputs, parse_int);
///
/// // Verify that the result is invalid and contains the expected number of errors
/// assert!(result.is_invalid());
/// assert_eq!(result.errors().len(), 2);
/// assert!(result.errors()[0].contains("not_a_number"));
/// assert!(result.errors()[1].contains("also_not_a_number"));
///
/// // Process a collection with no errors
/// let valid_inputs: Vec<&str> = vec!["1", "2", "3"];
/// let valid_result: Validated<String, Vec<i32>> = traverse_validated(valid_inputs, parse_int);
/// assert!(valid_result.is_valid());
/// assert_eq!(valid_result.unwrap(), vec![1, 2, 3]);
///
pub fn traverse_validated<A, B, E, F>(
    collection: impl IntoIterator<Item = A>, mut f: F,
) -> Validated<E, Vec<B>>
where
    F: FnMut(A) -> Result<B, E>,
    E: Clone,
{
    let mut values = Vec::new();
    let mut errors = SmallVec::<[E; 8]>::new();
    let mut had_error = false;

    for item in collection {
        match f(item) {
            Ok(value) => values.push(value),
            Err(error) => {
                had_error = true;
                errors.push(error);
            },
        }
    }

    if had_error {
        Validated::Invalid(errors)
    } else {
        Validated::Valid(values)
    }
}

/// Converts a collection of `WithError` values into a Result.
///
/// This function generalizes the `sequence` function to work with any type
/// that implements the `WithError` trait, not just `Result`.
///
/// # Type Parameters
///
/// * `C`: The container type that implements `WithError`
/// * `T`: The success type
/// * `E`: The error type
///
/// # Examples
///
/// ```rust
/// use rustica::utils::error_utils::{sequence_with_error, WithError};
/// use rustica::datatypes::either::Either;
///
/// // Create a collection of Either values (all successful)
/// let results: Vec<Either<&str, i32>> = vec![
///     Either::right(1),
///     Either::right(2),
///     Either::right(3),
/// ];
/// assert_eq!(sequence_with_error(results), Ok(vec![1, 2, 3]));
///
/// // Create a collection of Either values (with one failure)
/// let results: Vec<Either<&str, i32>> = vec![
///     Either::right(1),
///     Either::left("error"),
///     Either::right(3),
/// ];
/// assert_eq!(sequence_with_error::<Either<&str, i32>, i32, &str>(results), Err("error"));
/// ```
#[inline]
pub fn sequence_with_error<C, T, E>(collection: Vec<C>) -> Result<Vec<T>, E>
where
    C: WithError<E>,
    C::Success: Clone + Into<T>,
    E: Clone,
{
    let mut values = Vec::with_capacity(collection.len());

    for item in collection {
        match item.to_result() {
            Ok(value) => values.push(value.into()),
            Err(error) => return Err(error),
        }
    }

    Ok(values)
}

// ===== Chainable Error Handling =====

/// A chainable error handling extension trait.
///
/// This trait adds convenient methods to Result for more ergonomic error
/// handling patterns. It provides conversions to other error handling
/// types and additional utility methods.
///
/// # Examples
///
/// ```rust
/// use rustica::utils::error_utils::ResultExt;
/// use rustica::datatypes::either::Either;
///
/// // Convert a Result to an Either
/// let result: Result<i32, &str> = Ok(42);
/// let either: Either<&str, i32> = result.to_either();
/// assert_eq!(either, Either::right(42));
///
/// // Use unwrap_or_default with a specific error type
/// let result: Result<String, i32> = Err(404);
/// let default_value: String = result.unwrap_or_default();
/// assert_eq!(default_value, String::default());
///
/// // Transform both success and error types
/// let result: Result<i32, &str> = Ok(10);
/// let transformed: Result<String, usize> = result.bimap(
///     |v| v.to_string(),      // Success mapper
///     |e| e.len(),            // Error mapper
/// );
/// assert_eq!(transformed, Ok("10".to_string()));
/// ```
pub trait ResultExt<T, E> {
    /// Converts a Result to a Validated.
    #[deprecated(note = "Use `crate::error::result_to_validated` instead")]
    fn to_validated(self) -> Validated<E, T>;

    /// Converts a Result to an Either.
    #[deprecated(note = "Use `crate::error::result_to_either` instead")]
    fn to_either(self) -> Either<E, T>;

    /// Returns the contained value or the default for type T.
    fn unwrap_or_default(self) -> T
    where
        T: Default;

    /// Maps both the success and error types.
    #[deprecated(note = "Use `crate::error::ErrorOps::bimap_result` instead")]
    fn bimap<F, G, U, E2>(self, success_map: F, error_map: G) -> Result<U, E2>
    where
        F: FnOnce(T) -> U,
        G: FnOnce(E) -> E2;
}

impl<T, E> ResultExt<T, E> for Result<T, E> {
    fn to_validated(self) -> Validated<E, T> {
        use smallvec::smallvec;
        match self {
            Ok(value) => Validated::Valid(value),
            Err(error) => Validated::Invalid(smallvec![error]),
        }
    }

    fn to_either(self) -> Either<E, T> {
        crate::error::result_to_either(self)
    }

    fn unwrap_or_default(self) -> T
    where
        T: Default,
    {
        self.unwrap_or_else(|_| T::default())
    }

    fn bimap<F, G, U, E2>(self, success_map: F, error_map: G) -> Result<U, E2>
    where
        F: FnOnce(T) -> U,
        G: FnOnce(E) -> E2,
    {
        match self {
            Ok(value) => Ok(success_map(value)),
            Err(error) => Err(error_map(error)),
        }
    }
}

// ===== Private Implementation Functions =====

// Sequence implementation for Result
#[inline]
fn sequence_result<A, E>(collection: Vec<Result<A, E>>) -> Result<Vec<A>, E> {
    let mut values = Vec::with_capacity(collection.len());

    for item in collection {
        match item {
            Ok(value) => values.push(value),
            Err(error) => return Err(error),
        }
    }

    Ok(values)
}
// Traverse implementation for Result
#[inline]
fn traverse_result<A, B, E, F>(
    collection: impl IntoIterator<Item = A>, mut f: F,
) -> Result<Vec<B>, E>
where
    F: FnMut(A) -> Result<B, E>,
{
    let mut values = Vec::new();

    for item in collection {
        match f(item) {
            Ok(value) => values.push(value),
            Err(error) => return Err(error),
        }
    }

    Ok(values)
}
