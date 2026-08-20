//! # Error Context Management and Functional Pipelines
//!
//! This module provides utilities for managing error context and creating
//! functional error handling pipelines. It includes context accumulation,
//! error transformation chains, and composable error handling patterns.

use crate::error::types::{BoxedComposableResult, ComposableError, IntoErrorContext};
use std::fmt::Display;

/// Adds context to any error type, creating a ComposableError.
///
/// This function provides a convenient way to add contextual information
/// to any error, wrapping it in a ComposableError structure that supports
/// context accumulation and error chaining.
///
/// # Type Parameters
///
/// * `E`: The original error type
/// * `C`: The context type (must implement IntoErrorContext)
///
/// # Arguments
///
/// * `error`: The error to add context to
/// * `context`: The context information to add
///
/// # Examples
///
/// ```rust
/// use rustica::error::with_context;
///
/// let io_error = std::io::Error::new(std::io::ErrorKind::NotFound, "file.txt");
/// let contextual_error = with_context(io_error, "Failed to load configuration");
///
/// assert!(contextual_error.context().len() > 0);
/// ```
#[inline]
pub fn with_context<E, C>(error: E, context: C) -> ComposableError<E>
where
    C: IntoErrorContext,
{
    ComposableError::new(error).with_context(context)
}

/// Adds context to a Result, converting errors to ComposableError.
///
/// This function transforms a `Result<T, E>` into a `Result<T, ComposableError<E>>`,
/// adding the specified context to any error that occurs. Success values pass
/// through unchanged.
///
/// # Type Parameters
///
/// * `T`: The success type
/// * `E`: The original error type
/// * `C`: The context type (must implement IntoErrorContext)
///
/// # Arguments
///
/// * `result`: The Result to add context to
/// * `context`: The context information to add
///
/// # Examples
///
/// ```rust
/// use rustica::error::with_context_result;
///
/// fn parse_number(s: &str) -> Result<i32, std::num::ParseIntError> {
///     s.parse()
/// }
///
/// let result = parse_number("not_a_number");
/// let contextual = with_context_result(result, "Failed to parse user input");
///
/// match contextual {
///     Ok(_) => panic!("Expected error"),
///     Err(composable) => {
///         assert_eq!(composable.context().len(), 1);
///         assert!(composable.context()[0].contains("Failed to parse user input"));
///     }
/// }
/// ```
#[inline]
pub fn with_context_result<T, E, C>(result: Result<T, E>, context: C) -> BoxedComposableResult<T, E>
where
    C: IntoErrorContext,
{
    result.map_err(|e| Box::new(with_context(e, context)))
}

/// Creates a context function that can be applied lazily.
///
/// This function returns a closure that, when called with an error,
/// adds the specified context. This is useful for creating reusable
/// context transformations and building error handling pipelines.
///
/// # Type Parameters
///
/// * `C`: The context type (must implement IntoErrorContext)
///
/// # Arguments
///
/// * `context`: The context information to add
///
/// # Examples
///
/// ```rust
/// use rustica::error::context_fn;
///
/// let add_db_context = context_fn("Database operation failed");
///
/// let error = "Connection refused";
/// let contextual_error = add_db_context(error);
///
/// assert_eq!(contextual_error.context().len(), 1);
/// assert!(contextual_error.context()[0].contains("Database operation failed"));
/// ```
#[inline]
pub fn context_fn<E, C>(context: C) -> impl Fn(E) -> ComposableError<E>
where
    C: IntoErrorContext + Clone,
{
    move |error| with_context(error, context.clone())
}

/// Accumulates context from multiple sources into a single error.
///
/// This function takes an error and multiple context sources,
/// creating a ComposableError with all context information
/// accumulated in order.
///
/// # Type Parameters
///
/// * `E`: The error type
/// * `I`: The iterator type for contexts
/// * `C`: The context item type
///
/// # Arguments
///
/// * `error`: The base error
/// * `contexts`: An iterator of context information
///
/// # Examples
///
/// ```rust
/// use rustica::error::accumulate_context;
///
/// let error = "core error";
/// let contexts = vec!["step 1 failed", "step 2 failed", "operation failed"];
/// let accumulated = accumulate_context(error, contexts);
///
/// assert_eq!(accumulated.context().len(), 3);
/// ```
pub fn accumulate_context<E, I, C>(error: E, contexts: I) -> ComposableError<E>
where
    I: IntoIterator<Item = C>,
    C: IntoErrorContext,
{
    let context_strings: Vec<String> = contexts
        .into_iter()
        .map(|c| c.into_error_context().into_message())
        .collect();

    ComposableError::new(error).with_contexts(context_strings)
}

/// Creates a context accumulator function.
///
/// This returns a function that can accumulate multiple contexts
/// onto an error. The returned function can be reused for multiple
/// errors with the same context pattern.
///
/// # Type Parameters
///
/// * `I`: The iterator type for contexts
/// * `C`: The context item type
///
/// # Arguments
///
/// * `contexts`: The contexts to accumulate
///
/// # Examples
///
/// ```rust
/// use rustica::error::context_accumulator;
///
/// let contexts = vec!["database error", "user operation failed"];
/// let accumulator = context_accumulator(contexts);
///
/// let error1 = "connection timeout";
/// let error2 = "query failed";
///
/// let contextual1 = accumulator(error1);
/// let contextual2 = accumulator(error2);
///
/// // Both errors now have the same context stack
/// assert_eq!(contextual1.context().len(), 2);
/// assert_eq!(contextual2.context().len(), 2);
/// ```
pub fn context_accumulator<E, I, C>(contexts: I) -> impl Fn(E) -> ComposableError<E>
where
    I: IntoIterator<Item = C> + Clone,
    C: IntoErrorContext + Clone,
{
    move |error| accumulate_context(error, contexts.clone())
}

/// Formats an error with its full context chain.
///
/// This function creates a human-readable string representation
/// of an error and all its context information, formatted as
/// a chain from most recent context to core error.
///
/// # Type Parameters
///
/// * `E`: The error type (must implement Display)
///
/// # Arguments
///
/// * `error`: The ComposableError to format
///
/// # Examples
///
/// ```rust
/// use rustica::error::{ComposableError, format_error_chain};
///
/// let error = ComposableError::new("file not found")
///     .with_context("failed to load config".to_string())
///     .with_context("application startup failed".to_string());
///
/// let formatted = format_error_chain(&error);
/// assert!(formatted.contains("application startup failed"));
/// assert!(formatted.contains("failed to load config"));
/// assert!(formatted.contains("file not found"));
/// ```
pub fn format_error_chain<E>(error: &ComposableError<E>) -> String
where
    E: Display,
{
    error.error_chain()
}

/// Extracts all context information from a ComposableError.
///
/// This function returns a vector of all context strings in the
/// order they were added (most recent first).
///
/// # Type Parameters
///
/// * `E`: The error type
///
/// # Arguments
///
/// * `error`: The ComposableError to extract context from
///
/// # Examples
///
/// ```rust
/// use rustica::error::{ComposableError, extract_context};
///
/// let error = ComposableError::new("error")
///     .with_context("context 1".to_string())
///     .with_context("context 2".to_string());
///
/// let contexts = extract_context(&error);
/// assert_eq!(contexts.len(), 2);
/// assert_eq!(contexts[0], "context 2"); // Most recent first
/// assert_eq!(contexts[1], "context 1");
/// ```
pub fn extract_context<E>(error: &ComposableError<E>) -> Vec<String> {
    error.context()
}
