//! # Error Context Management and Functional Pipelines
//!
//! This module provides utilities for managing error context and creating
//! functional error handling pipelines. It includes context accumulation,
//! error transformation chains, and composable error handling patterns.

use crate::error::types::{BoxedComposableResult, ComposableError, IntoErrorContext};
use smallvec::SmallVec;
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
    C: Into<String>,
{
    ComposableError::new(error).with_context(context.into())
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
    C: Into<String>,
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
    C: Into<String> + Clone,
{
    move |error| with_context(error, context.clone())
}

/// A functional error handling pipeline builder.
///
/// `ErrorPipeline` allows you to build composable error handling chains
/// that can transform, contextualize, and recover from errors in a
/// functional style. Each operation returns a new pipeline that can
/// be further composed.
///
/// # Type Parameters
///
/// * `T`: The success type
/// * `E`: The current error type
///
/// # Examples
///
/// ```rust
/// use rustica::error::{ErrorPipeline, ComposableError};
///
/// let result: Result<i32, &str> = Err("parse error");
///
/// let processed = ErrorPipeline::new(result)
///     .with_context("Failed to process input")
///     .map_error(|e| format!("Error: {}", e))
///     .recover(|_| Ok(42))
///     .finish();
///
/// assert_eq!(processed, Ok(42));
/// ```
pub struct ErrorPipeline<T, E> {
    result: Result<T, E>,
    pending_contexts: SmallVec<[String; 4]>,
}

impl<T, E> ErrorPipeline<T, E> {
    /// Creates a new error pipeline from a Result.
    ///
    /// # Arguments
    ///
    /// * `result`: The initial Result to process
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::error::ErrorPipeline;
    ///
    /// let result: Result<i32, &str> = Ok(42);
    /// let pipeline = ErrorPipeline::new(result);
    /// ```
    #[inline]
    pub fn new(result: Result<T, E>) -> Self {
        Self {
            result,
            pending_contexts: SmallVec::new(),
        }
    }

    /// Adds context to errors in the pipeline.
    ///
    /// This buffers the context without transforming the error type,
    /// enabling efficient deep pipeline operations. Contexts are only
    /// applied when the pipeline is finished.
    ///
    /// # Arguments
    ///
    /// * `context`: The context to add
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::error::ErrorPipeline;
    ///
    /// let result: Result<i32, &str> = Err("failed");
    /// let pipeline = ErrorPipeline::new(result)
    ///     .with_context("Operation failed")
    ///     .with_context("Database error");
    /// ```
    #[inline]
    pub fn with_context<C>(mut self, context: C) -> Self
    where
        C: Into<String>,
    {
        self.pending_contexts.push(context.into());
        self
    }

    /// Maps the error type to a new type.
    ///
    /// This applies a transformation function to any error in the pipeline,
    /// allowing for error type conversions and transformations.
    ///
    /// # Type Parameters
    ///
    /// * `F`: The mapping function type
    /// * `NewE`: The new error type
    ///
    /// # Arguments
    ///
    /// * `f`: The function to apply to errors
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::error::ErrorPipeline;
    ///
    /// let result: Result<i32, i32> = Err(404);
    /// let pipeline = ErrorPipeline::new(result)
    ///     .map_error(|code| format!("HTTP Error: {}", code));
    /// ```
    #[inline]
    pub fn map_error<F, NewE>(self, f: F) -> ErrorPipeline<T, NewE>
    where
        F: FnOnce(E) -> NewE,
    {
        ErrorPipeline {
            result: self.result.map_err(f),
            pending_contexts: self.pending_contexts,
        }
    }

    /// Applies a recovery function to errors.
    ///
    /// This allows the pipeline to recover from errors by providing
    /// alternative values or alternative computations.
    ///
    /// # Type Parameters
    ///
    /// * `F`: The recovery function type
    ///
    /// # Arguments
    ///
    /// * `recovery`: The function to apply for error recovery
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::error::ErrorPipeline;
    ///
    /// let result: Result<i32, &str> = Err("failed");
    /// let pipeline = ErrorPipeline::new(result)
    ///     .recover(|_error| Ok(0)); // Provide default value
    /// ```
    #[inline]
    pub fn recover<F>(self, recovery: F) -> ErrorPipeline<T, E>
    where
        F: FnOnce(E) -> Result<T, E>,
    {
        ErrorPipeline {
            result: self.result.or_else(recovery),
            pending_contexts: self.pending_contexts,
        }
    }

    /// Chains another operation that might fail.
    ///
    /// This is similar to `Result::and_then`, allowing you to chain
    /// operations that might produce errors.
    ///
    /// # Type Parameters
    ///
    /// * `U`: The new success type
    /// * `F`: The chaining function type
    ///
    /// # Arguments
    ///
    /// * `f`: The function to apply to success values
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::error::ErrorPipeline;
    ///
    /// let result: Result<i32, &str> = Ok(42);
    /// let pipeline = ErrorPipeline::new(result)
    ///     .and_then(|x| if x > 0 { Ok(x * 2) } else { Err("negative") });
    /// ```
    #[inline]
    pub fn and_then<U, F>(self, f: F) -> ErrorPipeline<U, E>
    where
        F: FnOnce(T) -> Result<U, E>,
    {
        ErrorPipeline {
            result: self.result.and_then(f),
            pending_contexts: self.pending_contexts,
        }
    }

    /// Maps the success value to a new type.
    ///
    /// This applies a transformation function to any success value
    /// in the pipeline, leaving errors unchanged.
    ///
    /// # Type Parameters
    ///
    /// * `U`: The new success type
    /// * `F`: The mapping function type
    ///
    /// # Arguments
    ///
    /// * `f`: The function to apply to success values
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::error::ErrorPipeline;
    ///
    /// let result: Result<i32, &str> = Ok(42);
    /// let pipeline = ErrorPipeline::new(result)
    ///     .map(|x| x.to_string());
    /// ```
    #[inline]
    pub fn map<U, F>(self, f: F) -> ErrorPipeline<U, E>
    where
        F: FnOnce(T) -> U,
    {
        ErrorPipeline {
            result: self.result.map(f),
            pending_contexts: self.pending_contexts,
        }
    }

    /// Finishes the pipeline and returns the final result with applied contexts.
    ///
    /// This is the terminal operation of the pipeline that applies
    /// all buffered contexts to any error and returns the final Result.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::error::ErrorPipeline;
    ///
    /// let result: Result<i32, &str> = Ok(42);
    /// let final_result = ErrorPipeline::new(result)
    ///     .map(|x| x * 2)
    ///     .with_context("Processing data")
    ///     .finish();
    ///
    /// assert_eq!(final_result, Ok(84));
    /// ```
    #[inline]
    pub fn finish(self) -> BoxedComposableResult<T, E> {
        match self.result {
            Ok(v) => Ok(v),
            Err(e) => {
                let composable = ComposableError::new(e).with_contexts(self.pending_contexts);
                Err(Box::new(composable))
            },
        }
    }
}

/// Creates an error handling pipeline from a Result.
///
/// This is a convenience function that creates an `ErrorPipeline`
/// from a Result, enabling functional error handling patterns.
///
/// # Type Parameters
///
/// * `T`: The success type
/// * `E`: The error type
///
/// # Arguments
///
/// * `result`: The Result to create a pipeline from
///
/// # Examples
///
/// ```rust
/// use rustica::error::error_pipeline;
///
/// let result: Result<i32, &str> = Err("failed");
/// let processed = error_pipeline(result)
///     .with_context("Operation failed")
///     .recover(|_| Ok(0))
///     .finish();
///
/// assert_eq!(processed, Ok(0));
/// ```
#[inline]
pub fn error_pipeline<T, E>(result: Result<T, E>) -> ErrorPipeline<T, E> {
    ErrorPipeline::new(result)
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
        .map(|c| c.into_error_context().message().to_string())
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
