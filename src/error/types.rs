//! # Composable Error Types
//!
//! This module provides composable error structures that support context accumulation,
//! error chaining, and functional composition patterns. The types are designed to be
//! efficient for common error handling scenarios.

use smallvec::SmallVec;
use std::fmt::{Debug, Display};

/// A composable error type that supports context accumulation and error chaining.
///
/// `ComposableError<E>` wraps a core error of type `E` and provides additional
/// context information through a stack of context strings. This allows for
/// rich error reporting while maintaining performance through `SmallVec` optimization.
///
/// # Type Parameters
///
/// * `E`: The core error type
///
/// # Examples
///
/// ```rust
/// use rustica::error::ComposableError;
///
/// // Create a simple error
/// let error = ComposableError::new("File not found");
/// assert_eq!(error.core_error(), &"File not found");
/// assert!(error.context().is_empty());
///
/// // Add context
/// let error_with_context = error
///     .with_context("Failed to load configuration".to_string())
///     .with_context("Application startup failed".to_string());
///
/// assert_eq!(error_with_context.context().len(), 2);
/// ```
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ComposableError<E> {
    /// The core error that represents the root cause
    pub core_error: E,
    /// A stack of context information, stored in reverse order (oldest first)
    /// Public API presents them with most recent first
    context: SmallVec<[String; 2]>,
    /// Optional error code for programmatic error handling
    pub error_code: Option<u32>,
}

impl<E> ComposableError<E> {
    /// Creates a new `ComposableError` with just the core error.
    ///
    /// # Arguments
    ///
    /// * `error`: The core error to wrap
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::error::ComposableError;
    ///
    /// let error = ComposableError::new("Database connection failed");
    /// assert_eq!(error.core_error(), &"Database connection failed");
    /// assert!(error.context().is_empty());
    /// ```
    #[inline]
    pub fn new(error: E) -> Self {
        Self {
            core_error: error,
            context: SmallVec::new(),
            error_code: None,
        }
    }

    /// Creates a new `ComposableError` with a core error and error code.
    ///
    /// # Arguments
    ///
    /// * `error`: The core error to wrap
    /// * `code`: The error code for programmatic handling
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::error::ComposableError;
    ///
    /// let error = ComposableError::with_code("Not found", 404);
    /// assert_eq!(error.core_error(), &"Not found");
    /// assert_eq!(error.error_code(), Some(404));
    /// ```
    #[inline]
    pub fn with_code(error: E, code: u32) -> Self {
        Self {
            core_error: error,
            context: SmallVec::new(),
            error_code: Some(code),
        }
    }

    /// Adds context information to the error.
    ///
    /// This is an O(1) operation that appends context to the internal storage.
    /// The public API presents contexts with most recent first.
    ///
    /// # Arguments
    ///
    /// * `ctx`: The context to add (can be String, &str, or LazyContext)
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::error::ComposableError;
    ///
    /// let error = ComposableError::new("Connection refused")
    ///     .with_context("Failed to connect to database")
    ///     .with_context("User authentication failed".to_string());
    ///
    /// let contexts = error.context();
    /// assert_eq!(contexts[0], "User authentication failed");
    /// assert_eq!(contexts[1], "Failed to connect to database");
    /// ```
    #[inline]
    pub fn with_context<C>(mut self, ctx: C) -> Self
    where
        C: IntoErrorContext,
    {
        self.context.push(ctx.into_error_context().into_message());
        self
    }

    /// Adds multiple context entries at once.
    ///
    /// Contexts are added in the order provided, with the first becoming
    /// the oldest and the last becoming the most recent.
    ///
    /// # Arguments
    ///
    /// * `contexts`: An iterator of context strings
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::error::ComposableError;
    ///
    /// let contexts = vec!["Step 1 failed".to_string(), "Step 2 failed".to_string()];
    /// let error = ComposableError::new("Invalid input")
    ///     .with_contexts(contexts);
    ///
    /// assert_eq!(error.context().len(), 2);
    /// ```
    #[inline]
    pub fn with_contexts<I>(mut self, contexts: I) -> Self
    where
        I: IntoIterator<Item = String>,
    {
        self.context.extend(contexts); // O(1) per element
        self
    }

    /// Returns a reference to the core error.
    ///
    #[inline]
    pub fn core_error(&self) -> &E {
        &self.core_error
    }

    /// Returns a vector of contexts with the most recent first.
    ///
    #[inline]
    pub fn context(&self) -> Vec<String> {
        self.context.iter().rev().cloned().collect()
    }

    /// Returns an iterator over the context entries, most recent first.
    ///
    #[inline]
    pub fn context_iter(&self) -> std::iter::Rev<std::slice::Iter<'_, String>> {
        self.context.iter().rev()
    }

    /// Returns the error code if present.
    ///
    #[inline]
    pub fn error_code(&self) -> Option<u32> {
        self.error_code
    }

    /// Sets the error code.
    ///
    /// # Arguments
    ///
    /// * `code`: The error code to set
    ///
    #[inline]
    pub fn set_code(mut self, code: u32) -> Self {
        self.error_code = Some(code);
        self
    }

    /// Maps the core error to a new type.
    ///
    /// This preserves all context and error code information while transforming
    /// the core error. Useful for error type conversions.
    ///
    /// # Type Parameters
    ///
    /// * `F`: The mapping function type
    /// * `T`: The new core error type
    ///
    /// # Arguments
    ///
    /// * `f`: The function to apply to the core error
    ///
    #[inline]
    pub fn map_core<F, T>(self, f: F) -> ComposableError<T>
    where
        F: FnOnce(E) -> T,
    {
        ComposableError {
            core_error: f(self.core_error),
            context: self.context,
            error_code: self.error_code,
        }
    }

    /// Returns the full error chain as a formatted string.
    ///
    /// This creates a human-readable representation of the error including
    /// all context information, formatted as a chain from most recent to
    /// core error.
    ///
    pub fn error_chain(&self) -> String
    where
        E: Display,
    {
        let mut chain = String::new();
        self.write_chain(&mut chain)
            .expect("writing to String cannot fail");
        chain
    }

    /// Writes the chain directly to a formatter or string buffer. Keeping
    /// formatting in one pass avoids the temporary `String` previously
    /// created by `Display`.
    pub(crate) fn write_chain<W>(&self, out: &mut W) -> std::fmt::Result
    where
        W: std::fmt::Write,
        E: Display,
    {
        for (i, ctx) in self.context.iter().rev().enumerate() {
            if i > 0 {
                out.write_str(" -> ")?;
            }
            out.write_str(ctx)?;
        }

        if !self.context.is_empty() {
            out.write_str(" -> ")?;
        }

        write!(out, "{}", self.core_error)?;
        if let Some(code) = self.error_code {
            write!(out, " (code: {})", code)?;
        }
        Ok(())
    }
}

impl<E: Display> Display for ComposableError<E> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.write_chain(f)
    }
}

impl<E: Debug + Display> std::error::Error for ComposableError<E> {}

/// Implements `From<E>` for idiomatic error conversion.
///
/// This allows any error type `E` to be converted into a `ComposableError<E>`
/// using the standard `into()` method, making error handling more ergonomic.
///
impl<E> From<E> for ComposableError<E> {
    #[inline]
    fn from(error: E) -> Self {
        Self::new(error)
    }
}

/// A lightweight error context that can be attached to any error type.
///
/// `ErrorContext` provides a minimal way to add contextual information
/// to errors without the full overhead of `ComposableError`. It's designed
/// for cases where you need just a single context string.
///
/// # Examples
///
/// ```rust
/// use rustica::error::ErrorContext;
///
/// let context = ErrorContext::new("Failed during startup");
/// assert_eq!(context.message(), "Failed during startup");
/// ```
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[repr(transparent)]
pub struct ErrorContext {
    message: String,
}

impl ErrorContext {
    /// Creates a new error context with the given message.
    ///
    /// # Arguments
    ///
    /// * `message`: The context message
    ///
    #[inline]
    pub fn new<S: Into<String>>(message: S) -> Self {
        Self {
            message: message.into(),
        }
    }

    /// Returns the context message.
    ///
    #[inline]
    pub fn message(&self) -> &str {
        &self.message
    }

    /// Consumes the context and returns its owned message without cloning.
    #[inline]
    pub fn into_message(self) -> String {
        self.message
    }
}

impl Display for ErrorContext {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.message)
    }
}

impl std::error::Error for ErrorContext {}

/// A trait for types that can provide error context information.
///
/// This trait allows different types to be used as error context sources,
/// enabling flexible error context composition.
pub trait IntoErrorContext {
    /// Converts this value into an `ErrorContext`.
    fn into_error_context(self) -> ErrorContext;
}

impl IntoErrorContext for String {
    #[inline]
    fn into_error_context(self) -> ErrorContext {
        ErrorContext::new(self)
    }
}

impl IntoErrorContext for &str {
    #[inline]
    fn into_error_context(self) -> ErrorContext {
        ErrorContext::new(self)
    }
}

impl IntoErrorContext for ErrorContext {
    #[inline]
    fn into_error_context(self) -> ErrorContext {
        self
    }
}

/// A lazy error context that is evaluated only when needed.
///
/// This is used by the `context!` macro to avoid formatting costs
/// when the error path is not taken.
#[repr(transparent)]
pub struct LazyContext<F> {
    generator: F,
}

impl<F> LazyContext<F> {
    /// Creates a new lazy context with the given generator function.
    #[inline]
    pub fn new(generator: F) -> Self {
        Self { generator }
    }
}

impl<F> IntoErrorContext for LazyContext<F>
where
    F: FnOnce() -> String,
{
    #[inline]
    fn into_error_context(self) -> ErrorContext {
        ErrorContext::new((self.generator)())
    }
}

/// Convenience type alias for a Result with ComposableError.
///
/// This provides a more ergonomic way to work with Results that use
/// ComposableError as the error type.
///
/// # Type Parameters
///
/// * `T`: The success type
/// * `E`: The core error type
///
#[allow(clippy::result_large_err)]
pub type ComposableResult<T, E> = Result<T, ComposableError<E>>;

/// Convenience type alias for a boxed ComposableError to reduce size.
///
/// This helps avoid clippy warnings about large error types by boxing
/// the ComposableError when it becomes too large.
///
/// # Type Parameters
///
/// * `E`: The core error type
pub type BoxedComposableError<E> = Box<ComposableError<E>>;

/// Convenience type alias for a Result with boxed ComposableError.
///
/// This provides a more memory-efficient way to work with Results that use
/// ComposableError as the error type when the error is large.
///
/// # Type Parameters
///
/// * `T`: The success type
/// * `E`: The core error type
pub type BoxedComposableResult<T, E> = Result<T, BoxedComposableError<E>>;

#[cfg(test)]
mod tests {
    use crate::context;
    use crate::error::{ComposableError, ErrorContext, with_context_result};
    use std::sync::Arc;
    use std::sync::atomic::{AtomicBool, Ordering};

    #[test]
    fn composable_error_accessors_preserve_context_order() {
        let error = ComposableError::with_code("root", 404)
            .with_context("first")
            .with_context("second");

        assert_eq!(error.core_error(), &"root");
        assert_eq!(error.context(), vec!["second", "first"]);
        assert_eq!(
            error.context_iter().collect::<Vec<_>>(),
            error.context().iter().collect::<Vec<_>>()
        );
        assert_eq!(error.error_code(), Some(404));
        assert_eq!(ComposableError::new("plain").error_code(), None);
    }

    #[test]
    fn set_code_and_map_core_preserve_error_metadata() {
        let error = ComposableError::new(42)
            .with_context("numeric")
            .set_code(500)
            .map_core(|value| format!("code: {value}"));

        assert_eq!(error.core_error(), "code: 42");
        assert_eq!(error.context(), vec!["numeric"]);
        assert_eq!(error.error_code(), Some(500));
    }

    #[test]
    fn error_chain_and_from_conversion_are_user_readable() {
        let error: ComposableError<&str> = "file not found".into();
        assert_eq!(error.core_error(), &"file not found");
        assert!(error.context().is_empty());

        let chained = ComposableError::new("Connection refused")
            .with_context("Database connection failed")
            .with_context("User login failed");
        assert_eq!(
            chained.error_chain(),
            "User login failed -> Database connection failed -> Connection refused"
        );
    }

    #[test]
    fn error_context_exposes_its_message() {
        let context = ErrorContext::new("Operation failed");
        assert_eq!(context.message(), "Operation failed");
    }

    #[test]
    fn test_lazy_context_evaluation() {
        let was_evaluated = Arc::new(AtomicBool::new(false));
        let was_evaluated_clone = was_evaluated.clone();
        let result: Result<i32, &str> = Ok(42);

        let _ = with_context_result(
            result,
            context!("This should not be evaluated: {}", {
                was_evaluated_clone.store(true, Ordering::SeqCst);
                "failed"
            }),
        );

        assert!(!was_evaluated.load(Ordering::SeqCst));
    }

    #[test]
    fn test_lazy_context_evaluation_on_error() {
        let was_evaluated = Arc::new(AtomicBool::new(false));
        let was_evaluated_clone = was_evaluated.clone();
        let result: Result<i32, &str> = Err("oops");

        let _ = with_context_result(
            result,
            context!("Context evaluated: {}", {
                was_evaluated_clone.store(true, Ordering::SeqCst);
                "yes"
            }),
        );

        assert!(was_evaluated.load(Ordering::SeqCst));
    }

    #[test]
    fn context_into_message_moves_buffer() {
        let message = String::from("owned context");
        let ptr = message.as_ptr();
        let moved = ErrorContext::new(message).into_message();
        assert_eq!(moved.as_ptr(), ptr);
        assert_eq!(moved, "owned context");
    }
}

#[cfg(test)]
mod unit_tests {
    use super::ComposableError;

    #[test]
    fn public_error_anatomy_and_conversion_are_preserved() {
        let error = ComposableError::with_code("io_error", 500)
            .with_context("layer 1".to_string())
            .with_context("layer 2".to_string());
        assert_eq!(error.core_error(), &"io_error");
        assert_eq!(error.error_code(), Some(500));
        assert_eq!(error.context().len(), 2);
        assert!(error.error_chain().contains("io_error"));

        let converted: ComposableError<&str> = "simple".into();
        assert_eq!(converted.core_error(), &"simple");
    }
}
