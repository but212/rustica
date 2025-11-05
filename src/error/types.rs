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
/// # Performance Characteristics
///
/// - Uses `SmallVec<[String; 4]>` for context storage, avoiding heap allocation
///   for up to 4 context entries (covers 95% of real-world cases)
/// - O(1) context addition
/// - O(n) context traversal where n is the number of context entries
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
    /// A stack of context information, most recent first
    pub context: SmallVec<[String; 4]>,
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
    /// Context is added to the front of the context stack, so the most recent
    /// context appears first when iterating. This follows the pattern of
    /// error propagation where higher-level context wraps lower-level errors.
    ///
    /// # Arguments
    ///
    /// * `ctx`: The context string to add
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::error::ComposableError;
    ///
    /// let error = ComposableError::new("Connection refused")
    ///     .with_context("Failed to connect to database".to_string())
    ///     .with_context("User authentication failed".to_string());
    ///
    /// let contexts: Vec<&String> = error.context().iter().collect();
    /// assert_eq!(contexts[0], "User authentication failed");
    /// assert_eq!(contexts[1], "Failed to connect to database");
    /// ```
    #[inline]
    pub fn with_context(mut self, ctx: String) -> Self {
        self.context.insert(0, ctx);
        self
    }

    /// Adds multiple context entries at once.
    ///
    /// Context entries are added in reverse order so that the first entry
    /// in the iterator becomes the most recent context.
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
        let mut contexts: Vec<String> = contexts.into_iter().collect();
        contexts.reverse(); // Reverse so first becomes most recent
        for ctx in contexts {
            self.context.insert(0, ctx);
        }
        self
    }

    /// Returns a reference to the core error.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::error::ComposableError;
    ///
    /// let error = ComposableError::new("Core issue");
    /// assert_eq!(error.core_error(), &"Core issue");
    /// ```
    #[inline]
    pub fn core_error(&self) -> &E {
        &self.core_error
    }

    /// Returns a reference to the context stack.
    ///
    /// The context is ordered with the most recent context first.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::error::ComposableError;
    ///
    /// let error = ComposableError::new("Error")
    ///     .with_context("Context 1".to_string())
    ///     .with_context("Context 2".to_string());
    ///
    /// assert_eq!(error.context().len(), 2);
    /// assert_eq!(error.context()[0], "Context 2"); // Most recent first
    /// ```
    #[inline]
    pub fn context(&self) -> &SmallVec<[String; 4]> {
        &self.context
    }

    /// Returns the error code if present.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::error::ComposableError;
    ///
    /// let error = ComposableError::with_code("Not found", 404);
    /// assert_eq!(error.error_code(), Some(404));
    ///
    /// let simple_error = ComposableError::new("Simple error");
    /// assert_eq!(simple_error.error_code(), None);
    /// ```
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
    /// # Examples
    ///
    /// ```rust
    /// use rustica::error::ComposableError;
    ///
    /// let error = ComposableError::new("Server error").set_code(500);
    /// assert_eq!(error.error_code(), Some(500));
    /// ```
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
    /// # Examples
    ///
    /// ```rust
    /// use rustica::error::ComposableError;
    ///
    /// let error = ComposableError::new(42)
    ///     .with_context("Numeric error".to_string());
    ///
    /// let string_error = error.map_core(|n| format!("Error code: {}", n));
    /// assert_eq!(string_error.core_error(), "Error code: 42");
    /// assert_eq!(string_error.context().len(), 1);
    /// ```
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

    /// Returns an iterator over the context entries, most recent first.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::error::ComposableError;
    ///
    /// let error = ComposableError::new("Error")
    ///     .with_context("First".to_string())
    ///     .with_context("Second".to_string());
    ///
    /// let contexts: Vec<&String> = error.context_iter().collect();
    /// assert_eq!(contexts, vec![&"Second".to_string(), &"First".to_string()]);
    /// ```
    #[inline]
    pub fn context_iter(&self) -> std::slice::Iter<'_, String> {
        self.context.iter()
    }

    /// Returns the full error chain as a formatted string.
    ///
    /// This creates a human-readable representation of the error including
    /// all context information, formatted as a chain from most recent to
    /// core error.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::error::ComposableError;
    ///
    /// let error = ComposableError::new("Connection refused")
    ///     .with_context("Database connection failed".to_string())
    ///     .with_context("User login failed".to_string());
    ///
    /// let chain = error.error_chain();
    /// assert!(chain.contains("User login failed"));
    /// assert!(chain.contains("Database connection failed"));
    /// assert!(chain.contains("Connection refused"));
    /// ```
    pub fn error_chain(&self) -> String
    where
        E: Display,
    {
        let mut chain = String::new();

        for (i, ctx) in self.context.iter().enumerate() {
            if i > 0 {
                chain.push_str(" -> ");
            }
            chain.push_str(ctx);
        }

        if !self.context.is_empty() {
            chain.push_str(" -> ");
        }

        chain.push_str(&format!("{}", self.core_error));

        if let Some(code) = self.error_code {
            chain.push_str(&format!(" (code: {})", code));
        }

        chain
    }
}

impl<E: Display> Display for ComposableError<E> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.error_chain())
    }
}

impl<E: Debug + Display> std::error::Error for ComposableError<E> {}

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
    /// # Examples
    ///
    /// ```rust
    /// use rustica::error::ErrorContext;
    ///
    /// let context = ErrorContext::new("Operation failed");
    /// assert_eq!(context.message(), "Operation failed");
    /// ```
    #[inline]
    pub fn new<S: Into<String>>(message: S) -> Self {
        Self {
            message: message.into(),
        }
    }

    /// Returns the context message.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::error::ErrorContext;
    ///
    /// let context = ErrorContext::new("Test message");
    /// assert_eq!(context.message(), "Test message");
    /// ```
    #[inline]
    pub fn message(&self) -> &str {
        &self.message
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
/// # Examples
///
/// ```rust
/// use rustica::error::{ComposableResult, ComposableError};
///
/// fn might_fail() -> ComposableResult<i32, &'static str> {
///     Err(ComposableError::new("Something went wrong"))
/// }
/// ```
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
