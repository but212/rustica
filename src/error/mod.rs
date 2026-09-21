//! # Unified Error Handling System
//!
//! Rustica provides standard `Result<T, E>` and `std::error::Error` as its primary error model,
//! and provides [`ContextError<E>`](crate::error::ContextError) as a lightweight abstraction for context accumulation.
//!
//! ## Modern Context-based Error Handling
//!
//! ```
//! use rustica::error::{ContextError, with_context_result};
//! use rustica::context;
//!
//! fn run_step() -> Result<(), &'static str> {
//!     Err("network timeout")
//! }
//!
//! let result = with_context_result(run_step(), context!("connecting to host {}", "localhost"));
//! assert!(result.is_err());
//! ```

use std::fmt::{Debug, Display};

use crate::datatypes::validated::{NonEmptyErrors, Validated, core::ErrorVec};

/// Creates a lazy error context that is only evaluated when an error occurs.
///
/// This macro avoids the runtime cost of formatting context strings when
/// the operation is successful. It returns a `LazyContext` that implements
/// `IntoErrorContext`.
///
/// Use it with `with_context_result` when context formatting should be deferred until
/// the error path is taken; the lazy-evaluation behavior is covered by the module tests.
#[macro_export]
macro_rules! context {
    ($($arg:tt)*) => {
        $crate::error::LazyContext::new(move || format!($($arg)*))
    };
}

pub use crate::context;

// Backward-compatibility aliases for former submodules
pub mod context {
    pub use super::*;
}
pub mod convert {
    pub use super::*;
}
pub mod core {
    pub use super::*;
}

/// A slim, standard-aligned error context wrapper.
///
/// Rustica provides standard Result<T, E> and std::error::Error as primary primitives,
/// and adds `ContextError<E>` as the minimal abstraction for context accumulation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ContextError<E> {
    error: E,
    context: Vec<String>,
}

impl<E> ContextError<E> {
    /// Creates a new ContextError wrapping the root error.
    #[inline]
    pub fn new(error: E) -> Self {
        Self {
            error,
            context: Vec::new(),
        }
    }

    /// Appends context information to this error.
    #[inline]
    pub fn with_context<C>(mut self, ctx: C) -> Self
    where
        C: IntoErrorContext,
    {
        self.context.push(ctx.into_error_context().into_message());
        self
    }

    /// Appends multiple context strings to this error.
    #[inline]
    pub fn with_contexts<I>(mut self, contexts: I) -> Self
    where
        I: IntoIterator<Item = String>,
    {
        self.context.extend(contexts);
        self
    }

    /// Returns a reference to the root error.
    #[inline]
    pub fn error(&self) -> &E {
        &self.error
    }

    /// Consumes the wrapper and returns the underlying error.
    #[inline]
    pub fn into_error(self) -> E {
        self.error
    }

    /// Returns the accumulated contexts with most recent first.
    #[inline]
    pub fn context(&self) -> Vec<String> {
        self.context.iter().rev().cloned().collect()
    }

    /// Returns an iterator over context entries, most recent first.
    #[inline]
    pub fn context_iter(&self) -> std::iter::Rev<std::slice::Iter<'_, String>> {
        self.context.iter().rev()
    }

    /// Returns a zero-allocation reference to the internal contexts slice in insertion order (oldest first).
    #[inline]
    pub fn contexts_raw(&self) -> &[String] {
        &self.context
    }

    /// Maps the underlying error to a new type while preserving context.
    #[inline]
    pub fn map_error<F, T>(self, f: F) -> ContextError<T>
    where
        F: FnOnce(E) -> T,
    {
        ContextError {
            error: f(self.error),
            context: self.context,
        }
    }

    /// Returns the full error chain formatted as most_recent -> ... -> error.
    pub fn error_chain(&self) -> String
    where
        E: Display,
    {
        let mut chain = String::new();
        self.write_chain(&mut chain)
            .expect("writing to String cannot fail");
        chain
    }

    /// Writes the error chain directly to a formatter or writer.
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

        write!(out, "{}", self.error)
    }
}

impl<E: Display> Display for ContextError<E> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.write_chain(f)
    }
}

impl<E: Debug + Display + std::error::Error + 'static> std::error::Error for ContextError<E> {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        Some(&self.error)
    }
}

impl<E> From<E> for ContextError<E> {
    #[inline]
    fn from(error: E) -> Self {
        Self::new(error)
    }
}

/// A lightweight error context that can be attached to any error type.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
#[repr(transparent)]
pub struct ErrorContext {
    message: String,
}

impl ErrorContext {
    /// Creates a new error context with the given message.
    #[inline]
    pub fn new<S: Into<String>>(message: S) -> Self {
        Self {
            message: message.into(),
        }
    }

    /// Returns the context message.
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
pub trait IntoErrorContext {
    /// Converts this value into an ErrorContext.
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

/// Adds context to an error value, creating a ContextError.
#[inline]
pub fn with_context<E, C>(error: E, context: C) -> ContextError<E>
where
    C: IntoErrorContext,
{
    ContextError::new(error).with_context(context)
}

/// Adds context to a Result, converting the error variant to `ContextError<E>`.
#[inline]
pub fn with_context_result<T, E, C>(result: Result<T, E>, context: C) -> Result<T, ContextError<E>>
where
    C: IntoErrorContext,
{
    result.map_err(|e| with_context(e, context))
}

/// Creates a reusable context-attaching closure.
#[inline]
pub fn context_fn<E, C>(context: C) -> impl Fn(E) -> ContextError<E>
where
    C: IntoErrorContext + Clone,
{
    move |error| with_context(error, context.clone())
}

/// Accumulates context from multiple sources into a single ContextError.
pub fn accumulate_context<E, I, C>(error: E, contexts: I) -> ContextError<E>
where
    I: IntoIterator<Item = C>,
    C: IntoErrorContext,
{
    let context_strings: Vec<String> = contexts
        .into_iter()
        .map(|c| c.into_error_context().into_message())
        .collect();

    ContextError::new(error).with_contexts(context_strings)
}

/// Creates a reusable context accumulator function.
pub fn context_accumulator<E, I, C>(contexts: I) -> impl Fn(E) -> ContextError<E>
where
    I: IntoIterator<Item = C> + Clone,
    C: IntoErrorContext + Clone,
{
    move |error| accumulate_context(error, contexts.clone())
}

/// Collects zero or more errors into `Validated`.
pub fn collect_errors<E, I>(errors: I) -> Validated<(), E>
where
    I: IntoIterator<Item = E>,
{
    let errors: Vec<E> = errors.into_iter().collect();
    if errors.is_empty() {
        Validated::Valid(())
    } else {
        Validated::invalid_many(errors)
    }
}

/// Expands accumulated errors into individual fail-fast results.
pub fn split_validated_errors<T, E>(validated: Validated<T, E>) -> Vec<Result<T, E>> {
    match validated {
        Validated::Valid(value) => vec![Ok(value)],
        Validated::Invalid(errors) => errors.into_iter().map(Err).collect(),
    }
}

/// Traverses a collection with a fallible function, accumulating all errors into `Validated`.
pub fn traverse_validated<A, B, E, F>(
    collection: impl IntoIterator<Item = A>, mut f: F,
) -> Validated<Vec<B>, E>
where
    F: FnMut(A) -> Result<B, E>,
{
    let mut values = Vec::new();
    let mut errors = ErrorVec::new();

    for item in collection {
        match f(item) {
            Ok(value) => values.push(value),
            Err(error) => errors.push(error),
        }
    }

    match NonEmptyErrors::try_from_vec(errors) {
        Some(errors) => Validated::Invalid(errors),
        None => Validated::Valid(values),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn accumulate_context_preserves_all_entries() {
        let error = accumulate_context(
            "core error",
            ["step 1 failed", "step 2 failed", "operation failed"],
        );

        assert_eq!(error.context().len(), 3);
        assert_eq!(error.context()[0], "operation failed");
    }

    #[test]
    fn context_accumulator_reuses_contexts_for_multiple_errors() {
        let accumulator = context_accumulator(["database error", "user operation failed"]);

        let first = accumulator("connection timeout");
        let second = accumulator("query failed");

        assert_eq!(first.context().len(), 2);
        assert_eq!(second.context().len(), 2);
        assert_eq!(first.context(), second.context());
    }

    #[test]
    fn error_conversions_preserve_non_clone_values() {
        struct NoClone(&'static str);
        let collected = collect_errors([NoClone("error")]);
        assert_eq!(collected.error_slice()[0].0, "error");
        let split = split_validated_errors(Validated::<(), NoClone>::invalid(NoClone("split")));
        let mut split = split.into_iter();
        assert!(matches!(split.next(), Some(Err(NoClone("split")))));
        assert!(split.next().is_none());
    }

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
