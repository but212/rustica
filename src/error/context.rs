//! # Slim Error Context Management and ContextError
//!
//! This module provides the standard `ContextError<E>` wrapper for context accumulation,
//! along with lightweight context utilities (ErrorContext, IntoErrorContext, LazyContext).

use std::fmt::{Debug, Display};

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

/// Formats an error with its full context chain.
#[deprecated(
    since = "0.16.0",
    note = "Use error.error_chain() instead. format_error_chain is scheduled for removal in 0.18.0."
)]
pub fn format_error_chain<E>(error: &ContextError<E>) -> String
where
    E: Display,
{
    error.error_chain()
}

/// Extracts all context information from a `ContextError` (most recent first).
#[deprecated(
    since = "0.16.0",
    note = "Use error.context() or error.context_iter() instead. extract_context is scheduled for removal in 0.18.0."
)]
pub fn extract_context<E>(error: &ContextError<E>) -> Vec<String> {
    error.context()
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
    #[allow(deprecated)]
    fn format_error_chain_renders_context_and_error() {
        let error = ContextError::new("file not found")
            .with_context("failed to load config")
            .with_context("application startup failed");

        assert_eq!(
            format_error_chain(&error),
            "application startup failed -> failed to load config -> file not found"
        );
    }

    #[test]
    #[allow(deprecated)]
    fn extract_context_returns_most_recent_first() {
        let error = ContextError::new("error")
            .with_context("context 1")
            .with_context("context 2");

        assert_eq!(extract_context(&error), vec!["context 2", "context 1"]);
    }
}
