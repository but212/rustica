//! Context-accumulating error handling.
//!
//! Integrates standard `Result<T, E>` and `core::error::Error` with
//! [`ContextError<E>`](crate::error::ContextError) for stack-ordered diagnostic context.
//!
//! # Examples
//!
//! ```
//! use rustica::error::{with_context_result, ContextError};
//! use rustica::context;
//!
//! fn run_step() -> Result<(), &'static str> {
//!     Err("network timeout")
//! }
//!
//! let result = with_context_result(run_step(), context!("connecting to host {}", "localhost"));
//! assert!(result.is_err());
//! ```

use core::fmt::{Debug, Display};

/// Creates a lazy error context evaluated only on error.
///
/// Returns a [`LazyContext`] implementing [`IntoErrorContext`]. Use with
/// [`with_context_result`] to defer formatting costs to the error path.
#[macro_export]
macro_rules! context {
    ($($arg:tt)*) => {
        $crate::error::LazyContext::new(move || $crate::error::__macro_support::format!($($arg)*))
    };
}

/// Internal re-exports for [`context!`]. Not stable public API.
#[doc(hidden)]
pub mod __macro_support {
    pub use alloc::format;
}

use alloc::{
    string::{String, ToString},
    vec::Vec,
};

pub use crate::context;

/// Lightweight context-accumulating error wrapper.
///
/// Stores accumulated context entries in newest-first order around the root error.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ContextError<E> {
    error: E,
    context: Vec<String>,
}

impl<E> ContextError<E> {
    /// Wraps a root error with an empty context stack.
    #[inline]
    pub const fn new(error: E) -> Self {
        Self {
            error,
            context: Vec::new(),
        }
    }

    /// Prepends context to the front of the context stack (newest first).
    #[inline]
    pub fn with_context<C>(mut self, ctx: C) -> Self
    where
        C: IntoErrorContext,
    {
        self.context.insert(0, ctx.into_error_context());
        self
    }

    /// Prepends multiple context entries in encounter order (last item becomes newest).
    #[inline]
    pub fn with_contexts<I, C>(mut self, contexts: I) -> Self
    where
        I: IntoIterator<Item = C>,
        C: IntoErrorContext,
    {
        let iter = contexts.into_iter();
        let (lower, _) = iter.size_hint();
        let mut new_contexts = Vec::with_capacity(lower + self.context.len());
        new_contexts.extend(iter.map(IntoErrorContext::into_error_context));
        new_contexts.reverse();
        new_contexts.append(&mut self.context);
        self.context = new_contexts;
        self
    }

    /// Returns a reference to the root error.
    #[inline]
    pub const fn error(&self) -> &E {
        &self.error
    }

    /// Consumes the wrapper and returns the underlying error.
    #[inline]
    pub fn into_error(self) -> E {
        self.error
    }

    /// Returns accumulated context entries (newest first).
    #[inline]
    pub const fn contexts(&self) -> &[String] {
        self.context.as_slice()
    }

    /// Clones accumulated context entries into a vector (newest first).
    #[inline]
    pub fn to_contexts(&self) -> Vec<String> {
        self.context.clone()
    }

    /// Returns an iterator over context entries (newest first).
    #[inline]
    pub fn context_iter(&self) -> core::slice::Iter<'_, String> {
        self.context.iter()
    }

    /// Maps the root error while preserving accumulated context.
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

    /// Formats the context chain as `newest -> ... -> oldest` (or root error if empty).
    pub fn error_chain(&self) -> String
    where
        E: Display,
    {
        let total_len: usize = self.context.iter().map(String::len).sum();
        let sep_len = self.context.len().saturating_sub(1) * " -> ".len();
        let mut chain = String::with_capacity(total_len + sep_len);
        self.write_chain(&mut chain)
            .expect("writing to String cannot fail");
        chain
    }

    /// Writes the formatted context chain directly to a writer.
    pub(crate) fn write_chain<W>(&self, out: &mut W) -> core::fmt::Result
    where
        W: core::fmt::Write,
        E: Display,
    {
        if self.context.is_empty() {
            // Fall back to root error when no context exists.
            return write!(out, "{}", self.error);
        }

        for (i, ctx) in self.context.iter().enumerate() {
            if i > 0 {
                out.write_str(" -> ")?;
            }
            out.write_str(ctx)?;
        }

        Ok(())
    }
}

impl<E: Display> Display for ContextError<E> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        self.write_chain(f)
    }
}

impl<E: Debug + Display + core::error::Error + 'static> core::error::Error for ContextError<E> {
    fn source(&self) -> Option<&(dyn core::error::Error + 'static)> {
        Some(&self.error)
    }
}

impl<E> From<E> for ContextError<E> {
    #[inline]
    fn from(error: E) -> Self {
        Self::new(error)
    }
}

/// Conversion into an error context string.
pub trait IntoErrorContext {
    /// Converts this value into a context string.
    fn into_error_context(self) -> String;
}

impl IntoErrorContext for String {
    #[inline]
    fn into_error_context(self) -> String {
        self
    }
}

impl IntoErrorContext for &str {
    #[inline]
    fn into_error_context(self) -> String {
        self.to_string()
    }
}

impl IntoErrorContext for &String {
    #[inline]
    fn into_error_context(self) -> String {
        self.clone()
    }
}

/// Lazy error context evaluated on demand.
#[derive(Debug, Clone)]
#[repr(transparent)]
pub struct LazyContext<F> {
    generator: F,
}

impl<F> LazyContext<F> {
    /// Creates a lazy context with the given generator.
    #[inline]
    pub const fn new(generator: F) -> Self {
        Self { generator }
    }
}

impl<F> IntoErrorContext for LazyContext<F>
where
    F: FnOnce() -> String,
{
    #[inline]
    fn into_error_context(self) -> String {
        (self.generator)()
    }
}

/// Wraps `error` in a [`ContextError`] with `context`.
#[inline]
pub fn with_context<E, C>(error: E, context: C) -> ContextError<E>
where
    C: IntoErrorContext,
{
    ContextError::new(error).with_context(context)
}

/// Maps any error in `result` into a [`ContextError`] with `context`.
#[inline]
pub fn with_context_result<T, E, C>(result: Result<T, E>, context: C) -> Result<T, ContextError<E>>
where
    C: IntoErrorContext,
{
    result.map_err(|e| with_context(e, context))
}

/// Returns a closure attaching `context` to an error.
#[inline]
pub const fn context_fn<E, C>(context: C) -> impl Fn(E) -> ContextError<E>
where
    C: IntoErrorContext + Clone,
{
    move |error| with_context(error, context.clone())
}

/// Wraps `error` in a [`ContextError`] populated with `contexts`.
pub fn accumulate_context<E, I, C>(error: E, contexts: I) -> ContextError<E>
where
    I: IntoIterator<Item = C>,
    C: IntoErrorContext,
{
    ContextError::new(error).with_contexts(contexts)
}

/// Returns a closure attaching pre-evaluated `contexts` to an error.
pub fn context_accumulator<E, I, C>(contexts: I) -> impl Fn(E) -> ContextError<E>
where
    I: IntoIterator<Item = C>,
    C: IntoErrorContext,
{
    let mut pre_evaluated: Vec<String> = contexts
        .into_iter()
        .map(IntoErrorContext::into_error_context)
        .collect();
    pre_evaluated.reverse();
    move |error| ContextError {
        error,
        context: pre_evaluated.clone(),
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

        assert_eq!(error.contexts().len(), 3);
        assert_eq!(error.contexts()[0], "operation failed");
        assert_eq!(error.contexts(), error.to_contexts().as_slice());
    }

    #[test]
    fn context_accumulator_reuses_contexts_for_multiple_errors() {
        let accumulator = context_accumulator(["database error", "user operation failed"]);

        let first = accumulator("connection timeout");
        let second = accumulator("query failed");

        assert_eq!(first.contexts().len(), 2);
        assert_eq!(second.contexts().len(), 2);
        assert_eq!(first.contexts(), second.contexts());
        assert_eq!(first.contexts()[0], "user operation failed");
    }

    #[test]
    fn into_error_context_implementations() {
        let s = String::from("owned");
        let ref_s = &s;
        let str_literal = "literal";
        let lazy = LazyContext::new(|| "lazy".to_string());

        assert_eq!(ref_s.into_error_context(), "owned");
        assert_eq!(s.into_error_context(), "owned");
        assert_eq!(str_literal.into_error_context(), "literal");
        assert_eq!(lazy.into_error_context(), "lazy");
    }

    #[test]
    fn context_macro_formats_without_caller_side_format_macro() {
        // Under `#![no_std]`, verify macro resolves `format!` via `$crate`.
        let lazy = crate::context!("value {}", 7);
        let error = with_context_result::<(), &str, _>(Err("root"), lazy).unwrap_err();

        assert_eq!(error.contexts(), ["value 7"].as_slice());
    }

    #[test]
    fn context_macro_defers_formatting_until_error_path() {
        let lazy = crate::context!("value {}", 7);
        let ok: Result<(), ContextError<&str>> = with_context_result(Ok(()), lazy);
        assert!(ok.is_ok());
    }

    #[test]
    fn context_fn_attaches_context() {
        let attach = context_fn("step failed");
        let err = attach("io timeout");
        assert_eq!(err.error(), &"io timeout");
        assert_eq!(err.contexts(), ["step failed"].as_slice());
    }

    #[test]
    fn test_const_fn_capability() {
        const fn inspect_error<E>(err: &ContextError<E>) -> (&E, &[String]) {
            (err.error(), err.contexts())
        }

        let err = ContextError::new("root error");
        let (root, ctxs) = inspect_error(&err);
        assert_eq!(*root, "root error");
        assert_eq!(ctxs, &[] as &[String]);
    }
}
