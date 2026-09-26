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

/// A slim, standard-aligned error context wrapper.
///
/// Rustica provides standard Result<T, E> and std::error::Error as primary primitives,
/// and adds `ContextError<E>` as the minimal abstraction for context accumulation.
/// Context entries are stored in newest-first order.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ContextError<E> {
    error: E,
    context: Vec<String>,
}

impl<E> ContextError<E> {
    /// Creates a new ContextError wrapping the root error.
    #[inline]
    pub const fn new(error: E) -> Self {
        Self {
            error,
            context: Vec::new(),
        }
    }

    /// Appends context information to this error, placing it at the front of the context stack.
    #[inline]
    pub fn with_context<C>(mut self, ctx: C) -> Self
    where
        C: IntoErrorContext,
    {
        self.context.insert(0, ctx.into_error_context());
        self
    }

    /// Appends multiple context entries in encounter order (last item is most recent).
    #[inline]
    pub fn with_contexts<I, C>(mut self, contexts: I) -> Self
    where
        I: IntoIterator<Item = C>,
        C: IntoErrorContext,
    {
        let mut new_contexts: Vec<String> = contexts
            .into_iter()
            .map(IntoErrorContext::into_error_context)
            .collect();
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

    /// Returns the accumulated contexts with most recent first.
    #[inline]
    pub fn context(&self) -> Vec<String> {
        self.context.clone()
    }

    /// Returns an iterator over context entries, most recent first.
    #[inline]
    pub fn context_iter(&self) -> std::slice::Iter<'_, String> {
        self.context.iter()
    }

    /// Returns a zero-allocation reference to the internal contexts slice (most recent first).
    #[inline]
    pub const fn contexts_raw(&self) -> &[String] {
        self.context.as_slice()
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
        for (i, ctx) in self.context.iter().enumerate() {
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

/// A trait for types that can provide error context information.
pub trait IntoErrorContext {
    /// Converts this value into an error context string.
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

/// A lazy error context that is evaluated only when needed.
#[derive(Debug, Clone)]
#[repr(transparent)]
pub struct LazyContext<F> {
    generator: F,
}

impl<F> LazyContext<F> {
    /// Creates a new lazy context with the given generator function.
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
pub const fn context_fn<E, C>(context: C) -> impl Fn(E) -> ContextError<E>
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
    ContextError::new(error).with_contexts(contexts)
}

/// Creates a reusable context accumulator function.
pub fn context_accumulator<E, I, C>(contexts: I) -> impl Fn(E) -> ContextError<E>
where
    I: IntoIterator<Item = C>,
    C: IntoErrorContext,
{
    let pre_evaluated: Vec<String> = contexts
        .into_iter()
        .map(IntoErrorContext::into_error_context)
        .collect();
    move |error| ContextError::new(error).with_contexts(pre_evaluated.clone())
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
        assert_eq!(error.contexts_raw(), error.context().as_slice());
    }

    #[test]
    fn context_accumulator_reuses_contexts_for_multiple_errors() {
        let accumulator = context_accumulator(["database error", "user operation failed"]);

        let first = accumulator("connection timeout");
        let second = accumulator("query failed");

        assert_eq!(first.context().len(), 2);
        assert_eq!(second.context().len(), 2);
        assert_eq!(first.context(), second.context());
        assert_eq!(first.context()[0], "user operation failed");
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
    fn context_fn_attaches_context() {
        let attach = context_fn("step failed");
        let err = attach("io timeout");
        assert_eq!(err.error(), &"io timeout");
        assert_eq!(err.context(), vec!["step failed".to_string()]);
    }

    #[test]
    fn test_const_fn_capability() {
        const fn inspect_error<E>(err: &ContextError<E>) -> (&E, &[String]) {
            (err.error(), err.contexts_raw())
        }

        let err = ContextError::new("root error");
        let (root, ctxs) = inspect_error(&err);
        assert_eq!(*root, "root error");
        assert_eq!(ctxs, &[] as &[String]);
    }
}
