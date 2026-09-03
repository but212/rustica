//! # Error Handling Macros
//!
//! This module provides macros for efficient error handling, particularly
//! for lazy evaluation of error contexts.

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
        $crate::error::types::LazyContext::new(move || format!($($arg)*))
    };
}
