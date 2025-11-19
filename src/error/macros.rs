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
/// # Examples
///
/// ```rust
/// use rustica::context;
/// use rustica::error::{with_context_result, ComposableResult};
///
/// fn might_fail(id: i32) -> Result<i32, &'static str> {
///     Ok(id)
/// }
///
/// let id = 42;
/// // The format! is not executed because the result is Ok
/// let result = with_context_result(
///     might_fail(id),
///     context!("Failed to process item {}", id)
/// );
/// ```
#[macro_export]
macro_rules! context {
    ($($arg:tt)*) => {
        $crate::error::types::LazyContext::new(move || format!($($arg)*))
    };
}
