//!
//! Prelude: Unified Error Handling
//!
//! This module re-exports the primary interfaces from `crate::error`, making it easy to
//! pull in Rustica's composable error types, pipelines, and legacy compatibility shims
//! with a single glob import (`use rustica::prelude::error::*;`).
//!
//! ## Quick Start
//!
//! ```rust
//! use rustica::prelude::error::*;
//!
//! fn fallible() -> ComposableResult<(), &'static str> {
//!     Err("boom").map_err(ComposableError::new)
//! }
//!
//! let result = fallible().map_err(|e| e.with_context("while running example"));
//! assert!(result.is_err());
//! assert_eq!(result.unwrap_err().context(), vec!["while running example".to_string()]);
//! ```

pub use crate::error::{
    BoxedComposableError, BoxedComposableResult, ComposableError, ComposableResult, ErrorContext,
    IntoErrorContext, LazyContext, WithError, accumulate_context, collect_errors,
    context_accumulator, context_fn, extract_context, format_error_chain, sequence_with_error,
    split_validated_errors, traverse_validated, with_context, with_context_result,
};
