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
    BoxedComposableError, BoxedComposableResult, ComposableError, ComposableResult, ErrorCategory,
    ErrorContext, ErrorOps, ErrorPipeline, IntoErrorContext, LazyContext, ResultExt, WithError,
    accumulate_context, collect_errors, composable_to_core, context_accumulator, context_fn,
    core_to_composable, either_to_result, either_to_validated, error_pipeline, extract_context,
    flatten_composable_result, format_error_chain, result_to_either, result_to_validated, sequence,
    sequence_with_error, split_validated_errors, traverse, traverse_validated, validated_to_either,
    validated_to_result, with_context, with_context_result, wrap_in_composable_result,
    wrap_in_composable_result_boxed,
};
