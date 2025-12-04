//! # Unified Error Handling System
//!
//! This module provides a category theory-inspired error handling system that maintains
//! functional purity while leveraging Rust's strengths. It extends the existing `WithError`
//! trait with composable error structures and functional error handling patterns.
//!
//! ## Design Philosophy
//!
//! The error system follows category theory principles:
//! - **Functoriality**: Error transformations preserve structure
//! - **Composability**: Error handlers can be composed like functions  
//! - **Purity**: No hidden state or side effects in error handling
//!
//! ## Module Structure
//!
//! - `core`: Extended WithError trait and ErrorCategory
//! - `types`: ComposableError and error context structures
//! - `convert`: Type conversion utilities between error types
//! - `context`: Error context management and accumulation
//! - `pipeline`: Functional error handling pipelines

pub mod context; // Error context management and accumulation
pub mod convert; // Error type conversions
pub mod core; // Extended WithError trait and ErrorCategory
pub mod macros; // Error handling macros
pub mod types; // ComposableError and error context structures

// Re-export commonly used items
pub use context::{
    ErrorPipeline, accumulate_context, context_accumulator, context_fn, error_pipeline,
    extract_context, format_error_chain, with_context, with_context_result,
};
pub use convert::{
    collect_errors, composable_to_core, core_to_composable, either_to_result, either_to_validated,
    flatten_composable_result, result_to_either, result_to_validated, split_validated_errors,
    validated_to_either, validated_to_result, wrap_in_composable_result,
    wrap_in_composable_result_boxed,
};
pub use core::{ErrorCategory, ErrorOps};
pub use types::{
    BoxedComposableError, BoxedComposableResult, ComposableError, ComposableResult, ErrorContext,
    IntoErrorContext, LazyContext,
};

// Re-export existing error utilities for compatibility (avoiding conflicts)
pub use crate::utils::error_utils::{
    ResultExt, WithError, sequence, sequence_with_error, traverse, traverse_validated,
};
