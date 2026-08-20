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
//! - `core`: Extended WithError trait
//! - `types`: ComposableError and error context structures
//! - `convert`: Type conversion utilities between error types
//! - `context`: Error context management and accumulation
//! - `macros`: Error handling macros for lazy context evaluation

pub mod context; // Error context management and accumulation
pub mod convert; // Error type conversions
pub mod core; // Extended WithError trait
pub mod macros; // Error handling macros
pub mod types; // ComposableError and error context structures

// Re-export commonly used items
pub use context::{
    accumulate_context, context_accumulator, context_fn, extract_context, format_error_chain,
    with_context, with_context_result,
};
pub use convert::{collect_errors, split_validated_errors};
pub use types::{
    BoxedComposableError, BoxedComposableResult, ComposableError, ComposableResult, ErrorContext,
    IntoErrorContext, LazyContext,
};

// Re-export error utility traits directly from the unified error module.
pub use core::{WithError, sequence_with_error, traverse_validated};
