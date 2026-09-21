//! # Unified Error Handling System
//!
//! Rustica provides standard Result<T, E> and std::error::Error as its primary error model,
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

pub mod context;
pub mod convert;
pub mod core;
pub mod macros;

// Re-export modern ContextError and context utilities
pub use context::{
    ContextError, ErrorContext, IntoErrorContext, LazyContext, accumulate_context,
    context_accumulator, context_fn, with_context, with_context_result,
};

// Re-export validated conversion utilities
pub use convert::{collect_errors, split_validated_errors};

// Re-export macro
pub use crate::context;

// Re-export core functions
pub use core::traverse_validated;
