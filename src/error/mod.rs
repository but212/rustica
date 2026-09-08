//! # Unified Error Handling System
//!
//! Rustica provides standard Result<T, E> and std::error::Error as its primary error model,
//! and provides [`ContextError<E>`](crate::error::ContextError) as a lightweight abstraction for context accumulation.
//!
//! Legacy composable error types and HKT error abstractions (ComposableError, WithError)
//! are deprecated in 0.16.0 and scheduled for complete removal in 0.18.0.
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
pub mod types;

// Re-export modern ContextError and context utilities
pub use context::{
    ContextError, ErrorContext, IntoErrorContext, LazyContext, accumulate_context,
    context_accumulator, context_fn, with_context, with_context_result,
};

#[allow(deprecated)]
pub use context::{extract_context, format_error_chain};

// Re-export validated conversion utilities
pub use convert::{collect_errors, split_validated_errors};

// Re-export deprecated legacy types (scheduled for removal in 0.18.0)
#[allow(deprecated)]
pub use types::{BoxedComposableError, BoxedComposableResult, ComposableError, ComposableResult};

// Re-export macro
pub use crate::context;

// Re-export deprecated core traits (scheduled for removal in 0.18.0)
#[allow(deprecated)]
pub use core::{WithError, sequence_with_error, traverse_validated};
