//! # Prelude: Unified Error Handling
//!
//! This module re-exports the primary interfaces from crate::error, making it easy to
//! pull in Rustica's context error types and error utilities with a single glob import
//! (use rustica::prelude::error::*;).
//!
//! ## Quick Start
//!
//! ```
//! use rustica::prelude::error::*;
//!
//! fn fallible() -> Result<(), &'static str> {
//!     Err("boom")
//! }
//!
//! let result = with_context_result(fallible(), "while running example");
//! assert!(result.is_err());
//! assert_eq!(result.unwrap_err().context(), vec!["while running example".to_string()]);
//! ```

pub use crate::context;
pub use crate::error::{
    ContextError, IntoErrorContext, LazyContext, accumulate_context, context_accumulator,
    context_fn, with_context, with_context_result,
};
