//! Context-accumulating error handling prelude.
//!
//! Re-exports primary error types, macros, and context utilities from [`crate::error`].
//!
//! # Examples
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
//! assert_eq!(
//!     result.unwrap_err().contexts(),
//!     ["while running example"].as_slice()
//! );
//! ```

pub use crate::context;
pub use crate::error::{
    ContextError, IntoErrorContext, LazyContext, accumulate_context, context_accumulator,
    context_fn, with_context, with_context_result,
};
