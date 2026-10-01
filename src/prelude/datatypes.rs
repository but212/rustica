//! Core functional data types prelude.
//!
//! Re-exports primary functional data types for validation, optics, DSLs, and deferred evaluation.
//!
//! # Included Types
//!
//! - [`Validated`], [`NonEmptyErrors`]: Error-accumulating validation
//! - [`Choice`], [`ChoiceError`]: Non-empty collection with prioritized alternatives
//! - [`Free`], [`FreeError`]: Free monad DSLs and stack-safe trampoline evaluation
//! - [`Program`], [`TryProgram`]: Typed operational monads
//! - [`Lens`], [`Prism`]: Optics for focused data access
//!
//! # Examples
//!
//! ```rust
//! use rustica::prelude::datatypes::*;
//!
//! let v: Validated<i32, &str> = Validated::valid(5);
//! assert!(v.is_valid());
//! ```

pub use crate::datatypes::choice::Choice;
pub use crate::datatypes::free::Free;
pub use crate::datatypes::lens::Lens;
pub use crate::datatypes::operational::{Handler, Program, TryHandler, TryProgram};
pub use crate::datatypes::prism::Prism;
pub use crate::datatypes::validated::{NonEmptyErrors, Validated};
pub use crate::datatypes::{ChoiceError, FreeError};
