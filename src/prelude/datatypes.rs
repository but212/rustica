//!
//! Prelude: Core Functional Data Types
//!
//! This module re-exports Rustica's core functional data types for expressive, type-safe programming.
//! These types encode common functional programming patterns such as optionality, error handling,
//! validation, optics, and deferred computation.
//!
//! ## Included Data Types
//!
//! - [`Validated`]: Error accumulation and validation
//! - [`Choice`]: Non-empty collection with a primary value and prioritized alternatives
//! - [`Free`]: Free monad for DSL construction, AST inspection (`Clone`), and stack-safe trampoline evaluation
//! - [`Program`, `TryProgram`]: Statically-typed operational monads with zero-downcast command handlers
//! - [`Lens`, `Prism`]: Optics for immutable data access
//!
//! ## Usage Example
//!
//! ```rust
//! use rustica::prelude::datatypes::*;
//!
//! let v: Validated<i32, &str> = Validated::valid(5);
//! assert!(v.is_valid());
//! ```
//!
//! See each type's documentation for more details and advanced usage.

pub use crate::datatypes::choice::Choice;
pub use crate::datatypes::free::Free;
pub use crate::datatypes::lens::Lens;
pub use crate::datatypes::operational::{Handler, Program, TryHandler, TryProgram};
pub use crate::datatypes::prism::Prism;
pub use crate::datatypes::validated::{NonEmptyErrors, Validated};
pub use crate::datatypes::{ChoiceError, FreeError};
