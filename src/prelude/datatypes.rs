//!
//! Prelude: Core Functional Data Types
//!
//! This module re-exports Rustica's core functional data types for expressive, type-safe programming.
//! These types encode common functional programming patterns such as optionality, error handling,
//! validation, state, dependency injection, and more.
//!
//! ## Included Data Types
//!
//! - [`Validated`]: Error accumulation and validation
//! - [`Choice`]: Non-deterministic computation with multiple alternatives
//! - [`State`]: Composable stateful computations
//! - [`Reader`]: Dependency injection/context passing
//! - [`Writer`]: Output accumulation (logging, etc.)
//! - [`Id`]: Identity functor
//! - [`IO`]: Side-effectful computations
//! - [`Cont`]: Continuation-passing style
//! - [`Lens`, `Prism`]: Optics for immutable data access; `Iso` values can
//!   be lifted with `Lens::from_iso` and `Prism::from_iso`
//!
//! ## Usage Example
//!
//! ```rust
//! use rustica::prelude::datatypes::*;
//! use rustica::traits::functor::Functor;
//!
//! let x = Id::new(42);
//! let y = x.fmap(|n| n + 1);
//! assert_eq!(y.unwrap(), 43);
//!
//! let v: Validated<&str, i32> = Validated::valid(5);
//! assert!(v.is_valid());
//! ```
//!
//! See each type's documentation for more details and advanced usage.

#[cfg(feature = "async")]
pub use crate::datatypes::async_monad::AsyncM;
pub use crate::datatypes::choice::Choice;
pub use crate::datatypes::cont::Cont;
pub use crate::datatypes::id::Id;
pub use crate::datatypes::io::IO;
pub use crate::datatypes::lens::Lens;
pub use crate::datatypes::prism::Prism;
pub use crate::datatypes::reader::Reader;
pub use crate::datatypes::state::State;
pub use crate::datatypes::validated::{NonEmptyErrors, Validated};
pub use crate::datatypes::writer::Writer;
