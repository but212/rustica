//!
//! Prelude: Core Functional Data Types
//!
//! This module re-exports Rustica's core functional data types for expressive, type-safe programming.
//! These types encode common functional programming patterns such as optionality, error handling,
//! validation, state, dependency injection, and more.
//!
//! ## Included Data Types
//!
//! - [`Maybe`]: Optional values (like Option)
//! - [`Either`]: Sum type for error handling or branching
//! - [`Validated`]: Error accumulation and validation
//! - [`Choice`]: Generalized sum type
//! - [`State`]: Composable stateful computations
//! - [`Reader`]: Dependency injection/context passing
//! - [`Writer`]: Output accumulation (logging, etc.)
//! - [`Id`]: Identity functor
//! - [`IO`]: Side-effectful computations
//! - [`Cont`]: Continuation-passing style
//! - [`Lens`, `Prism`, `IsoLens`, `IsoPrism`]: Optics for immutable data access
//!
//! ## Usage Example
//!
//! ```rust
//! use rustica::prelude::datatypes::*;
//! use rustica::traits::functor::Functor;
//!
//! let x = Maybe::Just(42);
//! let y = x.fmap(|n| n + 1);
//! assert_eq!(y, Maybe::Just(43));
//!
//! let e: Either<&str, i32> = Either::right(10);
//! let mapped = e.fmap(|n| n * 2);
//! assert_eq!(mapped, Either::right(20));
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
pub use crate::datatypes::either::Either;
pub use crate::datatypes::id::Id;
pub use crate::datatypes::io::IO;
pub use crate::datatypes::iso_lens::IsoLens;
pub use crate::datatypes::iso_prism::IsoPrism;
pub use crate::datatypes::lens::Lens;
pub use crate::datatypes::maybe::Maybe;
pub use crate::datatypes::prism::Prism;
pub use crate::datatypes::reader::Reader;
pub use crate::datatypes::state::State;
pub use crate::datatypes::validated::Validated;
pub use crate::datatypes::writer::Writer;
