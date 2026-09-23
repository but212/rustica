//!
//! # Rustica Prelude
//!
//! This module provides a convenient re-export of the most essential types, traits,
//! and utilities from the Rustica functional programming library.
//! By importing this prelude, you gain access to the core functional programming abstractions
//! and tools with a single use statement.
//!
//! ## What is included?
//!
//! - **Datatypes**: Core functional types (`Validated`, `Choice`, `Free`, `Lens`, `Prism`, `Program`, `TryProgram`)
//! - **Traits**: Core algebraic traits (`Semigroup`, `Monoid`)
//! - **Error handling**: Context-aware error handling (see `prelude::error`)
//!
//! ## Usage Example
//!
//! ```rust
//! use rustica::prelude::*;
//!
//! // Semigroup combination
//! let a = vec![1, 2];
//! let b = vec![3, 4];
//! assert_eq!(a.combine(b), vec![1, 2, 3, 4]);
//!
//! // Validated error accumulation
//! let v1: Validated<i32, &str> = Validated::valid(10);
//! let v2: Validated<i32, &str> = Validated::valid(20);
//! assert_eq!(v1.zip_with(v2, |x, y| x + y), Validated::valid(30));
//!
//! // Use error utilities
//! let results = vec![Ok(1), Ok(2), Ok(3)];
//! let ok: Result<Vec<i32>, &str> = results.into_iter().collect();
//! assert_eq!(ok, Ok(vec![1, 2, 3]));
//! ```
//!
//! See each submodule for more detailed documentation and examples.

pub mod datatypes;
pub mod error;
pub mod traits;

pub use datatypes::*;
pub use error::*;
pub use traits::*;
