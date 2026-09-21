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
//! - **Datatypes**: Core functional types (Validated, Choice, Free, etc.)
//! - **Traits**: Functor, Applicative, Monad, Monoid, and many more
//! - **Error handling**: Context-aware error handling (see `prelude::error`)
//!
//! ## Usage Example
//!
//! ```rust
//! use rustica::prelude::*;
//!
//! // Use Option and Functor
//! let x = Some(10);
//! let y = x.fmap(|n| n * 2);
//! assert_eq!(y, Some(20));
//!
//! // Use Result and Monad
//! let e: Result<i32, &str> = Ok(5);
//! let bound = e.bind(|n| Ok(n + 1));
//! assert_eq!(bound, Ok(6));
//! // Use error utilities
//! use rustica::prelude::error::*;
//! let results = vec![Ok(1), Ok(2), Ok(3)];
//! let ok: Result<Vec<i32>, &str> = results.into_iter().collect();
//! assert_eq!(ok, Ok(vec![1, 2, 3]));
//! ```
//!
//! See each submodule for more detailed documentation and examples.

#![allow(deprecated)]

pub mod datatypes;
pub mod error;
pub mod traits;

pub use datatypes::*;
pub use error::*;
pub use traits::*;
