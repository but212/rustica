//!
//! # Rustica Prelude
//!
//! This module provides a convenient re-export of the most essential types, traits, wrappers,
//! utilities, and transformers from the Rustica functional programming library.
//! By importing this prelude, you gain access to the core functional programming abstractions
//! and tools with a single use statement.
//!
//! ## What is included?
//!
//! - **Datatypes**: Core functional types (Maybe, Either, Validated, etc.)
//! - **Traits**: Functor, Applicative, Monad, Monoid, and many more
//! - **Trait Extensions**: Ergonomic extension traits for functional operations
//! - **Wrappers**: Newtype wrappers for monoidal/semigroup operations
//! - **Utilities**: Error handling, higher-kinded type tools, transformation utilities
//! - **Transformers**: Monad transformers (StateT, ReaderT, etc.)
//!
//! ## Usage Example
//!
//! ```rust
//! use rustica::prelude::*;
//!
//! // Use Maybe and Functor
//! use rustica::datatypes::maybe::Maybe;
//! let x = Maybe::Just(10);
//! let y = x.fmap(|n| n * 2);
//! assert_eq!(y, Maybe::Just(20));
//!
//! // Use Either and Monad
//! use rustica::datatypes::either::Either;
//! let e: Either<&str, i32> = Either::right(5);
//! let bound = e.bind(|n| Either::right(n + 1));
//! assert_eq!(bound, Either::right(6));
//!
//! // Use wrapper types and monoid
//! use rustica::prelude::wrapper::*;
//! let a = Sum(3);
//! let b = Sum(4);
//! assert_eq!(a.combine(&b).unwrap(), 7);
//!
//! // Use error utilities
//! use rustica::prelude::utils::*;
//! let results = vec![Ok(1), Ok(2), Ok(3)];
//! let ok: Result<Vec<i32>, &str> = sequence(results);
//! assert_eq!(ok, Ok(vec![1, 2, 3]));
//! ```
//!
//! See each submodule for more detailed documentation and examples.

pub mod category;
pub mod datatypes;
pub mod traits;
pub mod traits_ext;
pub mod transformers;
pub mod utils;
pub mod wrapper;
pub mod error;

pub use category::*;
pub use datatypes::*;
pub use traits::*;
pub use traits_ext::*;
pub use transformers::*;
pub use utils::*;
pub use wrapper::*;
pub use error::*;
