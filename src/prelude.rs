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
//! - **Datatypes**: Core functional types (Validated, Id, Choice, etc.)
//! - **Traits**: Functor, Applicative, Monad, Monoid, and many more
//! - **Trait Extensions**: Ergonomic extension traits for functional operations
//! - **Wrappers**: Newtype wrappers for monoidal/semigroup operations
//! - **Error handling**: Composable errors and helpers (see `prelude::error`)
//! - **Utilities**: Higher-kinded type tools and transformation utilities (see `prelude::utils`)
//! - **Transformers**: Monad transformers (StateT, ReaderT, etc.)
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
//!
//! // Use wrapper types and monoid
//! use rustica::prelude::wrapper::*;
//! let a = Sum(3);
//! let b = Sum(4);
//! assert_eq!(a.combine(&b).unwrap(), 7);
//!
//! // Use error utilities
//! use rustica::prelude::error::*;
//! let results = vec![Ok(1), Ok(2), Ok(3)];
//! let ok: Result<Vec<i32>, &str> = results.into_iter().collect();
//! assert_eq!(ok, Ok(vec![1, 2, 3]));
//! ```
//!
//! See each submodule for more detailed documentation and examples.

pub mod category;
pub mod datatypes;
pub mod error;
pub mod traits;
pub mod traits_ext;
pub mod transformers;
pub mod utils;
pub mod wrapper;

pub use category::*;
pub use datatypes::*;
pub use error::*;
pub use traits::*;
pub use traits_ext::*;
pub use transformers::*;
pub use utils::*;
pub use wrapper::*;
