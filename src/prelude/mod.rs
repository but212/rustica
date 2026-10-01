//! Essential types, traits, and error utilities.
//!
//! # Included Modules
//!
//! - [`datatypes`]: Core functional types and optics (`Validated`, `Choice`, `Free`, `Lens`, `Prism`, `Program`, `TryProgram`)
//! - [`traits`]: Algebraic traits (`Semigroup`, `Monoid`)
//! - [`error`]: Context-accumulating error handling
//!
//! # Examples
//!
//! ```rust
//! use rustica::prelude::*;
//!
//! let a = vec![1, 2];
//! let b = vec![3, 4];
//! assert_eq!(a.combine(b), vec![1, 2, 3, 4]);
//!
//! let v1: Validated<i32, &str> = Validated::valid(10);
//! let v2: Validated<i32, &str> = Validated::valid(20);
//! assert_eq!(v1.zip_with(v2, |x, y| x + y), Validated::valid(30));
//!
//! let results = vec![Ok(1), Ok(2), Ok(3)];
//! let ok: Result<Vec<i32>, &str> = results.into_iter().collect();
//! assert_eq!(ok, Ok(vec![1, 2, 3]));
//! ```

pub mod datatypes;
pub mod error;
pub mod traits;

pub use datatypes::*;
pub use error::*;
pub use traits::*;
