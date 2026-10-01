//! Core algebraic traits prelude.
//!
//! Re-exports combination and identity traits.
//!
//! # Included Traits
//!
//! - [`Semigroup`]: Associative binary combination
//! - [`Monoid`]: Associative combination with identity element
//!
//! # Examples
//!
//! ```rust
//! use rustica::prelude::traits::*;
//!
//! let a = vec![1, 2];
//! let b = vec![3, 4];
//! assert_eq!(a.combine(b), vec![1, 2, 3, 4]);
//!
//! let empty: Vec<i32> = Monoid::empty();
//! assert!(empty.is_empty());
//! ```

pub use crate::traits::monoid::Monoid;
pub use crate::traits::semigroup::Semigroup;
