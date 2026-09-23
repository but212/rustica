//!
//! Prelude: Core Algebraic Traits
//!
//! This module re-exports Rustica's core algebraic traits (`Semigroup` and `Monoid`),
//! making it easy to bring combination and identity abstractions into scope.
//!
//! ## Included Traits
//!
//! - **Semigroup**: Algebraic structures for associative combination
//! - **Monoid**: Semigroups with an identity element
//!
//! ## Usage Example
//!
//! ```rust
//! use rustica::prelude::traits::*;
//!
//! // Semigroup: combine
//! let a = vec![1, 2];
//! let b = vec![3, 4];
//! assert_eq!(a.combine(b), vec![1, 2, 3, 4]);
//!
//! // Monoid: empty
//! let empty: Vec<i32> = Monoid::empty();
//! assert!(empty.is_empty());
//! ```

pub use crate::traits::monoid::Monoid;
pub use crate::traits::semigroup::Semigroup;
