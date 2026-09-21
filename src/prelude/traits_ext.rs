//! Prelude: Trait Extensions
//!
//! This module re-exports extension traits for Rustica's core functional abstractions.
//! These extension traits provide ergonomic methods and utility functions for working
//! with functors, monoids, foldables, and more.
//!
//! # Example Usage
//!
//! ```rust
//! use rustica::prelude::traits_ext::*;
//! use rustica::traits::functor::Functor;
//!
//! let x = Some(10);
//! let y = x.fmap(|n| n + 1);
//! assert_eq!(y, Some(11));
//! ```

pub use crate::traits::foldable::FoldableExt;
pub use crate::traits::functor::FunctorExt;
pub use crate::traits::monoid::MonoidExt;
pub use crate::traits::pure::PureExt;
pub use crate::traits::semigroup::SemigroupExt;
