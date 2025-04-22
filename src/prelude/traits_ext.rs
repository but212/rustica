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
//! use rustica::prelude::wrapper::*;
//! use rustica::datatypes::maybe::Maybe;
//! use rustica::traits::functor::Functor;
//!
//! let x = Maybe::Just(10);
//! let y = x.fmap(|n| n + 1);
//! assert_eq!(y, Maybe::Just(11));
//!
//! use rustica::traits::foldable::{Foldable, FoldableExt};
//! let xs = vec![Maybe::Just(1), Maybe::Just(2), Maybe::Nothing];
//! let sum = xs.fold_map(|m| Sum(m.unwrap_or(0)));
//! assert_eq!(sum.0, 3);
//!
//! use rustica::traits::monoid::MonoidExt;
//! use rustica::traits::semigroup::Semigroup;
//! let vals = vec![1, 2, 3];
//! let total = vals.iter().cloned().map(Sum).fold(Sum(0), |a, b| a.combine_owned(b));
//! assert_eq!(total.0, 6);
//! ```

pub use crate::traits::contravariant_functor::ContravariantFunctorExt;
pub use crate::traits::evaluate::EvaluateExt;
pub use crate::traits::foldable::FoldableExt;
pub use crate::traits::functor::FunctorExt;
pub use crate::traits::identity::IdentityExt;
pub use crate::traits::iso::IsoExt;
pub use crate::traits::monoid::MonoidExt;
pub use crate::traits::pure::PureExt;
pub use crate::traits::semigroup::SemigroupExt;
