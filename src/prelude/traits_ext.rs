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
//! use rustica::traits::functor::Functor;
//!
//! let x = Some(10);
//! let y = x.fmap(|n| n + 1);
//! assert_eq!(y, Some(11));
//!
//! use rustica::traits::foldable::{Foldable, FoldableExt};
//! let xs = vec![Some(1), Some(2), None];
//! let sum = xs.fold_map(|m| Sum(m.unwrap_or(0)));
//! assert_eq!(sum.into_inner(), 3);
//!
//! use rustica::traits::monoid::MonoidExt;
//! use rustica::traits::semigroup::Semigroup;
//! let vals = vec![1, 2, 3];
//! let total = vals.iter().cloned().map(Sum).fold(Sum(0), |a, b| a.combine_owned(b));
//! assert_eq!(total.into_inner(), 6);
//! ```

pub use crate::traits::foldable::FoldableExt;
pub use crate::traits::functor::FunctorExt;
pub use crate::traits::iso::IsoExt;
pub use crate::traits::monoid::MonoidExt;
pub use crate::traits::pure::PureExt;
pub use crate::traits::semigroup::SemigroupExt;
