//!
//! Prelude: Core Functional Traits
//!
//! This module re-exports Rustica's core functional programming traits, making it easy to bring
//! all the key abstractions into scope with a single import. These traits define the essential
//! type classes and algebraic structures for functional programming in Rust.
//!
//! ## Included Traits
//!
//! - **Functor**: Mapping over values in a context
//! - **Applicative**: Function application in a context
//! - **Monad**: Chaining computations in a context
//! - **Monoid/Semigroup**: Algebraic structures for combination and identity
//! - **Foldable/Traversable**: Folding and traversing data structures
//! - **Alternative/MonadPlus**: Choice and failure in computations
//! - **Arrow/Category/NaturalTransformation**: Abstract computation and morphisms
//! - **etc.**: Other Type Classes
//!
//! ## Usage Example
//!
//! ```rust
//! use rustica::prelude::traits::*;
//! use rustica::datatypes::maybe::Maybe;
//!
//! // Functor: fmap
//! let x = Maybe::Just(10);
//! let y = x.fmap(|n| n * 2);
//! assert_eq!(y, Maybe::Just(20));
//!
//! // Monad: bind
//! let m = Maybe::Just(5);
//! let bound = m.bind(|n| Maybe::Just(n + 1));
//! assert_eq!(bound, Maybe::Just(6));
//!
//! // Monoid: combine
//! use rustica::prelude::wrapper::Sum;
//! let a = Sum(3);
//! let b = Sum(4);
//! assert_eq!(a.combine(&b), Sum(7));
//! ```
//!
//! See each trait's documentation for more details and advanced usage.

pub use crate::traits::alternative::Alternative;
pub use crate::traits::applicative::Applicative;
pub use crate::traits::arrow::Arrow;
pub use crate::traits::bifunctor::Bifunctor;
pub use crate::traits::category::Category;
pub use crate::traits::composable::Composable;
pub use crate::traits::contravariant_functor::ContravariantFunctor;
pub use crate::traits::evaluate::{Evaluate, EvaluateExt};
pub use crate::traits::foldable::Foldable;
pub use crate::traits::functor::Functor;
pub use crate::traits::hkt::HKT;
pub use crate::traits::identity::Identity;
pub use crate::traits::iso::Iso;
pub use crate::traits::monad::Monad;
pub use crate::traits::monad_error::MonadError;
pub use crate::traits::monad_plus::MonadPlus;
pub use crate::traits::monoid::Monoid;
pub use crate::traits::natural_transformation::NaturalTransformation;
pub use crate::traits::pure::Pure;
pub use crate::traits::representable::Representable;
pub use crate::traits::semigroup::Semigroup;
pub use crate::traits::traversable::Traversable;
