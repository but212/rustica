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
//! - **Alternative**: Choice and failure in computations
//! - **etc.**: Other Type Classes
//!
//! ## Usage Example
//!
//! ```rust
//! use rustica::prelude::traits::*;
//!
//! // Functor: fmap
//! let x = Some(10);
//! let y = x.fmap(|n| n * 2);
//! assert_eq!(y, Some(20));
//!
//! // Monad: bind
//! let m = Some(5);
//! let bound = m.bind(|n| Some(n + 1));
//! assert_eq!(bound, Some(6));
//!
//! // Monoid: combine
//! use rustica::prelude::wrapper::Sum;
//! let a = Sum(3);
//! let b = Sum(4);
//! assert_eq!(a.combine(b), Sum(7));
//! ```
//!
//! See each trait's documentation for more details and advanced usage.

pub use crate::traits::alternative::Alternative;
pub use crate::traits::applicative::Applicative;
pub use crate::traits::bifunctor::Bifunctor;
pub use crate::traits::foldable::Foldable;
pub use crate::traits::functor::Functor;
pub use crate::traits::hkt::HKT;
pub use crate::traits::iso::Iso;
pub use crate::traits::monad::Monad;
#[allow(deprecated)]
pub use crate::traits::monad_error::{ErrorMapper, MonadError};
#[allow(deprecated)]
pub use crate::traits::monad_plus::MonadPlus;
pub use crate::traits::monoid::Monoid;
pub use crate::traits::one::One;
pub use crate::traits::pure::Pure;
pub use crate::traits::semigroup::Semigroup;
