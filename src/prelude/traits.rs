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
//! // Semigroup: combine
//! let a = vec![1, 2];
//! let b = vec![3, 4];
//! assert_eq!(a.combine(b), vec![1, 2, 3, 4]);
//! ```
//!
//! See each trait's documentation for more details and advanced usage.

#![allow(deprecated)]

pub use crate::traits::applicative::Applicative;
pub use crate::traits::foldable::Foldable;
pub use crate::traits::functor::Functor;
pub use crate::traits::hkt::HKT;
pub use crate::traits::monad::Monad;
pub use crate::traits::monoid::Monoid;
pub use crate::traits::pure::Pure;
pub use crate::traits::semigroup::Semigroup;
