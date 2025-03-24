//! Functional programming traits and abstractions.
//!
//! This module contains various traits that define core concepts and abstractions
//! in functional programming. These traits provide a foundation for implementing
//! functional programming patterns and techniques in Rust.

pub mod evaluate;
/// Basic functional programming concepts.
pub mod hkt;
pub mod identity;
pub mod pure;

pub mod applicative;
pub mod error_mapper;
/// Fundamental functional programming abstractions.
pub mod functor;
pub mod monad;
pub mod monad_error;
pub mod monad_plus;

pub mod bifunctor;
pub mod comonad;
pub mod contravariant_functor;

pub mod arrow;
pub mod category;
/// Traits for composition and transformation.
pub mod composable;

pub mod foldable;
pub mod monoid;
/// Traits for data structures and operations.
pub mod semigroup;
pub mod traversable;

pub mod alternative;
pub mod distributive;
pub mod divisible;
pub mod iso;
pub mod natural_transformation;
pub mod profunctor;
pub mod representable;
