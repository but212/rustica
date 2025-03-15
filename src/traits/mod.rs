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
/// Fundamental functional programming abstractions.
pub mod functor;
pub mod monad;

/// Advanced functional programming concepts.
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
