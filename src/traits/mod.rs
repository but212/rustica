//! Functional programming traits and abstractions.
//!
//! This module contains various traits that define core concepts and abstractions
//! in functional programming. These traits provide a foundation for implementing
//! functional programming patterns and techniques in Rust.

/// Basic functional programming concepts.
pub mod hkt;
pub mod enhanced_hkt;
pub mod identity;
pub mod pure;
pub mod evaluate;

/// Fundamental functional programming abstractions.
pub mod functor;
pub mod applicative;
pub mod monad;

/// Advanced functional programming concepts.
pub mod bifunctor;
pub mod contravariant_functor;
pub mod comonad;

/// Traits for composition and transformation.
pub mod composable;
pub mod arrow;
pub mod category;

/// Traits for data structures and operations.
pub mod monoid;
pub mod semigroup;
pub mod foldable;
pub mod traversable;