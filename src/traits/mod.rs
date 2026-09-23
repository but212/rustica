//! Functional programming traits and abstractions.
//!
//! This module contains core algebraic abstractions for functional programming in Rust:
//!
//! - [`Semigroup`](crate::traits::semigroup::Semigroup): Combinable types without identity elements
//! - [`Monoid`](crate::traits::monoid::Monoid): Combinable types with identity elements

/// Combinable types with identity elements.
///
/// This module provides the Monoid trait, which extends Semigroup to add an identity element.
pub mod monoid;
/// Combinable types without identity elements.
pub mod semigroup;
