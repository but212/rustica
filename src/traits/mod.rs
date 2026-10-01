#![doc = include_str!("../../docs/traits/README.md")]


/// Combinable types with identity elements.
///
/// This module provides the Monoid trait, which extends Semigroup to add an identity element.
pub mod monoid;
/// Combinable types without identity elements.
pub mod semigroup;
