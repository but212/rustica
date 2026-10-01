#![doc = include_str!("../README.md")]
#![no_std]

extern crate alloc;

/// Core algebraic abstractions ([`Semigroup`](traits::semigroup::Semigroup), [`Monoid`](traits::monoid::Monoid)).
pub mod traits;

/// Functional data types, optics, and operational monads.
pub mod datatypes;

/// Context-accumulating error handling.
pub mod error;

/// Convenient re-exports of essential types, traits, and utilities.
pub mod prelude;
