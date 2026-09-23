#![doc = include_str!("../README.md")]

/// Core algebraic traits for functional programming.
///
/// This module contains fundamental algebraic abstractions:
///
/// - `Semigroup`: Types that can be combined associatively
/// - `Monoid`: Types that can be combined with an identity element
pub mod traits;

/// Implementations of functional data types.
///
/// This module contains concrete implementations of common functional
/// programming data types and containers, each with appropriate trait
/// implementations.
pub mod datatypes;

/// Error handling utilities.
pub mod error;

/// Convenient re-exports of commonly used items.
pub mod prelude;
