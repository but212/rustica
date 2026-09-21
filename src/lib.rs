#![doc = include_str!("../README.md")]
#![cfg_attr(test, allow(deprecated))]

/// Core traits for functional programming abstractions.
///
/// This module contains the fundamental type classes and concepts from
/// functional programming, implemented as Rust traits. Key traits include:
///
/// - `Functor`: Types that can be mapped over
/// - `Applicative`: Functors with application capabilities
/// - `Monad`: Monadic types with binding operations
/// - `Monoid`: Types that can be combined with an identity element
pub mod traits;

/// Persistent vector implementation with structural sharing.
///
/// A high-performance, immutable vector implementation that preserves
/// previous versions through structural sharing.
#[cfg(feature = "pvec")]
#[deprecated(
    since = "0.18.0",
    note = "PersistentVector is deprecated in favor of specialized persistent collection crates like `imbl`. It will be removed in v0.19.0."
)]
pub mod pvec;

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
