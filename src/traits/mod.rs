//! Functional programming traits and abstractions.
//!
//! This module contains various traits that define core concepts and abstractions
//! in functional programming. These traits provide a foundation for implementing
//! functional programming patterns and techniques in Rust.
//!
//! ## Trait Categories
//!
//! The traits are organized into several conceptual categories:
//!
//! - **Core Abstractions**: Fundamental abstractions like Functor, Applicative, and Monad
//! - **Composition Traits**: Traits related to function composition and transformation
//! - **Data Structure Traits**: Traits for working with and combining data structures
//! - **Advanced Abstractions**: More specialized abstractions for advanced functional programming
//!
//! ## Getting Started
//!
//! If you're new to functional programming, start with Functor, Applicative, and Monad
//! which form the foundation of most functional programming patterns.

/// Higher-kinded type abstractions for generic programming.
pub mod hkt;
/// Creation of values in a computational context.
pub mod pure;

/// Function application within a computational context.
pub mod applicative;
/// Structure-preserving mapping over computational contexts.
pub mod functor;
/// Sequential computation with context binding.
pub mod monad;
/// Error handling within monadic contexts.
pub mod monad_error;

/// Mapping over two-type data structures.
pub mod bifunctor;

/// Reduction of data structures to a single value.
///
/// This module provides the Foldable trait which represents data structures that can be "folded" into a summary value.
pub mod foldable;
/// Combinable types with identity elements.
///
/// This module provides the Monoid trait, which extends Semigroup to add an identity element.
/// The MonoidExt trait adds extension methods to all types implementing Monoid.
pub mod monoid;
/// Combinable types without identity elements.
pub mod semigroup;

/// Choice between alternative computations.
pub mod alternative;

/// Isomorphism between types.
///
/// This module provides the Iso trait which represents isomorphisms between types.
pub mod iso;

/// Multiplicative identity element.
pub mod one;
pub use one::One;
