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
//! - **Core Abstractions**: Fundamental abstractions like `Functor`, `Applicative`, and `Monad`
//! - **Composition Traits**: Traits related to function composition and transformation
//! - **Data Structure Traits**: Traits for working with and combining data structures
//! - **Advanced Abstractions**: More specialized abstractions for advanced functional programming
//!
//! ## Getting Started
//!
//! If you're new to functional programming, start with `Functor`, `Applicative`, and `Monad`
//! which form the foundation of most functional programming patterns.

// ===== Core Evaluation Concepts =====
/// Traits for evaluating and processing data.
pub mod evaluate;
/// Higher-kinded type abstractions for generic programming.
pub mod hkt;
/// Identity and value extraction traits.
pub mod identity;
/// Creation of values in a computational context.
pub mod pure;

// ===== Fundamental Abstractions =====
/// Function application within a computational context.
pub mod applicative;
/// Error mapping and transformation.
pub mod error_mapper;
/// Structure-preserving mapping over computational contexts.
pub mod functor;
/// Sequential computation with context binding.
pub mod monad;
/// Error handling within monadic contexts.
pub mod monad_error;
/// Monads with zero and plus operations.
pub mod monad_plus;

// ===== Related Abstractions =====
/// Mapping over two-type data structures.
pub mod bifunctor;
/// Extracting values from computational contexts.
pub mod comonad;
/// Function mapping in opposite direction.
pub mod contravariant_functor;

// ===== Composition Traits =====
/// Arrow-based computation abstractions.
pub mod arrow;
/// Categorical composition abstractions.
pub mod category;
/// Function composition utilities.
pub mod composable;

// ===== Data Structure Traits =====
/// Reduction of data structures to a single value.
pub mod foldable;
/// Combinable types with identity elements.
pub mod monoid;
/// Combinable types without identity elements.
pub mod semigroup;
/// Traversing data structures with effects.
pub mod traversable;

// ===== Advanced Abstractions =====
/// Choice between alternative computations.
pub mod alternative;
/// Distribution of contexts over structures.
pub mod distributive;
/// Divisible contravariant functors.
pub mod divisible;
/// Isomorphism between types.
pub mod iso;
/// Transformations between functors.
pub mod natural_transformation;
/// Profunctorial abstractions.
pub mod profunctor;
/// Representable functors.
pub mod representable;
