//! Core traits for functional programming abstractions in Rustica.
//!
//! This module provides a comprehensive set of traits that form the foundation
//! of functional programming in Rust. The traits are organized in a hierarchical
//! structure that reflects their mathematical relationships:
//!
//! ```text
//! TypeConstraints
//!      ↓
//!     HKT
//!      ↓
//! Identity ← Composable → Category
//!      ↓          ↓
//!   Functor    Arrow
//!      ↓
//! Applicative
//!      ↓
//!    Monad
//!      ↓
//!   Comonad
//!
//! Semigroup → Monoid
//!
//! Bifunctor   Foldable
//!     ↓          ↓
//! Traversable ← Sequence
//! ```

// Base type system
pub mod hkt;
pub mod identity;
pub mod composable;

pub use hkt::{HKT, TypeConstraints};
pub use identity::Identity;

// Core abstractions
pub mod category;
pub mod arrow;

// Functor hierarchy
pub mod functor;
pub mod contravariant_functor;
pub mod bifunctor;
pub mod applicative;
pub mod monad;
pub mod comonad;

// Algebraic structures
pub mod semigroup;
pub mod monoid;

// Traversal and folding
pub mod foldable;
pub mod traversable;
pub mod sequence;

// Type class foundations
pub mod pure;
pub mod evaluate;