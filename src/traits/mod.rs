//! Rustica's Category Theory Trait Hierarchy
//!
//! This module defines the core traits that form the foundation of Rustica's
//! functional programming abstractions. The traits are organized in a hierarchy
//! that follows category theory principles:
//!
//! ```text
//! Base Traits:
//! HKT → TypeOps (foundation for type-level programming)
//!
//! Core Category Theory:
//! HKT → Identity → Functor → Applicative → Monad
//!  ↓
//! Composable → Category → Arrow
//!
//! Algebraic Structures:
//! Semigroup → Monoid
//!
//! Traversal:
//! Bifunctor   Foldable
//!     ↓          ↓
//! Traversable ← Sequence
//! ```
//!
//! Each trait in this hierarchy builds upon its predecessors, adding new
//! capabilities while maintaining the laws and properties of its parent traits.

// Base type system
pub mod hkt;
pub mod identity;
pub mod composable;

// Core category theory
pub mod functor;
pub mod category;
pub mod arrow;
pub mod applicative;
pub mod monad;
pub mod contravariant_functor;

// Algebraic structures
pub mod semigroup;
pub mod monoid;

// Traversal
pub mod bifunctor;
pub mod foldable;
pub mod traversable;
pub mod sequence;

// Natural transformations
pub mod natural;

// Type class operations
pub mod pure;
pub mod evaluate;
pub mod comonad;