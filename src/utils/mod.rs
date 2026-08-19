//! # Utility Functions and Helpers
//!
//! This module provides a collection of utility functions and types that support
//! functional programming patterns in Rust. These utilities enhance the core traits
//! and datatypes with practical tools for common operations.
//!
//! ## Module Structure
//!
//! The utilities are organized into four main categories:
//!
//! ### Categorical Utilities (`categorical_utils`)
//!
//! Category theory-inspired utilities designed for Rust's type system:
//!
//! - Result bifunctor mapping helper (`bimap_result`)
//! - Function composition utilities (`compose`, `pipe`)
//! - Following categorical laws
//!
//! ### Error Handling Utilities (`crate::error`)
//!
//! Error handling utilities have been consolidated under the top-level `crate::error` module.
//! Prefer importing from `rustica::error` or `rustica::prelude::error`.
//!
//! ### Higher-Kinded Type Utilities (`hkt_utils`)
//!
//! Generic functions and transformations for working with higher-kinded types:
//!
//! - Composition utilities for functions and transformations
//! - Pipeline operations for chaining computations
//! - Context-aware operations like `fan_out`
//!
//! ### Transformation Utilities (`transform_utils`)
//!
//! Tools for data transformation and operation chaining:
//!
//! - `transform_all` for applying transformations to collections
//! - `transform_chain` for optional transformations
//! - `Pipeline` type for fluent transformation chaining

/// Higher-kinded type utilities for generic programming.
///
/// This module provides functions and utilities for working with higher-kinded
/// types and generic operations, including:
///
/// - Pipeline operations for chaining computations
/// - Lifting and mapping functions for different contexts
/// - Collection operations that preserve context
/// - Function composition utilities
pub mod hkt_utils;

/// Data transformation utilities for functional operations.
///
/// This module provides utilities for transforming data in a functional style,
/// including:
///
/// - Transformation operations for functorial types
/// - Pipeline abstractions for chaining operations
/// - Transformation utilities for collections
pub mod transform_utils;

/// Category theory-inspired utilities for functional programming.
///
/// This module provides utility functions based on category theory concepts,
/// specifically designed for Rust's type system and ownership model. These
/// utilities extend common operations on `Option`, `Result`, and other types
/// while maintaining categorical correctness and type safety.
///
/// Key features include:
///
/// - Result bifunctor mapping for transforming success and error values
/// - Function composition utilities for building complex operations
pub mod categorical_utils;

/// Basic function combinators and utilities.
///
/// This module provides fundamental functional programming utilities including:
///
/// - `id`: The identity function (identity morphism)
/// - `const_fn`: Create constant functions
///
/// These are the building blocks for functional composition and should be
/// available throughout the codebase.
pub mod functions;
