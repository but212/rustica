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
//! - Functor-inspired mapping helpers (`map_option`, `map_result`, `bimap_result`)
//! - Monad-inspired chaining helpers (`flat_map_option`, `flat_map_result`)
//! - Function composition utilities (`compose`, `pipe`)
//! - Collection sequencing operations (`sequence_options`, `sequence_results`)
//! - Following categorical laws
//!
//! ### Error Handling Utilities (`error_utils`)
//!
//! Standardized error handling functions and types that work with functional
//! programming abstractions:
//!
//! - Type-class `WithError` for error transformation
//! - Conversion functions between different error handling types (`Result`, `Either`, `Validated`)
//! - Collection operations like `sequence` and `traverse` for error handling
//! - `AppError` for contextual error reporting
//!
//! ### Higher-Kinded Type Utilities (`hkt_utils`)
//!
//! Generic functions and transformations for working with higher-kinded types:
//!
//! - Composition utilities for functions and transformations
//! - Pipeline operations for chaining computations
//! - Collection utilities like `filter_map`, `fan_out`, and `zip_with`
//!
//! ### Transformation Utilities (`transform_utils`)
//!
//! Tools for data transformation and operation chaining:
//!
//! - `transform_all` for applying transformations to collections
//! - `transform_chain` for optional transformations
//! - `Pipeline` type for fluent transformation chaining

/// Error handling utilities for working with functional programming patterns.
///
/// This module provides standardized error handling functions that work with
/// the functional programming abstractions in Rustica, including:
///
/// - Error mapping and transformation
/// - Conversion between error types
/// - Collection operations for error handling
/// - Structured error types with context
pub mod error_utils;

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
/// - Functor-inspired mapping helpers for structure-preserving transformations
/// - Monad-inspired chaining helpers for sequencing computations with context
/// - Function composition utilities for building complex operations
/// - Collection utilities for working with sequences of optional/failable values
pub mod categorical_utils;
