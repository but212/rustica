//! # Rustica
//!
//! Rustica is a comprehensive Rust library that provides functional programming abstractions
//! and utilities, enabling clean, composable, and type-safe code.
//!
//! ## Overview
//!
//! Functional programming emphasizes immutable data, first-class functions, and composable abstractions.
//! Rustica brings these concepts to Rust with a focus on pragmatism and performance, providing:
//!
//! - Type-safe functional abstractions like `Functor`, `Applicative`, and `Monad`
//! - Practical data types such as `Maybe`, `Either`, and `Validated`
//! - Optics for data manipulation via `Lens` and `Prism`
//! - Composable operations for error handling and data transformation
//! - Zero-cost abstractions wherever possible
//! - Advanced monad transformers: `StateT`, `ReaderT`, `WriterT`, `ContT`
//!
//! ## Getting Started
//!
//! Add Rustica to your `Cargo.toml`:
//!
//! ```toml
//! [dependencies]
//! rustica = "0.7"
//! ```
//!
//! Import common traits and types through the prelude:
//!
//! ```rust
//! use rustica::prelude::*;
//! ```
//!
//! ## Examples
//!
//! ### Basic Functor Usage
//!
//! ```rust
//! use rustica::prelude::*;
//!
//! // Using fmap with Option
//! let value: Option<i32> = Some(42);
//! let doubled: Option<i32> = value.fmap(|x| x * 2);
//! assert_eq!(doubled, Some(84));
//!
//! // With Either for error handling
//! let success: Either<String, i32> = Either::right(42);
//! let mapped: Either<String, String> = success.fmap(|n| n.to_string());
//! assert_eq!(mapped.unwrap_right(), "42");
//! ```
//!
//! ### Error Handling with Validated
//!
//! ```rust
//! use rustica::datatypes::validated::Validated;
//! use rustica::traits::applicative::Applicative;
//! use rustica::traits::functor::Functor;
//!
//! fn validate_name(name: &str) -> Validated<Vec<String>, String> {
//!     if name.len() >= 2 {
//!         Validated::valid(name.to_string())
//!     } else {
//!         Validated::invalid(vec!["Name too short".to_string()])
//!     }
//! }
//!
//! fn validate_email(email: &str) -> Validated<Vec<String>, String> {
//!     if email.contains('@') {
//!         Validated::valid(email.to_string())
//!     } else {
//!         Validated::invalid(vec!["Invalid email format".to_string()])
//!     }
//! }
//!
//! // Collect all validation errors
//! let name = validate_name("A");
//! let email = validate_email("invalid-email");
//!
//! // Combine validations and format the result only when both are valid
//! let format_user = |n: &String, e: &String| format!("User: {}, Email: {}", n, e);
//! let combined = Validated::lift2(&name, &email, format_user);
//! assert!(combined.is_invalid());
//! assert_eq!(combined.unwrap_invalid().len(), 2); // Both errors are collected
//! ```
//!
//! ## Feature Flags
//!
//! Rustica provides several feature flags to customize the library for your needs:
//!
//! - `full`: Enables all features below
//! - `pvec`: Includes persistent vector implementation
//! - `async`: Includes async monad implementation
//!
//! ## Structure
//!
//! The library is organized into the following main components:
//!
//! - `traits`: Fundamental traits for functional programming concepts
//! - `datatypes`: Implementations of various functional data types
//! - `transformers`: Monad transformers and related utilities
//! - `utils`: Utility functions and helpers for common operations
//! - `prelude`: A convenient module that re-exports commonly used items
//! - `pvec`: Persistent vector implementation (feature-gated)

/// Core traits for functional programming abstractions.
///
/// This module contains the fundamental type classes and concepts from
/// functional programming, implemented as Rust traits. Key traits include:
///
/// - `Functor`: Types that can be mapped over
/// - `Applicative`: Functors with application capabilities
/// - `Monad`: Monadic types with binding operations
/// - Monoid: Types that can be combined with an identity element
pub mod traits;

/// Utility functions and helpers for common operations.
///
/// This module provides helper functions for error handling, function
/// composition, and other common functional programming patterns.
pub mod utils;

/// Persistent vector implementation with structural sharing.
///
/// A high-performance, immutable vector implementation that preserves
/// previous versions through structural sharing.
#[cfg(feature = "pvec")]
pub mod pvec;

/// Implementations of functional data types.
///
/// This module contains concrete implementations of common functional
/// programming data types and containers, each with appropriate trait
/// implementations.
pub mod datatypes {
    #[cfg(feature = "async")]
    pub mod async_monad;
    pub mod choice;
    pub mod cont;
    pub mod either;
    pub mod id;
    pub mod io;
    pub mod iso_lens;
    pub mod iso_prism;
    pub mod lens;
    pub mod maybe;
    pub mod prism;
    pub mod reader;
    pub mod state;
    pub mod validated;
    pub mod wrapper;
    pub mod writer;
}

/// Monad transformers and related utilities.
///
/// Monad transformers allow combining the effects of multiple monads,
/// such as adding error handling to stateful computations or adding
/// state to asynchronous operations.
pub mod transformers;

/// Convenient re-exports of commonly used items.
pub mod prelude;
