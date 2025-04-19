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
//! rustica = "0.6"
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
/// - `Monoid`: Types that can be combined with an identity element
#[macro_use]
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
    // Core data types are always included

    /// Either type for representing one of two possible values.
    ///
    /// Useful for error handling and branching computations.
    pub mod either;

    /// Identity monad implementation.
    pub mod id;

    /// Maybe type (equivalent to Option) with additional functional capabilities.
    pub mod maybe;

    // Wrapper types for semigroups and monoids
    /// Wrapper types for working with semigroups and monoids.
    pub mod wrapper;

    /// Validated type for accumulating multiple errors.
    pub mod validated;

    /// Writer monad for computations that produce values along with a log.
    pub mod writer;

    /// Reader monad for computations that read from a shared environment.
    pub mod reader;

    /// State monad for computations that maintain and modify state.
    pub mod state;

    /// Prism implementation for focusing on particular variants of a sum type.
    pub mod prism;

    /// Prism implementation for focusing on particular variants of a sum type.
    pub mod iso_prism;

    /// Lens implementation for focusing on parts of product types.
    pub mod lens;

    /// IsoLens implementation for focusing on parts of product types.
    pub mod iso_lens;

    /// Choice type representing multiple alternatives.
    pub mod choice;

    /// Async monad for asynchronous computations.
    #[cfg(feature = "async")]
    pub mod async_monad;

    /// IO monad for safely handling side effects.
    pub mod io;

    /// Continuation monad for expressing computations with continuations.
    pub mod cont;
}

/// Monad transformers and related utilities.
///
/// Monad transformers allow combining the effects of multiple monads,
/// such as adding error handling to stateful computations or adding
/// state to asynchronous operations.
pub mod transformers;

/// Convenient re-exports of commonly used items.
///
/// This module re-exports the most frequently used traits, types, and functions
/// from the library, allowing users to import them with a single use statement.
pub mod prelude {
    // Core traits
    pub use crate::traits::alternative::Alternative;
    pub use crate::traits::applicative::Applicative;
    pub use crate::traits::composable::Composable;
    pub use crate::traits::foldable::Foldable;
    pub use crate::traits::functor::Functor;
    pub use crate::traits::hkt::{BinaryHKT, HKT};
    pub use crate::traits::identity::Identity;
    pub use crate::traits::monad::Monad;
    pub use crate::traits::monoid::Monoid;
    pub use crate::traits::pure::Pure;
    pub use crate::traits::semigroup::Semigroup;

    // Monad transformer trait
    pub use crate::transformers::MonadTransformer;

    // Monad transformers (advanced)
    pub use crate::transformers::cont_t::ContT;
    pub use crate::transformers::reader_t::ReaderT;
    pub use crate::transformers::state_t::StateT;
    pub use crate::transformers::writer_t::WriterT;

    // Core datatypes
    pub use crate::datatypes::choice::Choice;
    pub use crate::datatypes::either::Either;
    pub use crate::datatypes::id::Id;
    pub use crate::datatypes::maybe::Maybe;
    pub use crate::datatypes::reader::Reader;
    pub use crate::datatypes::state::State;
    pub use crate::datatypes::validated::Validated;
    pub use crate::datatypes::writer::Writer;

    // Wrapper types
    pub use crate::datatypes::wrapper::first::First;
    pub use crate::datatypes::wrapper::last::Last;

    // Feature-gated: async monad
    #[cfg(feature = "async")]
    pub use crate::datatypes::async_monad::AsyncM;
}
