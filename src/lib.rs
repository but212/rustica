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
//! - Practical data types such as `Validated`, `Choice`, and `Id`
//! - Optics for data manipulation via `Lens` and `Prism`
//! - Composable operations for error handling and data transformation
//! - Advanced monad transformers: `StateT`, `ReaderT`, `ContT`
//!
//! ## Getting Started
//!
//! Add Rustica to your `Cargo.toml`:
//!
//! ```toml
//! [dependencies]
//! rustica = "0.14.0"
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
//! // With Result for error handling
//! let success: Result<i32, String> = Ok(42);
//! let mapped: Result<String, String> = success.fmap(|n| n.to_string());
//! assert_eq!(mapped, Ok("42".to_string()));
//! ```
//!
//! ### Error Handling with Validated
//!
//! ```rust
//! use rustica::datatypes::validated::Validated;
//! use rustica::traits::applicative::Applicative;
//! use rustica::traits::functor::Functor;
//!
//! fn validate_name(name: &str) -> Validated<String, String> {
//!     if name.len() >= 2 {
//!         Validated::valid(name.to_string())
//!     } else {
//!         Validated::invalid("Name too short".to_string())
//!     }
//! }
//!
//! fn validate_email(email: &str) -> Validated<String, String> {
//!     if email.contains('@') {
//!         Validated::valid(email.to_string())
//!     } else {
//!         Validated::invalid("Invalid email format".to_string())
//!     }
//! }
//!
//! // Collect all validation errors
//! let name = validate_name("A");
//! let email = validate_email("invalid-email");
//!
//! // Combine validations and format the result only when both are valid
//! let format_user = |n: &String, e: &String| format!("User: {n}, Email: {e}");
//! let combined = Validated::<String, String>::lift2(format_user, &name, &email);
//! assert!(combined.is_invalid());
//! assert_eq!(combined.unwrap_invalid().len(), 2); // Both errors are collected
//! ```
//!
//! ## Feature Flags
//!
//! Rustica provides several feature flags to customize the library for your needs:
//!
//! - `full`: Enables all optional features (`async` + `serde`)
//! - `async`: Enables async monad implementation (`AsyncM`)
//! - `serde`: Enables serialization/deserialization support
//!
//! ## Structure
//!
//! The library is organized into the following main components:
//!
//! - `traits`: Fundamental traits for functional programming concepts
//! - `datatypes`: Implementations of various functional data types
//! - `transformers`: Monad transformers and related utilities
//! - `error`: Composable error handling utilities
//! - `pvec`: Persistent vector implementation with structural sharing
//! - `category`: Category theory abstractions and function composition
//! - `prelude`: A convenient module that re-exports commonly used items
//!
//! ## API Removal Contract Tests
//!
//! The following doctests verify at compile time that deprecated and redundant APIs
//! removed in 0.14.0 or in the unreleased breaking changes can no longer be imported or called:
//!
//! ```compile_fail
//! // Maybe has been removed in 0.14.0 (use Option instead)
//! use rustica::datatypes::maybe::Maybe;
//! ```
//!
//! ```compile_fail
//! // Either has been removed in 0.14.0 (use Result or either crate instead)
//! use rustica::datatypes::either::Either;
//! ```
//!
//! ```compile_fail
//! // Comonad trait has been removed in 0.14.0 (use Id inherent methods)
//! use rustica::traits::comonad::Comonad;
//! ```
//!
//! ```compile_fail
//! // Arrow trait has been removed in 0.14.0 (use FunctionCategory inherent methods)
//! use rustica::traits::arrow::Arrow;
//! ```
//!
//! ```compile_fail
//! // Category trait has been removed in 0.14.0 (use FunctionCategory inherent methods)
//! use rustica::traits::category::Category;
//! ```
//!
//! ```compile_fail
//! // Evaluate trait has been removed in 0.14.0 (use Thunk::evaluate or IO::run)
//! use rustica::traits::evaluate::Evaluate;
//! ```
//!
//! ```compile_fail
//! // Memoizer wrapper has been removed in 0.14.0
//! use rustica::datatypes::wrapper::memoizer::Memoizer;
//! ```
//!
//! ```compile_fail
//! // ErrorPipeline has been removed in 0.14.0
//! use rustica::error::ErrorPipeline;
//! ```
//!
//! ```compile_fail
//! // Pipeline<T> has been removed in 0.14.0
//! use rustica::utils::transform_utils::Pipeline;
//! ```
//!
//! ```compile_fail
//! // IsoLens has been removed in the unreleased breaking changes
//! use rustica::datatypes::iso_lens::IsoLens;
//! ```
//!
//! ```compile_fail
//! // IsoPrism has been removed in the unreleased breaking changes
//! use rustica::datatypes::iso_prism::IsoPrism;
//! ```
//!
//! ```compile_fail
//! // Lens::compose is removed in the unreleased changes (use Lens::then)
//! use rustica::datatypes::lens::Lens;
//! let first = Lens::new(
//!     |value: &i32| *value,
//!     |_: i32, value: i32| value,
//! );
//! let second = Lens::new(
//!     |value: &i32| *value,
//!     |_: i32, value: i32| value,
//! );
//! let _ = first.compose(second);
//! ```
//!
//! ```compile_fail
//! // pipeline_result is removed in the unreleased changes (use Iterator::try_fold)
//! use rustica::utils::hkt_utils::pipeline_result;
//! ```
//!
//! ```compile_fail
//! // Prism::compose is removed in the unreleased changes (use Prism::then)
//! use rustica::datatypes::prism::Prism;
//! let first = Prism::new(
//!     |value: &i32| Some(*value),
//!     |value: &i32| *value,
//! );
//! let second = Prism::new(
//!     |value: &i32| Some(*value),
//!     |value: &i32| *value,
//! );
//! let _ = first.compose(second);
//! ```
//!
//! ```compile_fail
//! // PersistentVector::take has been removed in 0.14.0
//! use rustica::pvec::PersistentVector;
//! let v = PersistentVector::<i32>::new();
//! let _ = v.take(1);
//! ```
//!
//! ```compile_fail
//! // PersistentVector::skip has been removed in 0.14.0
//! use rustica::pvec::PersistentVector;
//! let v = PersistentVector::<i32>::new();
//! let _ = v.skip(1);
//! ```
//!
//! ```compile_fail
//! // ReaderT now rejects a base monad whose source is not its value type.
//! use rustica::transformers::ReaderT;
//! let _: Option<ReaderT<(), Option<i32>, String>> = None;
//! ```
//!
//! ```compile_fail
//! // Min and Max are semigroups; they do not provide a fabricated Monoid identity.
//! use rustica::datatypes::wrapper::min::Min;
//! use rustica::traits::monoid::Monoid;
//! let _ = Min::<i32>::empty();
//! ```
//!
//! ```compile_fail
//! use rustica::datatypes::wrapper::max::Max;
//! use rustica::traits::monoid::Monoid;
//! let _ = Max::<i32>::empty();
//! ```
//!
//! ```compile_fail
//! // Result has no lawful MonadPlus zero for an arbitrary error type.
//! use rustica::traits::monad_plus::MonadPlus;
//! let _: Result<i32, String> = Result::<i32, String>::mzero();
//! ```
//!
//! ```compile_fail
//! // HKTType was an unused phantom wrapper; use HKT directly.
//! use rustica::traits::hkt::HKTType;
//! ```
//!
//! ```compile_fail
//! // PureType was an unused phantom wrapper; use Pure or PureExt directly.
//! use rustica::traits::pure::PureType;
//! ```
//!
//! ```compile_fail
//! // StateT no longer exposes non-executable Pure/LiftM variants.
//! use rustica::transformers::StateT;
//! let _: StateT<i32, Option<(i32, i32)>, i32> = StateT::Pure(1);
//! ```
//!
//! ```compile_fail
//! use rustica::transformers::StateT;
//! let _: StateT<i32, Option<(i32, i32)>, i32> = StateT::LiftM(Some((0, 1)));
//! ```
//!
//! ```compile_fail
//! // Impossible error variants were removed.
//! use rustica::datatypes::error::ChoiceError;
//! let _ = ChoiceError::EmptyChoice;
//! ```
//!
//! ```compile_fail
//! // Choice construction is fallible when the input may be empty.
//! use rustica::datatypes::choice::Choice;
//! let _: Choice<i32> = vec![].into();
//! ```
//!
//! ```compile_fail
//! use rustica::datatypes::choice::Choice;
//! let _: Choice<i32> = std::iter::empty().collect();
//! ```
//!
//! ```compile_fail
//! // NonEmptyErrors no longer panics through FromIterator on empty input.
//! use rustica::datatypes::validated::NonEmptyErrors;
//! let _: NonEmptyErrors<i32> = std::iter::empty().collect();
//! ```
//!
//! ```compile_fail
//! use rustica::pvec::PVecError;
//! let _ = PVecError::InvalidRange { start: 2, end: 1 };
//! ```
//!
//! ```compile_fail
//! use rustica::datatypes::io::IOError;
//! let _ = IOError::ValueNotSet;
//! ```
//!
//! ```compile_fail
//! // Result already provides the former ErrorOps operations.
//! use rustica::error::ErrorOps;
//! ```
//!
//! ```compile_fail
//! // Use Iterator::collect instead of stdlib wrappers.
//! use rustica::error::sequence;
//! ```
//!
//! ```compile_fail
//! use rustica::error::traverse;
//! ```
//!
//! ```compile_fail
//! // Use From and map_err for error conversions.
//! use rustica::error::result_to_validated;
//! ```
//!
//! ```compile_fail
//! use rustica::error::wrap_in_composable_result;
//! ```
//!
//! ```compile_fail
//! use rustica::datatypes::validated::Validated;
//! let _ = Validated::<&str, i32>::from_result_owned(Ok(1));
//! ```
//!
//! ```compile_fail
//! // Empty/stdlib-only utility modules and orphan aliases were removed.
//! use rustica::utils::categorical_utils;
//! ```
//!
//! ```compile_fail
//! use rustica::utils::functions::id;
//! ```
//!
//! ```compile_fail
//! use rustica::datatypes::cont::ContFn;
//! ```
//!
//! ```compile_fail
//! use rustica::transformers::reader_t::ReaderCombineFn;
//! ```

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
pub mod pvec;

/// Implementations of functional data types.
///
/// This module contains concrete implementations of common functional
/// programming data types and containers, each with appropriate trait
/// implementations.
pub mod datatypes;

/// Monad transformers and related utilities.
///
/// Monad transformers allow combining the effects of multiple monads,
/// such as adding error handling to stateful computations or adding
/// state to asynchronous operations.
pub mod transformers;

/// Category theory abstractions.
pub mod category;

/// Error handling utilities.
pub mod error;

/// Convenient re-exports of commonly used items.
pub mod prelude;
