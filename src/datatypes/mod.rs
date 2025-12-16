//! Implementations of functional data types.
//!
//! This module contains concrete implementations of common functional
//! programming data types and containers, each with appropriate trait
//! implementations.
//!
//! # Overview
//!
//! The data types in this module provide foundational building blocks for
//! functional programming in Rust. Each type implements relevant traits
//! from the `traits` module, enabling composition and transformation.
//!
//! # Available Data Types
//!
//! ## Core Monadic Types
//!
//! - `maybe` - Optional values with `Just(T)` and `Nothing` variants
//! - `either` - Sum type representing one of two possible values (`Left` or `Right`)
//! - `id` - Identity functor/monad, the simplest container
//! - `validated` - Accumulating error handling (unlike `Either` which fails fast)
//!
//! ## Effect Types
//!
//! - `io` - Encapsulates side effects for deferred execution
//! - `reader` - Computations that read from a shared environment
//! - `writer` - Computations that produce a log alongside a value
//! - `state` - Stateful computations with get/put operations
//! - `cont` - Continuation-passing style computations
//!
//! ## Optics
//!
//! - `lens` - Bidirectional accessors for product types (structs)
//! - `prism` - Bidirectional accessors for sum types (enums)
//! - `iso_lens` - Isomorphism combined with lens functionality
//! - `iso_prism` - Isomorphism combined with prism functionality
//!
//! ## Utility Types
//!
//! - `choice` - N-ary sum type for multiple alternatives
//! - `wrapper` - Newtype wrapper for deriving trait implementations
//!
//! ## Async Support
//!
//! - `async_monad` - Async-aware monadic operations (requires `async` feature)
//!
//! # Example
//!
//! ```rust
//! use rustica::datatypes::maybe::Maybe;
//! use rustica::datatypes::either::Either;
//! use rustica::traits::functor::Functor;
//!
//! // Using Maybe for optional values
//! let value = Maybe::Just(42);
//! let doubled = value.fmap(|x| x * 2);
//! assert_eq!(doubled, Maybe::Just(84));
//!
//! // Using Either for error handling
//! let result: Either<String, i32> = Either::Right(10);
//! let incremented = result.fmap(|x| x + 1);
//! assert_eq!(incremented, Either::Right(11));
//! ```

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
