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
//! - `id` - Identity functor/monad, the simplest container
//! - `validated` - Accumulating error handling
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
//!
//! Isomorphisms can also induce core lenses and prisms through `Lens::from_iso`
//! and `Prism::from_iso`.
//!
//! ## Utility Types
//!
//! - `choice` - N-ary sum type for multiple alternatives
//! - `wrapper` - Newtype wrapper for deriving trait implementations
//!
//! ## Async Support
//!
//! - `async_monad` - Async-aware monadic operations (requires `async` feature)

#[cfg(feature = "async")]
pub mod async_monad;
pub mod choice;
pub mod cont;
pub mod error;
pub mod id;
pub mod io;
pub mod lens;
pub mod prism;
pub mod reader;
pub mod state;
pub mod validated;
pub mod wrapper;
pub mod writer;
