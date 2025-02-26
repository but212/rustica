//! Functional programming data types and abstractions.
//!
//! This module contains various data types and structures commonly used in
//! functional programming paradigms. Each submodule implements a specific
//! data type or concept, providing a rich set of tools for functional
//! programming in Rust.

/// The Either type, representing a value of one of two possible types.
pub mod either;

/// The State monad, for computations that carry state.
pub mod state;

/// The Validated type, for accumulating multiple errors.
pub mod validated;

/// The Writer monad, for computations that produce a log along with a value.
pub mod writer;

/// The Reader monad, for computations with a shared environment.
pub mod reader;

/// The Maybe type, representing optional values.
pub mod maybe;

/// The Cont monad, for continuation-passing style programming.
pub mod cont;

/// Asynchronous monad for handling asynchronous computations.
pub mod async_monad;

/// The IO monad, for handling input/output operations.
pub mod io;

/// The Choice type, representing a primary value with alternatives.
pub mod choice;

/// Lenses for focusing on parts of data structures.
pub mod lens;

/// Prisms for handling sum types.
pub mod prism;

/// The Identity functor.
pub mod id;