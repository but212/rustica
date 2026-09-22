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
//! - `validated` - Accumulating error handling
//! - `free` - Free monad for DSL construction and deferred interpretation
//! - `operational` - Statically-typed operational monad with command-handler dispatch
//!
//! ## Optics
//!
//! - `lens` - Bidirectional accessors for product types (structs)
//! - `prism` - Bidirectional accessors for sum types (enums)
//!
//! ## Utility Types
//!
//! - `choice` - N-ary sum type for multiple alternatives

pub mod choice;
pub mod free;
pub mod lens;
pub mod operational;
pub mod prism;
pub mod validated;

pub use choice::ChoiceError;
pub use free::FreeError;
pub use validated::ValidatedError;

// Backward-compatibility alias for former datatypes::error module
pub mod error {
    pub use crate::datatypes::choice::ChoiceError;
    pub use crate::datatypes::free::FreeError;
    pub use crate::datatypes::validated::ValidatedError;
}
