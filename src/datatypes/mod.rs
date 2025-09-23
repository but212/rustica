//! Implementations of functional data types.
//!
//! This module contains concrete implementations of common functional
//! programming data types and containers, each with appropriate trait
//! implementations.

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
