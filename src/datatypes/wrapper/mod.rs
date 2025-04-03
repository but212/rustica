//! # Wrapper Types
//!
//! This module provides various wrapper types that implement functional programming patterns.
//!
//! These wrappers add specific behaviors to existing types, particularly implementing
//! algebraic structures like monoids and semigroups.
//!
//! ## Available Wrapper Types
//!
//! - `Sum`: Forms a semigroup under addition
//! - `Product`: Forms a semigroup under multiplication
//! - `Min`: Forms a semigroup under the minimum operation
//! - `Max`: Forms a semigroup under the maximum operation
//! - `First`: Forms a semigroup by taking the first non-None value
//! - `Last`: Forms a semigroup by taking the last non-None value
//! - `Thunk`: A lightweight alternative to BoxedFn with static dispatch
//! - `Value`: A simple value wrapper implementing Evaluate

pub mod first;
pub mod last;
pub mod max;
pub mod memoize;
pub mod min;
pub mod product;
pub mod sum;
pub mod thunk;
pub mod value;
