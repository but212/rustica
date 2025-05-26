//! # Wrapper Types
//!
//! This module provides various wrapper types that implement functional programming patterns
//! and algebraic structures. Wrappers enhance existing types with specific behaviors while
//! preserving their original functionality.
//!
//! ## Purpose
//!
//! Wrapper types serve several important purposes in functional programming:
//!
//! 1. **Algebraic Structures**: Implement mathematical structures like monoids and semigroups
//! 2. **Type-Based Operations**: Enable operations based on wrapped type (like Sum, Product)
//! 3. **Deferred Computation**: Allow for lazy evaluation with types like Thunk
//! 4. **Context Addition**: Add additional context or capabilities to basic types
//!
//! ## Available Wrapper Types
//!
//! ### Semigroup Wrappers
//!
//! These wrappers implement the `Semigroup` trait with specific combine operations:
//!
//! - `Sum<T>`: Forms a semigroup under addition (T must support `Add`)
//! - `Product<T>`: Forms a semigroup under multiplication (T must support `Mul`)
//! - `Min<T>`: Forms a semigroup taking the minimum value (T must support `PartialOrd`)
//! - `Max<T>`: Forms a semigroup taking the maximum value (T must support `PartialOrd`)
//!
//! ### Option-Based Wrappers
//!
//! These wrappers provide special handling for `Option` types:
//!
//! - `First<T>`: Takes the first `Some` value when combining multiple `Option<T>` values
//! - `Last<T>`: Takes the last `Some` value when combining multiple `Option<T>` values
//!
//! ### Computation Wrappers
//!
//! These wrappers provide different ways to handle computations:
//!
//! - `Thunk<T>`: A lazy computation wrapper that evaluates only when needed
//! - `Value<T>`: A simple wrapper implementing `Evaluate` for immediate values
//! - `Memoize<F>`: Caches the result of a function for repeated calls
//!
//! ## Usage Patterns
//!
//! Wrapper types are typically used in these ways:
//!
//! ```rust
//! use rustica::datatypes::wrapper::sum::Sum;
//! use rustica::datatypes::wrapper::product::Product;
//! use rustica::datatypes::wrapper::value::Value;
//! use rustica::traits::{semigroup::Semigroup, evaluate::Evaluate};
//!
//! // 1. Arithmetic with Sum/Product wrappers
//! let sum1: Sum<i32> = Sum::new(5);
//! let sum2: Sum<i32> = Sum::new(7);
//! let combined = sum1.combine(&sum2);
//! assert_eq!(combined.inner(), 12); // 5 + 7 = 12
//!
//! // 2. Combining multiple values into one
//! let values = vec![Sum::new(1), Sum::new(2), Sum::new(3)];
//! let sum: i32 = values.into_iter()
//!     .fold(Sum::new(0), |acc, x| acc.combine(&x))
//!     .inner();
//! assert_eq!(sum, 6); // 1 + 2 + 3 = 6
//!
//! // 3. Using Value for evaluation contexts
//! let value: Value<i32> = Value::new(42);
//! let result: i32 = value.evaluate();
//! assert_eq!(result, 42);
//! ```
//!
//! ## When to Use Wrapper Types
//!
//! - Use `Sum`/`Product` when working with numeric collections that need to be combined
//! - Use `Min`/`Max` for finding extremes in collections
//! - Use `First`/`Last` when dealing with optional values that need to be combined with precedence rules
//! - Use `Thunk` when you need lazy evaluation
//! - Use `Value` when you need a simple evaluable container
//! - Use `Memoize` when you want to cache function results
//!
//! ## Implementation Note
//!
//! Most wrapper types follow a simple pattern:
//!
//! 1. They store a single value of type T
//! 2. They implement relevant traits (Semigroup, Monoid, Functor, etc.)
//! 3. They provide methods to access the inner value
//!
//! This consistent interface makes it easy to understand and use these wrappers
//! in your own code.

pub mod first;
pub mod last;
pub mod max;
pub mod memoizer;
pub mod min;
pub mod predicate;
pub mod product;
pub mod sum;
pub mod thunk;
pub mod value;
