//! Prelude: Wrapper Types
//!
//! This module re-exports various wrapper types from Rustica to make them available in a single import.
//!
//! # Key Wrapper Types
//!
//! - [`First`], [`Last`]: First/last priority wrappers (useful for Monoid/Ord operations)
//! - [`Max`], [`Min`]: Maximum/minimum value wrappers
//! - [`Product`], [`Sum`]: Product/sum wrappers (numeric Monoids)
//! - [`Memoizer`]: Memoization wrappers
//! - [`Thunk`]: Lazy evaluation wrapper
//!
//! # Usage Examples
//!
//! ```rust
//! use rustica::prelude::wrapper::*;
//! use rustica::traits::semigroup::Semigroup;
//!
//! let a = Sum(3);
//! let b = Sum(4);
//! assert_eq!(a.combine(&b).unwrap(), 7);
//!
//! let m = Max(10);
//! let n = Max(20);
//! assert_eq!(m.combine(&n).unwrap(), 20);
//! ```
//!
//! # Note
//!
//! Wrapper types provide powerful abstractions when used with [`Monoid`], [`Semigroup`], etc.

pub use crate::datatypes::wrapper::first::First;
pub use crate::datatypes::wrapper::last::Last;
pub use crate::datatypes::wrapper::max::Max;
pub use crate::datatypes::wrapper::memoizer::Memoizer;
pub use crate::datatypes::wrapper::min::Min;
pub use crate::datatypes::wrapper::product::Product;
pub use crate::datatypes::wrapper::sum::Sum;
pub use crate::datatypes::wrapper::thunk::Thunk;

// Also re-export commonly used traits
pub use crate::traits::evaluate::Evaluate;
pub use crate::traits::functor::Functor;
pub use crate::traits::monoid::Monoid;
pub use crate::traits::semigroup::Semigroup;
