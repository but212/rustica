//! Prelude: Utilities
//!
//! This module re-exports various utility functions from Rustica to make them available in a single import.
//!
//! # Key Utilities
//!
//! - `hkt_utils`: Higher-kinded type utilities (e.g., HKT conversions, type witnesses)
//! - `transform_utils`: Function composition, transformation, and chaining utilities
//!
//! # Usage Examples
//!
//! ```rust
//! use rustica::prelude::utils::*;
//!
//! // --- HKT Utilities ---
//! let numbers = vec![1, 2, 3, 4, 5, 6];
//! let evens_squared: Vec<_> = numbers.into_iter().filter(|n| n % 2 == 0).map(|n| n * n).collect();
//! assert_eq!(evens_squared, vec![4, 16, 36]);
//!
//! let a = vec![1, 2, 3];
//! let b = vec![4, 5, 6];
//! let summed: Vec<_> = a.into_iter().zip(b).map(|(x, y)| x + y).collect();
//! assert_eq!(summed, vec![5, 7, 9]);
//!
//! let double_if_even = |n: i32| if n % 2 == 0 { Some(n * 2) } else { None };
//! let result = pipeline_option(10, vec![double_if_even]);
//! assert_eq!(result, Some(20));
//!
//! // --- Transform Utilities ---
//! use rustica::datatypes::maybe::Maybe;
//! let maybes = vec![Maybe::Just(1), Maybe::Just(2), Maybe::Nothing];
//! let doubled: Vec<Maybe<i32>> = transform_all(&maybes, |x| x * 2);
//! assert_eq!(doubled, vec![Maybe::Just(2), Maybe::Just(4), Maybe::Nothing]);
//!
//! use rustica::utils::transform_utils::Pipeline;
//! let result = Pipeline::new(Some(5))
//!     .map(|&x| x * 3)
//!     .map(|x| x.to_string())
//!     .extract();
//! assert_eq!(result, Some("15".to_string()));
//! ```
//!
//! # Note
//!
//! These utilities form powerful combinations when used with Rustica's datatypes, traits, and transformers.

pub use crate::utils::hkt_utils::*;
pub use crate::utils::transform_utils::*;
