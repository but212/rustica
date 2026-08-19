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
//! use rustica::datatypes::id::Id;
//!
//! // --- HKT Utilities ---
//! let double_if_even = |n: i32| if n % 2 == 0 { Some(n * 2) } else { None };
//! let result = pipeline_option(10, vec![double_if_even]);
//! assert_eq!(result, Some(20));
//!
//! // --- Transform Utilities ---
//! let opt = Some(Id::new(5));
//! let doubled = transform_chain(opt, |&x| x * 2);
//! assert_eq!(doubled, Some(Id::new(10)));
//! ```
//!
//! # Note
//!
//! These utilities form powerful combinations when used with Rustica's datatypes, traits, and transformers.

pub use crate::utils::hkt_utils::*;
pub use crate::utils::transform_utils::*;
