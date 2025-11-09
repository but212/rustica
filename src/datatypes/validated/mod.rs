//! # Validated Datatype (`Validated<E, A>`)
//!
//! The `Validated` datatype represents a validation result that can either be valid with a value
//! or invalid with a collection of errors. Unlike `Result`, which fails fast on the first error,
//! `Validated` can accumulate multiple errors during validation.
//!
//! ## Quick Start
//!
//! Accumulate validation errors instead of failing fast:
//!
//! ```rust
//! use rustica::datatypes::validated::Validated;
//! use rustica::traits::applicative::Applicative;
//! use rustica::traits::functor::Functor;
//! use rustica::traits::pure::Pure;
//!
//! // Create validation functions
//! let validate_positive = |x: &i32| -> Validated<String, i32> {
//!     if *x > 0 {
//!         Validated::Valid(*x)
//!     } else {
//!         Validated::Invalid(vec!["Must be positive".to_string()].into())
//!     }
//! };
//!
//! let validate_even = |x: &i32| -> Validated<String, i32> {
//!     if *x % 2 == 0 {
//!         Validated::Valid(*x)
//!     } else {
//!         Validated::Invalid(vec!["Must be even".to_string()].into())
//!     }
//! };
//!
//! // Combine validations - accumulates ALL errors
//! let combine_validations = |a: &i32, b: &i32| -> Validated<String, i32> {
//!     Validated::<String, i32>::lift2(
//!         |x: &i32, y: &i32| x + y,
//!         &validate_positive(a),
//!         &validate_even(b)
//!     )
//! };
//!
//! // Success case
//! let success = combine_validations(&5, &4);
//! assert_eq!(success, Validated::Valid(9));
//!
//! // Error accumulation - gets BOTH errors
//! let errors = combine_validations(&-1, &3);
//! assert!(errors.is_invalid());
//! assert_eq!(errors.errors().len(), 2);
//! ```
//!
//! ## Type Class Implementations
//!
//! `Validated<E, A>` implements several type classes that enable its core functionality:
//!
//! - **Functor**: Maps functions over the valid value
//! - **Bifunctor**: Maps functions over both the error and valid values
//! - **Applicative**: Allows applying functions wrapped in Validated contexts
//! - **Semigroup**: Combines error values when both Validated values are invalid
//! - **Foldable**: Folds valid values (ignoring invalid ones)
//!
//! ## Examples
//!
//! ### Creating and Checking Validated Values
//!
//! ```rust
//! use rustica::datatypes::validated::Validated;
//!
//! let valid: Validated<&str, i32> = Validated::valid(42);
//! assert!(valid.is_valid());
//!
//! let invalid: Validated<&str, i32> = Validated::invalid("error");
//! assert!(invalid.is_invalid());
//!
//! /// Converting From Result
//!
//! let result: Result<i32, &str> = Ok(42);
//! let validated = Validated::from_result(&result);
//! assert_eq!(validated, Validated::valid(42));
//!
//! let error_result: Result<i32, &str> = Err("error");
//! let validated = Validated::from_result(&error_result);
//! assert_eq!(validated, Validated::invalid("error"));
//!
//! /// Converting From Option
//!
//! let some_value: Option<i32> = Some(42);
//! let validated: Validated<&str, i32> = Validated::from_option(&some_value, &"missing value");
//! assert_eq!(validated, Validated::valid(42));
//!
//! let none_value: Option<i32> = None;
//! let validated: Validated<&str, i32> = Validated::from_option(&none_value, &"missing value");
//! assert_eq!(validated, Validated::invalid("missing value"));
//! ```
//!
//! ### Advanced Operations
//!
//! ```rust
//! use rustica::datatypes::validated::Validated;
//!
//! // Collecting Multiple Validated Values
//!
//! let values = vec![
//!     Validated::<&str, i32>::valid(1),
//!     Validated::<&str, i32>::valid(2),
//!     Validated::<&str, i32>::valid(3),
//! ];
//! let collected: Validated<&str, Vec<i32>> = Validated::collect(values.iter().cloned());
//! assert_eq!(collected, Validated::valid(vec![1, 2, 3]));
//!
//! let mixed = vec![
//!     Validated::<&str, i32>::valid(1),
//!     Validated::<&str, i32>::invalid("error"),
//!     Validated::<&str, i32>::valid(3),
//! ];
//! let collected: Validated<&str, Vec<i32>> = Validated::collect(mixed.iter().cloned());
//! assert!(collected.is_invalid());
//!
//! // Error Transformation
//!
//! let invalid: Validated<&str, i32> = Validated::invalid("error");
//! let mapped = invalid.fmap_invalid(|e| format!("Error: {}", e));
//! assert_eq!(mapped, Validated::invalid("Error: error".to_string()));
//! ```
//!
//! ## Functional Programming Context
//!
//! In functional programming, validation is often handled through types that can represent
//! either success or failure. The `Validated` type is inspired by similar constructs in other
//! functional programming languages, such as:
//!
//! - `Validated` in Cats (Scala)
//! - `Validation` in Arrow (Kotlin)
//! - `Validation` in fp-ts (TypeScript)
//!
//! The key difference between `Validated` and `Result` is that `Validated` is designed for
//! scenarios where you want to collect all validation errors rather than stopping at the first one.
//!
//! ## Type Class Laws
//!
//! ### Functor Laws
//!
//! 1. **Identity**: `fmap(id) == id`
//! 2. **Composition**: `fmap(f . g) == fmap(f) . fmap(g)`
//!
//! ### Bifunctor Laws
//!
//! 1. **Identity**: `bimap(id, id) == id`
//! 2. **Composition**: `bimap(f1 . f2, g1 . g2) == bimap(f1, g1) . bimap(f2, g2)`
//!
//! ### Applicative Laws
//!
//! 1. **Identity**: `pure(id) <*> v = v`
//! 2. **Homomorphism**: `pure(f) <*> pure(x) = pure(f(x))`
//! 3. **Interchange**: `u <*> pure(y) = pure($ y) <*> u`
//! 4. **Composition**: `pure(.) <*> u <*> v <*> w = u <*> (v <*> w)`
//!
//! ### Semigroup Laws
//!
//! 1. **Associativity**: `(a <> b) <> c = a <> (b <> c)`
//!
//! ### Monoid Laws
//!
//! 1. **Left Identity**: `mempty <> a = a`
//! 2. **Right Identity**: `a <> mempty = a`
//!
//! ## Use Cases
//!
//! The `Validated` datatype is particularly useful for:
//!
//! - **Form validation**: Collecting all validation errors at once
//! - **Configuration validation**: Validating multiple configuration parameters
//! - **Data parsing**: Accumulating parsing errors from different parts of a document
//! - **API request validation**: Returning all validation errors to the client
//!
//! ## Function-Level Documentation
//!
//! For detailed examples of how to use the `Validated` datatype, including:
//! - Creating valid and invalid instances
//! - Working with validation results
//! - Accumulating errors
//! - Transforming valid and invalid values
//! - Converting between `Validated` and other types
//! - Using applicative validation for form validation
//!
//! Please refer to the documentation of individual functions in this module.
pub mod core;
pub mod iter;
pub mod traits;

pub use core::*;
pub use iter::*;
