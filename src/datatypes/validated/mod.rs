//! # Validated Datatype (`Validated<T, E>`)
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
//!
//! // Create validation functions
//! let validate_positive = |x: &i32| -> Validated<i32, String> {
//!     if *x > 0 {
//!         Validated::Valid(*x)
//!     } else {
//!         Validated::invalid("Must be positive".to_string())
//!     }
//! };
//!
//! let validate_even = |x: &i32| -> Validated<i32, String> {
//!     if *x % 2 == 0 {
//!         Validated::Valid(*x)
//!     } else {
//!         Validated::invalid("Must be even".to_string())
//!     }
//! };
//!
//! // Combine validations - accumulates ALL errors
//! let combine_validations = |a: &i32, b: &i32| -> Validated<i32, String> {
//!     Validated::<i32, String>::lift2(
//!         |x: i32, y: i32| x + y,
//!         validate_positive(a),
//!         validate_even(b)
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
//! assert_eq!(errors.error_slice().len(), 2);
//! ```
//!
//! ## Trait Implementations
//!
//! `Validated<T, E>` implements algebraic traits and provides inherent functional methods:
//!
//! - **Semigroup**: Combines inner values when both are valid via `T::combine`, or concatenates error collections when invalid
//!
//! Inherent methods like [`bimap`](Validated::bimap), [`map`](Validated::map), [`map_err`](Validated::map_err),
//! [`zip`](Validated::zip), and [`zip_with`](Validated::zip_with) provide dual-track mappings and applicative combinations without trait bounds.
//!
//! ## Examples
//!
//! The quick-start example above demonstrates the core workflow. Individual methods document
//! their minimal invocation; algebraic laws and boundary cases are covered by the unit tests.
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
//! The type-class implementations obey their documented laws; executable law and boundary
//! checks live in the unit-test module below rather than in independent doctest crates.
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
pub mod combinators;
pub mod core;
pub mod iter;
pub mod traits;

pub use core::{NonEmptyErrors, Validated};
pub use iter::*;

#[cfg(test)]
mod tests {
    use super::Validated;
    use crate::traits::semigroup::Semigroup;
    use quickcheck_macros::quickcheck;

    // Core Algebraic Laws & Properties
    #[test]
    fn test_validated_basic_logic() {
        let v: Validated<i32, String> = Validated::valid(42);
        let i: Validated<i32, String> = Validated::invalid("err".into());

        assert!(v.is_valid());
        assert!(i.is_invalid());
        assert_eq!(v.unwrap(), 42);
        assert_eq!(i.error_slice(), &["err".to_string()]);
    }

    #[test]
    #[should_panic(expected = "requires at least one error")]
    fn invalid_many_rejects_empty_input() {
        let _: Validated<(), String> = Validated::invalid_many(std::iter::empty());
    }

    #[test]
    fn try_invalid_many_reports_empty_input() {
        let result: Option<Validated<(), String>> = Validated::try_invalid_many(std::iter::empty());
        assert!(result.is_none());
    }

    #[quickcheck]
    fn prop_validated_functor_identity(val: i32) -> bool {
        let v: Validated<i32, String> = Validated::valid(val);
        v.clone().map(|x| x) == v
    }

    #[test]
    fn test_validated_typeclass_laws() {
        let value = Validated::<i32, String>::valid(10);
        let mapped = value.map(|x| x + 1).map(|x| x * 2);
        assert_eq!(mapped, Validated::valid(22));

        let function: Validated<fn(i32) -> i32, String> = Validated::valid(|x| x * 2);
        let argument = Validated::<i32, String>::valid(10);
        assert_eq!(
            function.zip_with(argument, |f, x| f(x)),
            Validated::valid(20)
        );

        let left = Validated::<String, String>::invalid("a".into());
        let middle = Validated::<String, String>::invalid("b".into());
        let right = Validated::<String, String>::invalid("c".into());
        assert_eq!(
            left.clone().combine(middle.clone()).combine(right.clone()),
            left.combine(middle.combine(right))
        );
    }

    #[test]
    fn test_validated_core_conversions_and_mapping() {
        let valid: Validated<i32, &str> = Validated::valid(42);
        assert!(valid.is_valid());
        let invalid: Validated<i32, &str> = Validated::invalid("error");
        assert!(invalid.is_invalid());

        let result: Result<i32, &str> = Err("error");
        assert_eq!(Validated::from(result), invalid);

        let some = Some(42);
        assert_eq!(
            Validated::from_option(some, "missing"),
            Validated::valid(42)
        );
        let none: Option<i32> = None;
        assert_eq!(
            Validated::from_option(none, "missing"),
            Validated::invalid("missing")
        );

        let mapped = invalid.map_err(|error| format!("Error: {error}"));
        assert_eq!(mapped, Validated::invalid("Error: error".to_string()));
    }

    // Accumulation & Traversal (the core USP)
    #[test]
    fn test_validated_error_accumulation() {
        let v1: Validated<i32, String> = Validated::invalid("e1".into());
        let v2: Validated<i32, String> = Validated::invalid("e2".into());
        let v3: Validated<i32, String> = Validated::valid(100);

        let result =
            Validated::<i32, String>::lift3(|a, b, c| a + b + c, v1.clone(), v2.clone(), v3);
        assert_eq!(result.error_slice(), &["e1".to_string(), "e2".to_string()]);

        let list = vec![v1.clone(), v2.clone(), Validated::valid(100)];
        let collected: Validated<Vec<i32>, String> = Validated::collect(list.into_iter());
        assert_eq!(collected.error_slice().len(), 2);

        let combined = v1.combine_errors(v2).unwrap();
        assert_eq!(combined.as_slice(), &["e1".to_string(), "e2".to_string()]);
    }

    // Interop, unwrap and recovery
    #[test]
    fn test_validated_recovery_and_interop() {
        let invalid: Validated<i32, String> =
            Validated::invalid_many(["e1".to_string(), "e2".to_string()]);

        let res = invalid.clone().into_result_first_error();
        assert_eq!(res, Err("e1".to_string()));
        assert_eq!(
            Validated::<i32, String>::from(&Ok::<i32, String>(42)),
            Validated::valid(42)
        );

        let recovered = invalid.clone().recover_with(0);
        assert_eq!(recovered.unwrap(), 0);

        let early_recovery = invalid.clone().recover_all(|e: String| {
            if e == "e2" {
                Validated::valid(99)
            } else {
                Validated::invalid(e)
            }
        });
        assert_eq!(early_recovery.unwrap(), 99);

        assert_eq!(Validated::<i32, &str>::valid(10).unwrap_or(0), 10);
        assert_eq!(invalid.into_option(), None);
    }

    // Real-world complex validation scenario
    #[test]
    fn test_validated_complex_registration_scenario() {
        #[derive(Debug, PartialEq, Clone)]
        struct User {
            name: String,
            age: u8,
            email: String,
        }

        let validate_name = |n: &str| {
            if n.len() >= 2 {
                Validated::valid(n.to_string())
            } else {
                Validated::invalid("Name too short".into())
            }
        };
        let validate_age = |a: u8| {
            if a >= 18 {
                Validated::valid(a)
            } else {
                Validated::invalid("Must be adult".into())
            }
        };
        let validate_email = |e: &str| {
            if e.contains('@') {
                Validated::valid(e.to_string())
            } else {
                Validated::invalid("Invalid email".into())
            }
        };

        let result = Validated::<User, String>::lift3(
            |n, a, e| User {
                name: n,
                age: a,
                email: e,
            },
            validate_name("A"),
            validate_age(10),
            validate_email("bad"),
        );

        assert_eq!(result.error_slice().len(), 3);
        assert!(result.error_slice().contains(&"Name too short".to_string()));

        let success = Validated::<User, String>::lift3(
            |n, a, e| User {
                name: n,
                age: a,
                email: e,
            },
            validate_name("John"),
            validate_age(25),
            validate_email("john@doe.com"),
        );
        assert!(success.is_valid());
    }

    #[cfg(feature = "serde")]
    #[test]
    fn test_validated_serialization() {
        use serde_json;

        let invalid: Validated<i32, String> = Validated::invalid("error".to_string());
        let json = serde_json::to_string(&invalid).unwrap();
        let back: Validated<i32, String> = serde_json::from_str(&json).unwrap();
        assert_eq!(invalid, back);
        assert!(serde_json::from_str::<Validated<i32, String>>(r#"{"Invalid":[]}"#).is_err());
    }
}
