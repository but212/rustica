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
//!         Validated::invalid("Must be positive".to_string())
//!     }
//! };
//!
//! let validate_even = |x: &i32| -> Validated<String, i32> {
//!     if *x % 2 == 0 {
//!         Validated::Valid(*x)
//!     } else {
//!         Validated::invalid("Must be even".to_string())
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
//! - **Applicative**: Allows applying functions wrapped in `Validated` contexts
//! - **Semigroup**: Combines error values when both `Validated` values are invalid
//! - **Foldable**: Folds valid values (ignoring invalid ones)
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
pub mod accessors;
#[cfg(feature = "async")]
pub mod async_ops;
pub mod combinators;
pub mod conversions;
pub mod core;
pub mod iter;
pub mod recovery;
pub mod traits;

pub use core::{NonEmptyErrors, Validated};
pub use iter::*;

#[cfg(test)]
mod tests {
    use super::{NonEmptyErrors, Validated};
    use crate::traits::{
        applicative::Applicative, bifunctor::Bifunctor, functor::Functor, monad::Monad, pure::Pure,
        semigroup::Semigroup,
    };
    use quickcheck_macros::quickcheck;

    // Core Algebraic Laws & Properties
    #[test]
    fn test_validated_basic_logic() {
        let v: Validated<String, i32> = Validated::valid(42);
        let i: Validated<String, i32> = Validated::invalid("err".into());

        assert!(v.is_valid());
        assert!(i.is_invalid());
        assert_eq!(v.unwrap(), 42);
        assert_eq!(i.errors(), &["err".to_string()]);
    }

    #[test]
    #[should_panic(expected = "requires at least one error")]
    fn invalid_many_rejects_empty_input() {
        let _: Validated<String, ()> = Validated::invalid_many(std::iter::empty());
    }

    #[test]
    fn try_invalid_many_reports_empty_input() {
        let result: Option<Validated<String, ()>> = Validated::try_invalid_many(std::iter::empty());
        assert!(result.is_none());
    }

    #[test]
    fn non_empty_errors_fallible_construction() {
        assert_eq!(NonEmptyErrors::<String>::try_from_iter(Vec::new()), None);

        let errors = NonEmptyErrors::try_from_iter(["first".to_string(), "second".to_string()])
            .expect("non-empty input should construct errors");
        assert_eq!(errors.as_slice(), ["first", "second"]);
    }

    #[quickcheck]
    fn prop_validated_functor_identity(val: i32) -> bool {
        let v: Validated<String, i32> = Validated::valid(val);
        v.fmap(|x| *x) == v
    }

    #[quickcheck]
    fn prop_validated_monad_left_identity(val: i32) -> bool {
        let f = |x: &i32| Validated::<String, i32>::valid(x.saturating_add(1));
        Validated::<String, i32>::pure(&val).bind(f) == f(&val)
    }

    #[test]
    fn test_validated_typeclass_laws() {
        let value = Validated::<String, i32>::valid(10);
        let mapped = value.fmap(|x| x + 1).fmap(|x| x * 2);
        assert_eq!(mapped, Validated::valid(22));

        let function: Validated<String, fn(&i32) -> i32> = Validated::valid(|x| x * 2);
        let argument = Validated::<String, i32>::valid(10);
        assert_eq!(function.apply(&argument), Validated::valid(20));

        let left = Validated::<String, String>::invalid("a".into());
        let middle = Validated::<String, String>::invalid("b".into());
        let right = Validated::<String, String>::invalid("c".into());
        assert_eq!(
            left.combine(&middle).combine(&right),
            left.combine(&middle.combine(&right))
        );

        let bifunctor = Validated::<String, i32>::invalid("error".into());
        assert_eq!(
            bifunctor.bimap(|x| x + 1, |e| format!("{e}!")),
            Validated::invalid("error!".to_string())
        );
    }

    #[test]
    fn test_validated_core_conversions_and_mapping() {
        let valid: Validated<&str, i32> = Validated::valid(42);
        assert!(valid.is_valid());
        let invalid: Validated<&str, i32> = Validated::invalid("error");
        assert!(invalid.is_invalid());

        let result: Result<i32, &str> = Err("error");
        assert_eq!(Validated::from(&result), invalid);

        let some = Some(42);
        assert_eq!(
            Validated::from_option(&some, &"missing"),
            Validated::valid(42)
        );
        let none: Option<i32> = None;
        assert_eq!(
            Validated::from_option(&none, &"missing"),
            Validated::invalid("missing")
        );

        let mapped = invalid.fmap_invalid(|error| format!("Error: {error}"));
        assert_eq!(mapped, Validated::invalid("Error: error".to_string()));
    }

    // Accumulation & Traversal (the core USP)
    #[test]
    fn test_validated_error_accumulation() {
        let v1: Validated<String, i32> = Validated::invalid("e1".into());
        let v2: Validated<String, i32> = Validated::invalid("e2".into());
        let v3: Validated<String, i32> = Validated::valid(100);

        let result = Validated::<String, i32>::lift3(|a, b, c| a + b + c, &v1, &v2, &v3);
        assert_eq!(result.errors(), &["e1".to_string(), "e2".to_string()]);

        let list = vec![v1.clone(), v2.clone(), v3];
        let collected: Validated<String, Vec<i32>> = Validated::collect(list.into_iter());
        assert_eq!(collected.errors().len(), 2);

        let combined = v1.combine_errors_owned(v2);
        assert_eq!(
            combined.error_slice(),
            &["e1".to_string(), "e2".to_string()]
        );
    }

    // Interop, unwrap and recovery
    #[test]
    fn test_validated_recovery_and_interop() {
        let invalid: Validated<String, i32> =
            Validated::invalid_many(["e1".to_string(), "e2".to_string()]);

        let res = invalid.clone().into_result_first_error();
        assert_eq!(res, Err("e1".to_string()));
        assert_eq!(
            Validated::<String, i32>::from(&Ok::<i32, String>(42)),
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

        assert_eq!(Validated::<&str, i32>::valid(10).unwrap_or(&0), 10);
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

        let result = Validated::<String, User>::lift3(
            |n, a, e| User {
                name: n.clone(),
                age: *a,
                email: e.clone(),
            },
            &validate_name("A"),
            &validate_age(10),
            &validate_email("bad"),
        );

        assert_eq!(result.errors().len(), 3);
        assert!(result.errors().contains(&"Name too short".to_string()));

        let success = Validated::<String, User>::lift3(
            |n, a, e| User {
                name: n.clone(),
                age: *a,
                email: e.clone(),
            },
            &validate_name("John"),
            &validate_age(25),
            &validate_email("john@doe.com"),
        );
        assert!(success.is_valid());
    }

    #[cfg(feature = "serde")]
    #[test]
    fn test_validated_serialization() {
        use serde_json;

        let invalid: Validated<String, i32> = Validated::invalid("error".to_string());
        let json = serde_json::to_string(&invalid).unwrap();
        let back: Validated<String, i32> = serde_json::from_str(&json).unwrap();
        assert_eq!(invalid, back);
        assert!(serde_json::from_str::<Validated<String, i32>>(r#"{"Invalid":[]}"#).is_err());
    }
}
