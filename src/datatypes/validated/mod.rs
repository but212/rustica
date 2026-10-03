#![doc = include_str!("../../../docs/datatypes/validated.md")]

mod combinators;
pub mod core;
pub mod iter;

pub use core::{NonEmptyErrors, Validated};
pub use iter::*;

#[cfg(test)]
mod tests {
    use super::Validated;
    use crate::traits::semigroup::Semigroup;
    use alloc::format;
    use alloc::string::String;
    use alloc::string::ToString;
    use alloc::vec;
    use alloc::vec::Vec;
    use quickcheck_macros::quickcheck;

    // Algebraic laws
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
        let _: Validated<(), String> = Validated::invalid_many(core::iter::empty());
    }

    #[test]
    fn try_invalid_many_reports_empty_input() {
        let result: Option<Validated<(), String>> =
            Validated::try_invalid_many(core::iter::empty());
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

    // Accumulation and traversal
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

    // Interop and recovery
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

        assert_eq!(Validated::<i32, &str>::valid(10).unwrap_or(0), 10);
        assert_eq!(invalid.into_option(), None);
    }

    // Complex validation
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
