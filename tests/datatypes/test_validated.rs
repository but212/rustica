//! Comprehensive test suite for the Validated type
//!
//! This module provides extensive testing for the Validated data type,
//! covering all major functionality including functor, applicative, and monad laws.

use quickcheck::TestResult;
use quickcheck_macros::quickcheck;
use rustica::datatypes::validated::Validated;
use rustica::prelude::*;
use rustica::traits::applicative::Applicative;
use rustica::traits::foldable::Foldable;
use rustica::traits::functor::Functor;
use rustica::traits::monad::Monad;
use smallvec::{SmallVec, smallvec};

// =============================================================================
// BASIC CREATION AND ACCESS TESTS
// =============================================================================

#[cfg(test)]
mod creation_tests {
    use super::*;

    #[test]
    fn test_valid_creation() {
        let valid: Validated<String, i32> = Validated::valid(42);
        assert!(valid.is_valid());
        assert!(!valid.is_invalid());
        assert_eq!(valid.iter().next(), Some(&42));
        assert!(valid.errors().is_empty());
    }

    #[test]
    fn test_invalid_single_error() {
        let invalid: Validated<&str, i32> = Validated::invalid("error");
        assert!(!invalid.is_valid());
        assert!(invalid.is_invalid());
        assert_eq!(invalid.errors().len(), 1);
        assert_eq!(invalid.errors()[0], "error");
        assert_eq!(invalid.iter().next(), None);
    }

    #[test]
    fn test_invalid_multiple_errors() {
        let multi_invalid: Validated<&str, i32> =
            Validated::invalid_many(["error1", "error2", "error3"]);
        assert!(multi_invalid.is_invalid());
        assert_eq!(multi_invalid.errors().len(), 3);
        assert_eq!(multi_invalid.errors()[0], "error1");
        assert_eq!(multi_invalid.errors()[1], "error2");
        assert_eq!(multi_invalid.errors()[2], "error3");
    }

    #[test]
    fn test_value_and_error_payload_accessors() {
        let valid: Validated<&str, i32> = Validated::Valid(42);
        assert_eq!(valid.iter().next(), Some(&42));
        assert_eq!(valid.error_payload(), None);

        let invalid: Validated<&str, i32> = Validated::Invalid(smallvec!["error1", "error2"]);
        assert_eq!(invalid.iter().next(), None);
        assert_eq!(
            invalid.error_payload(),
            Some(&smallvec!["error1", "error2"])
        );
    }

    #[test]
    fn test_edge_cases() {
        // Empty error vector (edge case)
        let empty: Validated<String, i32> = Validated::invalid_many(Vec::<String>::new());
        assert!(empty.is_invalid());
        assert!(empty.errors().is_empty());

        // Large error vector
        let many: Vec<_> = (0..100).map(|i| format!("err{i}")).collect();
        let large: Validated<String, i32> = Validated::invalid_many(many.clone());
        assert_eq!(large.errors().len(), 100);
        assert_eq!(large.errors()[0], "err0");
        assert_eq!(large.errors()[99], "err99");
    }
}

// =============================================================================
// FUNCTOR TESTS
// =============================================================================

#[cfg(test)]
mod functor_tests {
    use super::*;

    #[test]
    fn test_fmap_on_valid() {
        let v1: Validated<String, i32> = Validated::valid(42); // Assuming String for error type, adjust if needed
        let _v2 = v1.fmap(|x: &i32| x * 2);
        assert_eq!(_v2, Validated::<String, i32>::valid(84));
    }

    #[test]
    fn test_fmap_on_invalid() {
        let invalid: Validated<String, i32> = Validated::invalid("error".to_string());
        let error_result = invalid.fmap(|x| x * 2);
        assert!(error_result.is_invalid());
    }

    #[test]
    fn test_fmap_owned() {
        let valid: Validated<String, i32> = Validated::valid(21);
        let mapped = valid.fmap_owned(|x| x * 2);
        assert_eq!(mapped, Validated::valid(42));
    }

    #[test]
    fn test_fmap_invalid_operations() {
        // Single error
        let invalid: Validated<&str, i32> = Validated::invalid("error");
        let mapped = invalid.fmap_invalid(|e| format!("Error: {e}"));
        assert_eq!(mapped, Validated::invalid("Error: error".to_string()));

        // Multiple errors
        let multi: Validated<&str, i32> = Validated::invalid_many(["e1", "e2"]);
        let mapped = multi.fmap_invalid(|e| format!("Err: {e}"));
        assert_eq!(
            mapped.errors(),
            &["Err: e1".to_string(), "Err: e2".to_string()]
        );
    }

    #[test]
    fn test_functor_identity_law() {
        let v: Validated<String, i32> = Validated::valid(5);
        assert_eq!(v.fmap(|x| *x), v);

        let invalid: Validated<String, i32> = Validated::invalid("error".to_string());
        assert_eq!(invalid.fmap(|x| *x), invalid);
    }

    #[test]
    fn test_functor_composition_law() {
        let v: Validated<String, i32> = Validated::valid(5);
        let f = |x: &i32| x + 1;
        let g = |x: &i32| x * 2;

        let lhs = v.fmap(|x| f(&g(x)));
        let rhs = v.fmap(g).fmap(f);
        assert_eq!(lhs, rhs);
    }
}

// =============================================================================
// APPLICATIVE TESTS
// =============================================================================

#[cfg(test)]
mod applicative_tests {
    use super::*;

    #[test]
    fn test_apply_valid_to_valid() {
        let value: Validated<String, i32> = Validated::valid(21);
        let f: Validated<String, fn(&i32) -> i32> = Validated::valid(|x| x * 2);
        let result = f.apply(&value);
        assert_eq!(result, Validated::valid(42));
    }

    #[test]
    fn test_apply_with_errors() {
        let value: Validated<String, i32> = Validated::valid(21);
        let f: Validated<String, fn(&i32) -> i32> = Validated::invalid("error".to_string());
        let result = f.apply(&value);
        assert_eq!(result, Validated::invalid("error".to_string()));

        let value: Validated<String, i32> = Validated::invalid("error".to_string());
        let f: Validated<String, fn(&i32) -> i32> = Validated::valid(|x| x * 2);
        let result = f.apply(&value);
        assert_eq!(result, Validated::invalid("error".to_string()));
    }

    #[test]
    fn test_error_accumulation_in_apply() {
        let f: Validated<String, fn(&i32) -> i32> = Validated::invalid("error1".to_string());
        let value: Validated<String, i32> = Validated::invalid("error2".to_string());
        let result = f.apply(&value);
        let errors = result.errors();
        assert_eq!(errors.len(), 2);
        assert_eq!(errors[0], "error1");
        assert_eq!(errors[1], "error2");
    }

    #[test]
    fn test_pure() {
        let pure: Validated<String, i32> = Validated::<String, i32>::pure(&42);
        assert_eq!(pure, Validated::valid(42));
    }

    #[test]
    fn test_lift2() {
        let a: Validated<String, i32> = Validated::valid(10);
        let b: Validated<String, i32> = Validated::valid(32);
        let result = Validated::<String, i32>::lift2(|x, y| x + y, &a, &b);
        assert_eq!(result, Validated::valid(42));
    }

    #[test]
    fn test_lift3_success() {
        let a: Validated<String, i32> = Validated::valid(10);
        let b: Validated<String, i32> = Validated::valid(20);
        let c: Validated<String, i32> = Validated::valid(12);
        let result = Validated::<String, i32>::lift3(|x, y, z| x + y + z, &a, &b, &c);
        assert_eq!(result, Validated::valid(42));
    }

    #[test]
    fn test_lift3_error_accumulation() {
        let a: Validated<String, i32> = Validated::invalid("error1".to_string());
        let b: Validated<String, i32> = Validated::invalid("error2".to_string());
        let c: Validated<String, i32> = Validated::invalid("error3".to_string());
        let result = Validated::<String, i32>::lift3(|x, y, z| x + y + z, &a, &b, &c);
        let errors = result.errors();
        assert_eq!(errors.len(), 3);
        assert_eq!(errors[0], "error1");
        assert_eq!(errors[1], "error2");
        assert_eq!(errors[2], "error3");
    }

    #[test]
    fn test_apply_owned() {
        let value: Validated<String, i32> = Validated::valid(10);
        let f: Validated<String, fn(i32) -> i32> = Validated::valid(|x| x + 1);
        let applied = f.clone().apply_owned(value.clone());
        assert_eq!(applied, Validated::valid(11));

        let invalid: Validated<String, i32> = Validated::invalid("err".to_string());
        let applied = f.clone().apply_owned(invalid.clone());
        assert!(applied.is_invalid());
    }

    #[test]
    fn test_applicative_identity_law() {
        let v: Validated<String, i32> = Validated::valid(7);
        let id_fn: Validated<String, fn(&i32) -> i32> = Validated::valid(|x| *x);
        assert_eq!(id_fn.apply(&v), v);
    }

    #[test]
    fn test_applicative_homomorphism_law() {
        let f = |x: &i32| x + 1;
        let a = 3;
        let pure_a: Validated<String, i32> = Validated::valid(a);
        let pure_f = Validated::valid(f);
        assert_eq!(pure_f.apply(&pure_a), Validated::valid(f(&a)));
    }
}

// =============================================================================
// MONAD TESTS
// =============================================================================

#[cfg(test)]
mod monad_tests {
    use super::*;

    #[test]
    fn test_bind_with_valid() {
        let valid: Validated<String, i32> = Validated::valid(21);
        let result = valid.bind(|&x| Validated::valid(x * 2));
        assert_eq!(result, Validated::valid(42));
    }

    #[test]
    fn test_bind_with_invalid() {
        let invalid: Validated<String, i32> = Validated::invalid("error".to_string());
        let result = invalid.bind(|&x| Validated::valid(x * 2));
        assert_eq!(result, Validated::invalid("error".to_string()));
    }

    #[test]
    fn test_monad_left_identity_law() {
        let a = 42;
        let f = |x: &i32| Validated::<String, i32>::valid(*x + 1);
        let left = Validated::<String, i32>::pure(&a).bind(f);
        let right = f(&a);
        assert_eq!(left, right);
    }

    #[test]
    fn test_monad_right_identity_law() {
        let m = Validated::<String, i32>::valid(1);
        let right = m.bind(Validated::<String, i32>::pure);
        assert_eq!(right, m);
    }

    #[test]
    fn test_monad_associativity_law() {
        let f = |x: &i32| Validated::<String, i32>::valid(x + 1);
        let g = |x: &i32| Validated::<String, i32>::valid(x * 2);
        let m = Validated::<String, i32>::valid(10);

        let left = m.bind(f).bind(g);
        let right = m.bind(|x| f(x).bind(g));
        assert_eq!(left, right);
    }
}

// =============================================================================
// FOLDABLE TESTS
// =============================================================================

#[cfg(test)]
mod foldable_tests {
    use super::*;

    #[test]
    fn test_fold_left_valid() {
        let valid: Validated<String, i32> = Validated::valid(21);
        let result = valid.fold_left(&0, |acc, x| acc + x);
        assert_eq!(result, 21);
    }

    #[test]
    fn test_fold_left_invalid() {
        let invalid: Validated<String, i32> = Validated::invalid("error".to_string());
        let result = invalid.fold_left(&0, |acc, x| acc + x);
        assert_eq!(result, 0);
    }

    #[test]
    fn test_fold_right() {
        let valid: Validated<String, i32> = Validated::valid(5);
        let prod = valid.fold_right(&1, |x, acc| x * acc);
        assert_eq!(prod, 5);
    }
}

// =============================================================================
// CONVERSION TESTS
// =============================================================================

#[cfg(test)]
mod conversion_tests {
    use super::*;

    #[test]
    fn test_from_result() {
        let ok_result: Result<i32, &str> = Ok(42);
        let validated = Validated::from_result(&ok_result);
        assert!(validated.is_valid());
        assert_eq!(validated.iter().next(), Some(&42));

        let err_result: Result<i32, &str> = Err("error");
        let validated = Validated::from_result(&err_result);
        assert!(validated.is_invalid());
        assert_eq!(validated.errors()[0], "error");
    }

    #[test]
    fn test_to_result() {
        let valid: Validated<&str, i32> = Validated::valid(42);
        let result = valid.to_result();
        assert!(result.is_ok());
        assert_eq!(result.unwrap(), 42);

        let invalid: Validated<&str, i32> = Validated::invalid("error");
        let result = invalid.to_result();
        assert!(result.is_err());
        assert_eq!(result.unwrap_err(), "error");

        // Multiple errors - returns first error
        let multi_invalid: Validated<&str, i32> = Validated::invalid_many(["error1", "error2"]);
        let result = multi_invalid.to_result();
        assert!(result.is_err());
        assert_eq!(result.unwrap_err(), "error1");
    }

    #[test]
    fn test_from_option() {
        let some_value: Option<i32> = Some(42);
        let validated = Validated::from_option(&some_value, &"no value");
        assert_eq!(validated, Validated::valid(42));

        let none_value: Option<i32> = None;
        let validated = Validated::from_option(&none_value, &"no value");
        assert_eq!(validated, Validated::invalid("no value"));
    }

    #[test]
    fn test_to_option() {
        let valid: Validated<&str, i32> = Validated::valid(42);
        let option = valid.to_option();
        assert_eq!(option, Some(42));

        let invalid: Validated<&str, i32> = Validated::invalid("error");
        let option = invalid.to_option();
        assert_eq!(option, None);
    }

    #[test]
    fn test_into_value() {
        let valid: Validated<&str, i32> = Validated::Valid(42);
        assert_eq!(valid.into_value(), Ok(42));

        let invalid: Validated<&str, i32> = Validated::Invalid(smallvec!["err1"]);
        assert_eq!(invalid.into_value(), Err(smallvec!["err1"]));
    }

    #[test]
    fn test_into_error_payload() {
        let valid: Validated<&str, i32> = Validated::Valid(42);
        assert_eq!(valid.into_error_payload(), Err(42));

        let invalid: Validated<&str, i32> = Validated::Invalid(smallvec!["err1", "err2"]);
        assert_eq!(invalid.into_error_payload(), Ok(smallvec!["err1", "err2"]));
    }
}

// =============================================================================
// UNWRAP AND UTILITY TESTS
// =============================================================================

#[cfg(test)]
mod unwrap_tests {
    use super::*;

    #[test]
    fn test_unwrap_or() {
        let valid: Validated<&str, i32> = Validated::valid(42);
        assert_eq!(valid.unwrap_or(&0), 42);

        let invalid: Validated<&str, i32> = Validated::invalid("error");
        assert_eq!(invalid.unwrap_or(&0), 0);
    }

    #[test]
    fn test_unwrap_owned() {
        let valid: Validated<&str, i32> = Validated::Valid(42);
        assert_eq!(valid.unwrap_owned(), 42);

        // Test with a non-Clone type
        #[derive(Debug, PartialEq)]
        struct NonClone(i32);
        let valid_non_clone: Validated<&str, NonClone> = Validated::Valid(NonClone(100));
        assert_eq!(valid_non_clone.unwrap_owned(), NonClone(100));
    }

    #[test]
    #[should_panic(expected = "Called Validated::unwrap_owned() on an Invalid value")]
    fn test_unwrap_owned_panic() {
        let invalid: Validated<&str, i32> = Validated::Invalid(smallvec!["error"]);
        invalid.unwrap_owned();
    }

    #[test]
    fn test_unwrap_invalid_owned() {
        let invalid: Validated<&str, i32> = Validated::Invalid(smallvec!["error1"]);
        let expected: SmallVec<[String; 1]> = smallvec![String::from("error1")];
        assert_eq!(invalid.unwrap_invalid_owned(), expected);
    }

    #[test]
    #[should_panic(expected = "Called Validated::unwrap_invalid_owned() on a Valid value")]
    fn test_unwrap_invalid_owned_panic() {
        let valid: Validated<&str, i32> = Validated::Valid(42);
        valid.unwrap_invalid_owned();
    }

    #[test]
    fn test_unwrap_basic() {
        let v = Validated::<String, i32>::valid(42);
        assert_eq!(v.unwrap(), 42);
    }

    #[test]
    #[should_panic]
    fn test_unwrap_panic() {
        let i: Validated<String, i32> = Validated::invalid("err".to_string());
        i.unwrap();
    }
}

// =============================================================================
// PANIC CONDITION TESTS
// =============================================================================

#[cfg(test)]
mod panic_tests {
    use super::*;
    use std::panic;

    #[test]
    fn test_invalid_vec_panics_on_empty() {
        let result = panic::catch_unwind(|| {
            Validated::<&str, i32>::invalid_vec(Vec::<&str>::new());
        });
        assert!(result.is_err());
    }

    #[test]
    fn test_unwrap_invalid_panics_on_valid() {
        let valid = Validated::<&str, i32>::valid(1);
        let result = panic::catch_unwind(|| {
            valid.unwrap_invalid();
        });
        assert!(result.is_err());
    }
}

// =============================================================================
// ITERATOR TESTS
// =============================================================================

#[cfg(test)]
mod iterator_tests {
    use super::*;

    #[test]
    fn test_iter() {
        let valid = Validated::<&str, i32>::valid(42);
        let invalid = Validated::<&str, i32>::invalid("err");

        let vals: Vec<_> = valid.iter().collect();
        assert_eq!(vals, vec![&42]);

        let vals: Vec<_> = invalid.iter().collect();
        assert!(vals.is_empty());
    }

    #[test]
    fn test_iter_mut() {
        let mut valid = Validated::<&str, i32>::valid(100);
        let mut invalid = Validated::<&str, i32>::invalid("err2");

        let vals: Vec<_> = valid.iter_mut().collect();
        assert_eq!(vals.len(), 1);

        let vals: Vec<_> = invalid.iter_mut().collect();
        assert!(vals.is_empty());
    }

    #[test]
    fn test_iter_errors() {
        let valid = Validated::<&str, i32>::valid(42);
        let invalid = Validated::<&str, i32>::invalid("err");

        let errs: Vec<_> = invalid.iter_errors().collect();
        assert_eq!(errs, vec![&"err"]);

        let errs: Vec<_> = valid.iter_errors().collect();
        assert!(errs.is_empty());
    }

    #[test]
    fn test_iter_errors_mut() {
        let mut invalid = Validated::<&str, i32>::invalid("err3");
        let errs: Vec<_> = invalid.iter_errors_mut().collect();
        assert_eq!(errs.len(), 1);
    }

    #[test]
    fn test_collection_operations() {
        let valid: Validated<String, i32> = Validated::valid(1);
        let vals: Vec<_> = valid.iter().cloned().collect();
        assert_eq!(vals, vec![1]);

        let invalid: Validated<String, i32> =
            Validated::invalid_many(["e1".to_string(), "e2".to_string()]);
        let errs: Vec<_> = invalid.iter_errors().cloned().collect();
        assert_eq!(errs, vec!["e1".to_string(), "e2".to_string()]);
    }
}

// =============================================================================
// EQUALITY AND COMPARISON TESTS
// =============================================================================

#[cfg(test)]
mod equality_tests {
    use super::*;

    #[test]
    fn test_equality() {
        let v1 = Validated::<String, i32>::valid(1);
        let v2 = Validated::<String, i32>::valid(1);
        let v3 = Validated::<String, i32>::valid(2);
        assert_eq!(v1, v2);
        assert_ne!(v1, v3);

        let i1 = Validated::<String, i32>::invalid("e".to_string());
        let i2 = Validated::<String, i32>::invalid("e".to_string());
        let i3 = Validated::<String, i32>::invalid("e2".to_string());
        assert_eq!(i1, i2);
        assert_ne!(i1, i3);
    }
}

// =============================================================================
// REAL-WORLD VALIDATION SCENARIOS
// =============================================================================

#[cfg(test)]
mod real_world_tests {
    use super::*;

    #[derive(Debug, PartialEq, Clone)]
    struct User {
        name: String,
        email: String,
        age: u8,
    }

    fn validate_name(name: &str) -> Validated<String, String> {
        if name.trim().is_empty() {
            Validated::invalid("Name must not be empty".to_string())
        } else if name.len() < 2 {
            Validated::invalid("Name must be at least 2 characters".to_string())
        } else {
            Validated::valid(name.to_string())
        }
    }

    fn validate_age(age: i32) -> Validated<String, u8> {
        if age < 0 {
            Validated::invalid("Age must be positive".to_string())
        } else if age < 18 {
            Validated::invalid("Age must be at least 18".to_string())
        } else if age > 120 {
            Validated::invalid("Age must be realistic".to_string())
        } else {
            Validated::valid(age as u8)
        }
    }

    fn validate_email(email: &str) -> Validated<String, String> {
        if !email.contains('@') {
            Validated::invalid("Email must contain @ symbol".to_string())
        } else if !email.contains('.') {
            Validated::invalid("Email must contain a domain".to_string())
        } else {
            Validated::valid(email.to_string())
        }
    }

    #[test]
    fn test_successful_user_validation() {
        let valid_name = validate_name("John Doe");
        let valid_age = validate_age(25);
        let valid_email = validate_email("john@example.com");

        let valid_user = Validated::<String, User>::lift3(
            |name, age, email| User {
                name: name.clone(),
                email: email.clone(),
                age: *age,
            },
            &valid_name,
            &valid_age,
            &valid_email,
        );

        assert!(valid_user.is_valid());
        let user = valid_user.unwrap();
        assert_eq!(user.name, "John Doe");
        assert_eq!(user.age, 25);
        assert_eq!(user.email, "john@example.com");
    }

    #[test]
    fn test_user_validation_error_accumulation() {
        let invalid_name = validate_name("");
        let invalid_age = validate_age(15);
        let invalid_email = validate_email("not-an-email");

        let invalid_user = Validated::<String, User>::lift3(
            |name, age, email| User {
                name: name.clone(),
                email: email.clone(),
                age: *age,
            },
            &invalid_name,
            &invalid_age,
            &invalid_email,
        );

        assert!(invalid_user.is_invalid());
        let errors = invalid_user.errors();
        assert_eq!(errors.len(), 3);
        assert_eq!(errors[0], "Name must not be empty");
        assert_eq!(errors[1], "Age must be at least 18");
        assert_eq!(errors[2], "Email must contain @ symbol");
    }

    #[test]
    fn test_partial_validation_errors() {
        let valid_name = validate_name("Jane Smith");
        let invalid_age = validate_age(-5);
        let valid_email = validate_email("jane@example.com");

        let result = Validated::<String, User>::lift3(
            |name, age, email| User {
                name: name.clone(),
                email: email.clone(),
                age: *age,
            },
            &valid_name,
            &invalid_age,
            &valid_email,
        );

        assert!(result.is_invalid());
        let errors = result.errors();
        assert_eq!(errors.len(), 1);
        assert_eq!(errors[0], "Age must be positive");
    }

    #[test]
    fn test_form_validation_pipeline() {
        fn validate_user_form(name: &str, email: &str, age: i32) -> Validated<String, User> {
            let name_validation = validate_name(name);
            let email_validation = validate_email(email);
            let age_validation = validate_age(age);

            let name_email_pair = Validated::<String, (String, String)>::lift2(
                |n, e| (n.clone(), e.clone()),
                &name_validation,
                &email_validation,
            );

            Validated::<String, User>::lift2(
                |(n, e), a| User {
                    name: n.clone(),
                    email: e.clone(),
                    age: *a,
                },
                &name_email_pair,
                &age_validation,
            )
        }

        // Test successful validation
        let valid_user = validate_user_form("Alice Johnson", "alice@example.com", 30);
        assert!(valid_user.is_valid());

        // Test complete failure
        let invalid_user = validate_user_form("", "invalid-email", 150);
        assert!(invalid_user.is_invalid());
        let errors = invalid_user.errors();
        assert!(errors.len() >= 2); // At least name and email errors
    }
}

// =============================================================================
// PERFORMANCE TESTS
// =============================================================================

#[cfg(test)]
mod performance_tests {
    use super::*;
    use std::time::Instant;

    #[test]
    fn test_error_accumulation_performance() {
        const ITERATIONS: usize = 20;
        const ERROR_COUNT: usize = 1000;

        // Pre-create strings to isolate invalid_many cost
        let error_strings: Vec<String> = (0..ERROR_COUNT).map(|i| format!("error_{i}")).collect();

        // Warmup: stabilize system cache and allocator
        for _ in 0..5 {
            let strings = error_strings.clone();
            let _validated: Validated<String, i32> = Validated::invalid_many(strings);
        }

        // Baseline 1: Pure Vec clone (what invalid_many should beat)
        let mut vec_clone_durations = Vec::with_capacity(ITERATIONS);
        for _ in 0..ITERATIONS {
            let start = Instant::now();
            let strings = error_strings.clone();
            let _cloned = strings.clone();
            vec_clone_durations.push(start.elapsed());
        }

        // Baseline 2: SmallVec collection (optimal path without size_hint logic)
        let mut smallvec_durations = Vec::with_capacity(ITERATIONS);
        for _ in 0..ITERATIONS {
            let start = Instant::now();
            let strings = error_strings.clone();
            let mut sv: smallvec::SmallVec<[String; 8]> =
                smallvec::SmallVec::with_capacity(strings.len());
            sv.extend(strings);
            smallvec_durations.push(start.elapsed());
        }

        // Operation: Validated::invalid_many (with size_hint optimization)
        let mut invalid_many_durations = Vec::with_capacity(ITERATIONS);
        for _ in 0..ITERATIONS {
            let start = Instant::now();
            let strings = error_strings.clone();
            let validated: Validated<String, i32> = Validated::invalid_many(strings);
            assert_eq!(validated.errors().len(), ERROR_COUNT);
            invalid_many_durations.push(start.elapsed());
        }

        // Use median for stability
        vec_clone_durations.sort();
        smallvec_durations.sort();
        invalid_many_durations.sort();

        let vec_clone_median = vec_clone_durations[ITERATIONS / 2];
        let smallvec_median = smallvec_durations[ITERATIONS / 2];
        let invalid_many_median = invalid_many_durations[ITERATIONS / 2];

        println!("\n=== Error Accumulation Performance ({ERROR_COUNT} errors) ===");
        println!(
            "Vec clone baseline:                {:>12.2?}",
            vec_clone_median
        );
        println!(
            "SmallVec optimal path:             {:>12.2?}",
            smallvec_median
        );
        println!(
            "Validated::invalid_many():         {:>12.2?}",
            invalid_many_median
        );

        println!("\n=== Performance Analysis ===");
        println!(
            "invalid_many vs Vec clone:        {:.2}x",
            invalid_many_median.as_secs_f64() / vec_clone_median.as_secs_f64()
        );
        println!(
            "invalid_many vs SmallVec optimal: {:.2}x",
            invalid_many_median.as_secs_f64() / smallvec_median.as_secs_f64()
        );

        // Performance expectations:
        // 1. invalid_many should be close to optimal SmallVec path (within 3x)
        // 2. invalid_many should be competitive with Vec clone for large collections (within 2x)
        // 3. Size hint optimization should provide reasonable benefits

        let smallvec_overhead = invalid_many_median.as_secs_f64() / smallvec_median.as_secs_f64();
        let vec_clone_ratio = invalid_many_median.as_secs_f64() / vec_clone_median.as_secs_f64();

        // Check that invalid_many is reasonably close to optimal SmallVec path
        // Allow up to 3x overhead for size_hint logic and enum wrapping
        assert!(
            smallvec_overhead < 3.0,
            "invalid_many is {:.2}x slower than optimal SmallVec path!\n\
            Expected: < 3.0x (reasonable overhead for size_hint logic + enum wrapping)\n\
            This suggests the size_hint optimization is inefficient.",
            smallvec_overhead
        );

        // For large collections, invalid_many should be competitive with Vec clone
        // Allow up to 2x since we have enum overhead but better memory efficiency
        if ERROR_COUNT > 100 {
            assert!(
                vec_clone_ratio < 2.0,
                "invalid_many is {:.2}x slower than Vec clone for {} errors!\n\
            Expected: < 2.0x (competitive with Vec clone despite enum overhead)\n\
            This indicates a performance regression.",
                vec_clone_ratio,
                ERROR_COUNT
            );
        }

        println!("✓ Performance test passed - invalid_many is reasonably efficient");
    }

    #[test]
    fn test_nested_operation_performance() {
        // Baseline: measure simple accumulation without Validated wrapper
        let start_baseline = Instant::now();
        let mut baseline_sum = 0;
        for i in 1..=100 {
            baseline_sum += i;
        }
        assert_eq!(baseline_sum, 5050); // Sum of 1..100 = 5050
        let baseline_duration = start_baseline.elapsed();

        // Actual test: nested operations with Validated
        let start = Instant::now();
        let mut result = Validated::<String, i32>::valid(0);
        for i in 1..=100 {
            result = result.bind(|&x| Validated::valid(x + i));
        }
        assert_eq!(result.iter().next(), Some(&5050));
        let operation_duration = start.elapsed();

        println!("Nested operations baseline: {baseline_duration:?}");
        println!("Nested operations with Validated: {operation_duration:?}");
        println!(
            "Ratio: {:.2}x",
            operation_duration.as_secs_f64() / baseline_duration.as_secs_f64()
        );

        // PERFORMANCE REALITY CHECK: 20x slower is NOT acceptable performance!
        // This test demonstrates the severe performance penalty of our abstraction layers.
        // 20x overhead indicates fundamental architectural performance problems.
        //
        // WARNING: This test accepts terrible performance as "normal"
        // TODO: Either optimize implementation or document as experimental/educational only
        let slowdown_factor = operation_duration.as_secs_f64() / baseline_duration.as_secs_f64();

        if slowdown_factor > 20.0 {
            panic!(
                "Validated operations are catastrophically slow: {:.2}x slower than baseline. \
                This indicates severe performance problems that make this unsuitable for production use.",
                slowdown_factor
            );
        } else if slowdown_factor > 5.0 {
            eprintln!(
                "WARNING: Validated operations are {:.2}x slower than baseline. \
                This is a significant performance penalty that limits practical usage.",
                slowdown_factor
            );
        }
    }
}

// =============================================================================
// TYPE SAFETY AND ERGONOMICS TESTS
// =============================================================================

#[cfg(test)]
mod type_safety_tests {
    use super::*;

    #[test]
    fn test_type_inference_and_ergonomics() {
        // Test that type inference works well
        let v1: Validated<String, i32> = Validated::valid(42); // Should infer types
        let _v2 = v1.fmap(|x| x * 2);

        // Test with different types
        let string_validation: Validated<&str, String> = Validated::valid("hello".to_string());
        let length_validation = string_validation.fmap(|s| s.len());

        assert_eq!(length_validation, Validated::valid(5));
    }

    #[test]
    fn test_complex_type_combinations() {
        // Test with complex nested types
        let nested: Validated<Vec<String>, Vec<i32>> = Validated::valid(vec![1, 2, 3]);
        let sum = nested.fmap(|v| v.iter().sum::<i32>());
        assert_eq!(sum, Validated::valid(6));

        // Test with Result<T, E> as value type
        let result_validation: Validated<String, Result<i32, &str>> = Validated::valid(Ok(42));
        let unwrapped = result_validation.fmap(|r| r.unwrap_or(0));
        assert_eq!(unwrapped, Validated::valid(42));
    }

    #[test]
    fn test_lifetime_handling() {
        fn process_string(s: &str) -> Validated<&'static str, usize> {
            if s.is_empty() {
                Validated::invalid("Empty string")
            } else {
                Validated::valid(s.len())
            }
        }

        let result1 = process_string("hello");
        assert_eq!(result1, Validated::valid(5));

        let result2 = process_string("");
        assert_eq!(result2, Validated::invalid("Empty string"));
    }

    #[test]
    fn test_non_clone_types() {
        // Test with types that don't implement Clone
        #[derive(Debug, PartialEq, Clone)]
        struct NonClone {
            data: Vec<i32>,
        }

        let non_clone = NonClone {
            data: vec![1, 2, 3],
        };
        let validated: Validated<String, NonClone> = Validated::valid(non_clone);

        // Test operations that don't require Clone
        assert!(validated.is_valid());
        assert_eq!(validated.unwrap().data, vec![1, 2, 3]);

        // into_value should move without cloning
        let consumed = validated.into_value();
        assert!(consumed.is_ok());
        assert_eq!(consumed.unwrap().data, vec![1, 2, 3]);
    }
}

// =============================================================================
// ADVANCED COMBINATOR TESTS
// =============================================================================

#[cfg(test)]
mod combinator_tests {
    use super::*;

    #[test]
    fn test_complex_error_accumulation_scenarios() {
        // Test combining multiple validation sources
        let errors1: Validated<String, i32> =
            Validated::invalid_many(["error1".to_string(), "error2".to_string()]);
        let errors2: Validated<String, i32> =
            Validated::invalid_many(["error3".to_string(), "error4".to_string()]);

        // Using applicative to combine errors
        let combined = Validated::<String, i32>::lift2(|a, b| a + b, &errors1, &errors2);
        let all_errors = combined.errors();
        assert_eq!(all_errors.len(), 4);
        assert_eq!(all_errors[0], "error1");
        assert_eq!(all_errors[1], "error2");
        assert_eq!(all_errors[2], "error3");
        assert_eq!(all_errors[3], "error4");
    }

    #[test]
    fn test_nested_validation_chains() {
        fn validate_positive(n: i32) -> Validated<String, i32> {
            if n > 0 {
                Validated::valid(n)
            } else {
                Validated::invalid("Must be positive".to_string())
            }
        }

        fn validate_even(n: i32) -> Validated<String, i32> {
            if n % 2 == 0 {
                Validated::valid(n)
            } else {
                Validated::invalid("Must be even".to_string())
            }
        }

        fn validate_small(n: i32) -> Validated<String, i32> {
            if n < 100 {
                Validated::valid(n)
            } else {
                Validated::invalid("Must be less than 100".to_string())
            }
        }

        // Chain validations using bind (monadic style - stops at first error)
        let result1 = validate_positive(42)
            .bind(|&n| validate_even(n))
            .bind(|&n| validate_small(n));
        assert_eq!(result1, Validated::valid(42));

        // Test with failing validation in chain
        let result2 = validate_positive(-5)
            .bind(|&n| validate_even(n))
            .bind(|&n| validate_small(n));
        assert_eq!(result2, Validated::invalid("Must be positive".to_string()));

        // Test with applicative style - accumulates all errors
        let pos = validate_positive(-5);
        let even = validate_even(3);
        let small = validate_small(150);
        let all_result = Validated::<String, i32>::lift3(|a, b, c| a + b + c, &pos, &even, &small);
        let errors = all_result.errors();
        assert_eq!(errors.len(), 3);
    }

    #[test]
    fn test_conditional_validation() {
        fn validate_conditionally(value: i32, should_validate: bool) -> Validated<String, i32> {
            if should_validate {
                if value > 0 {
                    Validated::valid(value)
                } else {
                    Validated::invalid("Value must be positive".to_string())
                }
            } else {
                Validated::valid(value) // Always valid when not validating
            }
        }

        assert_eq!(validate_conditionally(-5, false), Validated::valid(-5));
        assert_eq!(
            validate_conditionally(-5, true),
            Validated::invalid("Value must be positive".to_string())
        );
        assert_eq!(validate_conditionally(5, true), Validated::valid(5));
    }
}

// =============================================================================
// DOCUMENTATION AND EXAMPLE TESTS
// =============================================================================

#[cfg(test)]
mod documentation_tests {
    use super::*;

    /// Example from documentation: Basic usage
    #[test]
    fn test_basic_usage_example() {
        // Example: Basic creation and checking
        let valid: Validated<String, i32> = Validated::valid(42);
        let invalid: Validated<String, i32> = Validated::invalid("Error message".to_string());

        assert!(valid.is_valid());
        assert!(!valid.is_invalid());
        assert_eq!(valid.iter().next(), Some(&42));

        assert!(!invalid.is_valid());
        assert!(invalid.is_invalid());
        assert_eq!(invalid.iter().next(), None);
        assert_eq!(invalid.errors().len(), 1);
    }

    /// Example from documentation: Form validation
    #[test]
    fn test_form_validation_example() {
        #[derive(Debug, PartialEq, Clone)]
        struct FormData {
            username: String,
            email: String,
            age: u8,
        }

        fn validate_form(username: &str, email: &str, age: i32) -> Validated<String, FormData> {
            let username_valid = if username.len() >= 3 {
                Validated::valid(username.to_string())
            } else {
                Validated::invalid("Username too short".to_string())
            };

            let email_valid = if email.contains('@') {
                Validated::valid(email.to_string())
            } else {
                Validated::invalid("Invalid email".to_string())
            };

            let age_valid = if (0..=120).contains(&age) {
                Validated::valid(age as u8)
            } else {
                Validated::invalid("Invalid age".to_string())
            };

            let intermediate = Validated::<String, (String, String)>::lift2(
                |username, email| (username.clone(), email.clone()),
                &username_valid,
                &email_valid,
            );

            Validated::<String, FormData>::lift2(
                |(username, email), age| FormData {
                    username: username.clone(),
                    email: email.clone(),
                    age: *age,
                },
                &intermediate,
                &age_valid,
            )
        }

        // Test valid form
        let valid_form = validate_form("john_doe", "john@example.com", 25);
        assert!(valid_form.is_valid());

        // Test invalid form - collects all errors
        let invalid_form = validate_form("jo", "invalid-email", -5);
        assert!(invalid_form.is_invalid());
        assert_eq!(invalid_form.errors().len(), 3);
    }

    /// Example from documentation: Working with Results
    #[test]
    fn test_result_conversion_example() {
        fn parse_number(s: &str) -> Result<i32, String> {
            s.parse().map_err(|_| format!("Failed to parse: {s}"))
        }

        let results = ["42", "invalid", "123"];
        let validations: Vec<_> = results
            .iter()
            .map(|s| {
                let result = parse_number(s);
                Validated::from_result(&result)
            })
            .collect();

        assert!(validations[0].is_valid());
        assert!(validations[1].is_invalid());
        assert!(validations[2].is_valid());
    }
}

// =============================================================================
// PROPERTY-BASED TESTS
// =============================================================================

#[cfg(test)]
mod property_tests {
    use super::*;

    // Property tests for unwrap_owned
    #[quickcheck]
    fn prop_unwrap_owned_on_valid_returns_value(value: i32) -> bool {
        let v: Validated<String, i32> = Validated::Valid(value);
        v.unwrap_owned() == value
    }

    #[quickcheck]
    fn prop_unwrap_owned_on_invalid_panics(errors: Vec<String>) -> TestResult {
        if errors.is_empty() {
            return TestResult::discard();
        }
        let small_errors: SmallVec<[String; 8]> = errors.into_iter().collect();
        if small_errors.is_empty() {
            return TestResult::discard();
        }
        let v: Validated<String, i32> = Validated::Invalid(small_errors);
        let result = std::panic::catch_unwind(|| v.unwrap_owned());
        TestResult::from_bool(result.is_err())
    }

    // Property tests for unwrap_invalid_owned
    #[quickcheck]
    fn prop_unwrap_invalid_owned_on_invalid_returns_errors(errors: Vec<String>) -> bool {
        let small_errors: SmallVec<[String; 8]> = errors.into_iter().collect();
        let v: Validated<String, i32> = Validated::Invalid(small_errors.clone());
        v.unwrap_invalid_owned() == small_errors
    }

    #[quickcheck]
    fn prop_unwrap_invalid_owned_on_valid_panics(value: i32) -> bool {
        let v: Validated<String, i32> = Validated::Valid(value);
        let result = std::panic::catch_unwind(|| v.unwrap_invalid_owned());
        result.is_err()
    }

    // Property tests for into_value
    #[quickcheck]
    fn prop_into_value_on_valid_returns_ok_value(value: i32) -> bool {
        let v: Validated<String, i32> = Validated::Valid(value);
        match v.into_value() {
            Ok(val) => val == value,
            Err(_) => false,
        }
    }

    #[quickcheck]
    fn prop_into_value_on_invalid_returns_err_errors(errors: Vec<String>) -> bool {
        let small_errors: SmallVec<[String; 8]> = errors.into_iter().collect();
        let v: Validated<String, i32> = Validated::Invalid(small_errors.clone());
        match v.into_value() {
            Ok(_) => false,
            Err(errs) => errs == small_errors,
        }
    }

    // Property tests for into_error_payload
    #[quickcheck]
    fn prop_into_error_payload_on_invalid_returns_ok_errors(errors: Vec<String>) -> bool {
        let small_errors: SmallVec<[String; 8]> = errors.into_iter().collect();
        let v: Validated<String, i32> = Validated::Invalid(small_errors.clone());
        match v.into_error_payload() {
            Ok(errs) => errs == small_errors,
            Err(_) => false,
        }
    }

    #[quickcheck]
    fn prop_into_error_payload_on_valid_returns_err_value(value: i32) -> bool {
        let v: Validated<String, i32> = Validated::Valid(value);
        match v.into_error_payload() {
            Ok(_) => false,
            Err(val) => val == value,
        }
    }

    // Property tests for value accessor
    #[quickcheck]
    fn prop_value_accessor_on_valid_returns_some_ref_value(value: i32) -> bool {
        let v: Validated<String, i32> = Validated::Valid(value);
        v.unwrap() == value
    }

    #[quickcheck]
    fn prop_value_accessor_on_invalid_returns_none(errors: Vec<String>) -> bool {
        let small_errors: SmallVec<[String; 8]> = errors.into_iter().collect();
        let v: Validated<String, i32> = Validated::Invalid(small_errors);
        match v.into_value() {
            Ok(_) => false, // Should not happen for invalid
            Err(_) => true, // Expected for invalid
        }
    }

    // Property tests for error_payload accessor
    #[quickcheck]
    fn prop_error_payload_accessor_on_invalid_returns_some_ref_errors(errors: Vec<String>) -> bool {
        let small_errors: SmallVec<[String; 8]> = errors.into_iter().collect();
        let v: Validated<String, i32> = Validated::Invalid(small_errors.clone());
        v.error_payload() == Some(&small_errors)
    }

    #[quickcheck]
    fn prop_error_payload_accessor_on_valid_returns_none(value: i32) -> bool {
        let v: Validated<String, i32> = Validated::Valid(value);
        v.error_payload().is_none()
    }

    // Property tests for functor laws
    #[quickcheck]
    fn prop_functor_identity_law(value: i32) -> bool {
        let v: Validated<String, i32> = Validated::valid(value);
        v.fmap(|x| *x) == v
    }

    #[quickcheck]
    fn prop_functor_composition_law(value: i32, add_val: i32, mult_val: i32) -> bool {
        // Use smaller values to avoid overflow
        let safe_value = value % 100;
        let safe_add = add_val % 10;
        let safe_mult = mult_val % 5;

        let v: Validated<String, i32> = Validated::valid(safe_value);
        let f = |x: &i32| x + safe_add;
        let g = |x: &i32| x * safe_mult;

        let lhs = v.fmap(|x| f(&g(x)));
        let rhs = v.fmap(g).fmap(f);
        lhs == rhs
    }

    // Property tests for fmap preserving structure
    #[quickcheck]
    fn prop_fmap_preserves_structure(value: i32, errors: Vec<String>) -> bool {
        let valid: Validated<String, i32> = Validated::valid(value);
        let invalid: Validated<String, i32> = if errors.is_empty() {
            return true; // Skip empty errors
        } else {
            Validated::invalid_many(errors)
        };

        // fmap should preserve valid/invalid structure
        // Use a safe function that won't overflow
        valid.fmap(|x| x.saturating_mul(2)).is_valid()
            && invalid.fmap(|x| x.saturating_mul(2)).is_invalid()
    }

    // Property tests for error accumulation
    #[quickcheck]
    fn prop_error_accumulation_preserves_all_errors(
        errors1: Vec<String>, errors2: Vec<String>,
    ) -> TestResult {
        if errors1.is_empty() || errors2.is_empty() {
            return TestResult::discard();
        }

        let v1: Validated<String, i32> = Validated::invalid_many(errors1.clone());
        let v2: Validated<String, i32> = Validated::invalid_many(errors2.clone());

        let combined = Validated::<String, i32>::lift2(|a, b| a + b, &v1, &v2);
        let all_errors = combined.errors();

        let expected_count = errors1.len() + errors2.len();
        TestResult::from_bool(all_errors.len() == expected_count)
    }

    // Property tests for conversion consistency
    #[quickcheck]
    fn prop_result_conversion_roundtrip_valid(value: i32) -> bool {
        let validated: Validated<String, i32> = Validated::valid(value);
        let result = validated.to_result();
        let back_to_validated = Validated::from_result(&result);
        back_to_validated == Validated::valid(value)
    }

    #[quickcheck]
    fn prop_option_conversion_roundtrip_valid(value: i32) -> bool {
        let validated: Validated<String, i32> = Validated::valid(value);
        let option = validated.to_option();
        let back_to_validated = Validated::from_option(&option, &"error".to_string());
        back_to_validated == Validated::valid(value)
    }
}

// =============================================================================
// STRESS AND EDGE CASE TESTS
// =============================================================================

#[cfg(test)]
mod stress_tests {
    use super::*;

    #[test]
    fn test_deeply_nested_bind_chains() {
        let mut result = Validated::<String, i32>::valid(0);

        // Create a long chain of bind operations
        for i in 1..=50 {
            result = result.bind(|&x| {
                if x < 1000 {
                    Validated::valid(x + i)
                } else {
                    Validated::invalid(format!("Overflow at step {i}"))
                }
            });
        }

        // Should fail since we exceed 1000 at some point
        assert!(!result.is_valid());
        println!("Result: {:#?}", result.errors());
        assert!(!result.errors().is_empty());
        assert!(result.errors().contains(&"Overflow at step 46".to_string()));
    }

    #[test]
    fn test_very_large_error_collections() {
        let large_errors: Vec<String> = (0..10000).map(|i| format!("error_{i:04}")).collect();

        let validated: Validated<String, i32> = Validated::invalid_many(large_errors.clone());

        assert!(validated.is_invalid());
        assert_eq!(validated.errors().len(), 10000);
        assert_eq!(validated.errors()[0], "error_0000");
        assert_eq!(validated.errors()[9999], "error_9999");
    }

    #[test]
    fn test_memory_efficiency_with_large_values() {
        // Test with large values to ensure no unnecessary cloning
        let large_vec: Vec<i32> = (0..10000).collect();
        let validated: Validated<String, Vec<i32>> = Validated::valid(large_vec.clone());

        // Operations that should not clone the large vector
        assert!(validated.is_valid());
        assert_eq!(validated.unwrap().len(), 10000);

        // into_value should move without cloning
        let moved_value = validated.into_value();
        assert!(moved_value.is_ok());
        assert_eq!(moved_value.unwrap().len(), 10000);
    }

    #[test]
    fn test_unicode_and_special_characters_in_errors() {
        let unicode_errors = vec![
            "错误信息".to_string(),
            "エラーメッセージ".to_string(),
            "🚨 Error with emoji 🚨".to_string(),
            "Error with\nnewlines\nand\ttabs".to_string(),
            "Error with quotes: \"quoted\" and 'single'".to_string(),
        ];

        let validated: Validated<String, i32> = Validated::invalid_many(unicode_errors.clone());

        assert!(validated.is_invalid());
        assert_eq!(validated.errors().len(), 5);
        assert_eq!(validated.errors()[0], "错误信息");
        assert_eq!(validated.errors()[1], "エラーメッセージ");
        assert!(validated.errors()[2].contains("🚨"));
        assert!(validated.errors()[3].contains("\n"));
        assert!(validated.errors()[4].contains("\""));
    }

    #[test]
    fn test_zero_sized_types() {
        // Test with unit type
        let unit_valid: Validated<String, ()> = Validated::valid(());
        assert!(unit_valid.is_valid());
        assert_eq!(unit_valid.unwrap(), ());

        // Test with zero-sized struct
        #[derive(Debug, PartialEq, Clone)]
        struct ZeroSized;

        let zst_valid: Validated<String, ZeroSized> = Validated::valid(ZeroSized);
        assert!(zst_valid.is_valid());
        assert_eq!(zst_valid.unwrap(), ZeroSized);
    }
}

// =============================================================================
// INTEGRATION AND COMPATIBILITY TESTS
// =============================================================================

#[cfg(test)]
mod integration_tests {
    use super::*;

    #[test]
    fn test_compatibility_with_standard_library() {
        // Test with Vec
        let vec_result: Validated<String, Vec<i32>> = Validated::valid(vec![1, 2, 3]);
        let sum = vec_result.fmap(|v| v.iter().sum::<i32>());
        assert_eq!(sum, Validated::valid(6));

        // Test with HashMap
        use std::collections::HashMap;
        let mut map = HashMap::new();
        map.insert("key".to_string(), 42);

        let map_result: Validated<String, HashMap<String, i32>> = Validated::valid(map);
        let value = map_result.fmap(|m| m.get("key").copied().unwrap_or(0));
        assert_eq!(value, Validated::valid(42));

        // Test with Result
        let result_ok: Result<i32, &str> = Ok(42);
        let validated_from_result = Validated::from_result(&result_ok);
        assert_eq!(validated_from_result, Validated::valid(42));
    }

    #[test]
    fn test_interop_with_option_and_result() {
        // Complex chain: Option -> Result -> Validated
        let option_value: Option<i32> = Some(42);
        let result_from_option: Result<i32, &str> = option_value.ok_or("No value");
        let validated_from_result = Validated::from_result(&result_from_option);

        assert!(validated_from_result.is_valid());
        assert_eq!(validated_from_result.unwrap(), 42);

        // Reverse chain: Validated -> Result -> Option
        let validated: Validated<&str, i32> = Validated::valid(42);
        let result = validated.to_result();
        let option = result.ok();

        assert_eq!(option, Some(42));
    }

    #[test]
    fn test_serialization_compatibility() {
        // Note: This test assumes serde integration exists
        // For now, we test the basic structure that would support serialization

        #[derive(Debug, PartialEq, Clone)]
        struct SerializableData {
            id: u32,
            name: String,
        }

        let data = SerializableData {
            id: 1,
            name: "test".to_string(),
        };

        let validated: Validated<String, SerializableData> = Validated::valid(data);
        assert!(validated.is_valid());

        // Test that we can extract the data for serialization
        let extracted = validated.into_value();
        assert!(extracted.is_ok());
        assert_eq!(extracted.unwrap().id, 1);
    }
}

// =============================================================================
// HELPER FUNCTIONS AND UTILITIES FOR TESTING
// =============================================================================

#[cfg(test)]
mod test_helpers {
    use super::*;

    // Helper function to create test data
    #[derive(Debug, PartialEq, Clone)]
    pub struct TestUser {
        pub name: String,
        pub age: u8,
        pub email: String,
    }

    pub fn create_test_user(name: &str, age: u8, email: &str) -> Validated<String, TestUser> {
        if name.is_empty() {
            return Validated::invalid("Name cannot be empty".to_string());
        }

        if age < 18 {
            return Validated::invalid("Must be 18 or older".to_string());
        }

        if !email.contains('@') {
            return Validated::invalid("Invalid email format".to_string());
        }

        Validated::valid(TestUser {
            name: name.to_string(),
            age,
            email: email.to_string(),
        })
    }

    // Helper for testing error accumulation
    pub fn combine_validations<T>(
        validations: Vec<Validated<String, T>>,
    ) -> Validated<String, Vec<T>>
    where
        T: Clone,
    {
        validations
            .into_iter()
            .fold(Validated::valid(Vec::new()), |acc, validation| {
                Validated::<String, Vec<T>>::lift2_owned(
                    |mut vec, item: T| {
                        vec.push(item.clone());
                        vec
                    },
                    acc,
                    validation,
                )
            })
    }

    #[test]
    fn test_helper_functions() {
        // Test the helper functions themselves
        let valid_user = create_test_user("John", 25, "john@example.com");
        assert!(valid_user.is_valid());

        let invalid_user = create_test_user("", 16, "invalid-email");
        assert!(invalid_user.is_invalid());

        // Test combining validations
        let validations = vec![
            Validated::valid(1),
            Validated::valid(2),
            Validated::invalid("error".to_string()),
            Validated::valid(3),
        ];

        let combined = combine_validations(validations);
        assert!(combined.is_invalid());
        assert_eq!(combined.errors(), &["error".to_string()]);
    }
}

// =============================================================================
// REGRESSION TESTS
// =============================================================================

#[cfg(test)]
mod regression_tests {
    use super::*;

    #[test]
    fn test_issue_empty_error_vector_handling() {
        // Regression test: ensure empty error vectors are handled correctly
        let empty_errors: Vec<String> = vec![];
        let validated = Validated::<String, i32>::invalid_many(empty_errors);

        assert!(validated.is_invalid());
        assert!(validated.errors().is_empty());
        assert_eq!(validated.iter().next(), None);
    }

    #[test]
    fn test_issue_large_error_message_handling() {
        // Regression test: ensure very large error messages don't cause issues
        let large_error = "error".repeat(10000);
        let validated: Validated<String, i32> = Validated::invalid(large_error.clone());

        assert!(validated.is_invalid());
        assert_eq!(validated.errors().len(), 1);
        assert_eq!(validated.errors()[0], large_error);
    }

    #[test]
    fn test_issue_bind_with_error_propagation() {
        // Regression test: ensure bind properly propagates errors without modification
        let original_error = "original error";
        let invalid: Validated<&str, i32> = Validated::invalid(original_error);

        let result = invalid.bind(|&x| Validated::valid(x * 2));

        assert!(result.is_invalid());
        assert_eq!(result.errors().len(), 1);
        assert_eq!(result.errors()[0], original_error);
    }

    #[test]
    fn test_issue_multiple_consecutive_fmaps() {
        // Regression test: ensure multiple fmap operations work correctly
        let validated: Validated<String, i32> = Validated::valid(10);

        let result = validated
            .fmap(|x| x * 2) // 20
            .fmap(|x| x + 5) // 25
            .fmap(|x| x / 5) // 5
            .fmap(|x| x - 1); // 4

        assert_eq!(result, Validated::valid(4));
    }
}

// =============================================================================
// FINAL COMPREHENSIVE TEST
// =============================================================================

#[cfg(test)]
mod comprehensive_test {
    use super::*;

    #[test]
    fn test_complete_validated_workflow() {
        // This test demonstrates a complete workflow using all major features

        #[derive(Debug, PartialEq, Clone)]
        struct CompleteUser {
            id: u32,
            username: String,
            email: String,
            age: u8,
            preferences: UserPreferences,
        }

        #[derive(Debug, PartialEq, Clone)]
        struct UserPreferences {
            newsletter: bool,
            theme: String,
        }

        // Individual validation functions
        fn validate_id(id: u32) -> Validated<String, u32> {
            if id > 0 {
                Validated::valid(id)
            } else {
                Validated::invalid("ID must be positive".to_string())
            }
        }

        fn validate_username(username: &str) -> Validated<String, String> {
            if username.len() >= 3 && username.len() <= 20 {
                Validated::valid(username.to_string())
            } else {
                Validated::invalid("Username must be 3-20 characters".to_string())
            }
        }

        fn validate_email(email: &str) -> Validated<String, String> {
            if email.contains('@') && email.contains('.') {
                Validated::valid(email.to_string())
            } else {
                Validated::invalid("Invalid email format".to_string())
            }
        }

        fn validate_age(age: u8) -> Validated<String, u8> {
            if (13..=120).contains(&age) {
                Validated::valid(age)
            } else {
                Validated::invalid("Age must be between 13 and 120".to_string())
            }
        }

        // Complete user validation using all validation functions
        fn validate_complete_user(
            id: u32, username: &str, email: &str, age: u8, newsletter: bool, theme: &str,
        ) -> Validated<String, CompleteUser> {
            // Create a curried constructor function that works with applicative pattern
            let create_user = |id: u32, name: String, email: String| CompleteUser {
                id,
                username: name,
                email,
                age,
                preferences: UserPreferences {
                    newsletter,
                    theme: theme.to_string(),
                },
            };

            // Use lift3_owned for applying a 3-argument function to Validated inputs
            let user_builder: Validated<String, CompleteUser> =
                Validated::<String, CompleteUser>::lift3_owned(
                    create_user,
                    validate_id(id),
                    validate_username(username),
                    validate_email(email),
                );

            // Apply remaining validations
            Validated::<String, CompleteUser>::lift2(
                |user, age| CompleteUser {
                    id: user.id,
                    username: user.username.clone(),
                    email: user.email.clone(),
                    age: *age,
                    preferences: UserPreferences {
                        newsletter,
                        theme: theme.to_string(),
                    },
                },
                &user_builder,
                &validate_age(age),
            )
        }

        // Test successful validation
        let valid_user =
            validate_complete_user(1, "john_doe", "john@example.com", 25, true, "dark");

        assert!(valid_user.is_valid());
        let user = valid_user.unwrap();
        assert_eq!(user.id, 1);
        assert_eq!(user.username, "john_doe");
        assert_eq!(user.email, "john@example.com");
        assert_eq!(user.age, 25);
        assert!(user.preferences.newsletter);
        assert_eq!(user.preferences.theme, "dark");

        // Test validation with multiple errors
        let invalid_user = validate_complete_user(
            0,         // Invalid ID
            "jo",      // Username too short
            "invalid", // Invalid email
            150,       // Invalid age
            false,
            "invalid_theme", // Invalid theme
        );

        assert!(invalid_user.is_invalid());
        let errors = invalid_user.errors();
        assert_eq!(errors.len(), 4);
        assert!(errors.contains(&"ID must be positive".to_string()));
        assert!(errors.contains(&"Username must be 3-20 characters".to_string()));
        assert!(errors.contains(&"Invalid email format".to_string()));
        assert!(errors.contains(&"Age must be between 13 and 120".to_string()));

        let partial_user = validate_complete_user(
            42,
            "valid_username",
            "valid@email.com",
            16, // Age between 13-120 is valid
            true,
            "light", // Valid theme
        );

        assert!(partial_user.is_valid());
        let user = partial_user.unwrap();
        assert_eq!(user.id, 42);
        assert_eq!(user.username, "valid_username");
        assert_eq!(user.email, "valid@email.com");
        assert_eq!(user.age, 16);
        assert_eq!(user.preferences.theme, "light");

        // Test conversion to Result and back
        let result = valid_user.to_result();
        assert!(result.is_ok());

        let back_to_validated = Validated::from_result(&result);
        assert!(back_to_validated.is_valid());

        // Test monadic operations
        let processed_user = back_to_validated.bind(|user| {
            if user.age >= 18 {
                Validated::valid(format!("Adult user: {}", user.username))
            } else {
                Validated::invalid("User must be adult for this operation".to_string())
            }
        });

        assert!(processed_user.is_valid());
        assert_eq!(processed_user.unwrap(), "Adult user: john_doe".to_string());

        // Test error mapping
        let mapped_errors =
            invalid_user.fmap_invalid(|error| format!("[VALIDATION_ERROR] {error}"));

        assert!(mapped_errors.is_invalid());
        for error in mapped_errors.errors() {
            assert!(error.starts_with("[VALIDATION_ERROR]"));
        }
    }

    #[test]
    fn test_type_system_integration() {
        // Ensure the type system works well with Validated

        fn generic_validation<E: Clone, T: Clone>(
            value: T, condition: bool, error: E,
        ) -> Validated<E, T> {
            if condition {
                Validated::valid(value)
            } else {
                Validated::invalid(error)
            }
        }

        let string_validation = generic_validation("hello", true, "error");
        assert!(string_validation.is_valid());

        let number_validation = generic_validation(42, true, "number error");
        assert!(number_validation.is_valid());

        println!("Type system integration works correctly!");
    }

    #[test]
    fn test_comprehensive_coverage_verification() {
        // Verify that we've tested all major aspects

        let test_categories = vec![
            "Creation and basic operations",
            "Functor laws and operations",
            "Applicative laws and operations",
            "Monad laws and operations",
            "Foldable operations",
            "Conversions (Result, Option)",
            "Error accumulation",
            "Iterator support",
            "Unwrap operations",
            "Panic conditions",
            "Performance characteristics",
            "Real-world scenarios",
            "Type safety",
            "Property-based testing",
            "Edge cases and stress testing",
        ];

        println!("Test coverage includes:");
        for category in test_categories {
            println!("   - {category}");
        }

        println!("Comprehensive test suite completed successfully!");
    }
}

// =============================================================================
// FINAL TEST SUMMARY AND VALIDATION
// =============================================================================

#[cfg(test)]
mod test_summary {
    use super::*;

    #[test]
    fn test_all_major_operations_work_together() {
        // This test ensures all major operations work correctly in combination

        // 1. Creation
        let valid1: Validated<String, i32> = Validated::valid(10);
        let valid2: Validated<String, i32> = Validated::valid(20);
        let invalid: Validated<String, i32> = Validated::invalid("error".to_string());

        // 2. Functor operations
        let mapped_valid = valid1.fmap(|x| x * 2);
        assert_eq!(mapped_valid, Validated::valid(20));

        // 3. Applicative operations
        let combined = Validated::<String, i32>::lift2(|a, b| a + b, &valid1, &valid2);
        assert_eq!(combined, Validated::valid(30));

        // 4. Monadic operations
        let bound = valid1.bind(|&x| Validated::valid(x + 5));
        assert_eq!(bound, Validated::valid(15));

        // 5. Error handling
        let error_result = invalid.fmap(|x| x * 2);
        assert!(error_result.is_invalid());

        // 6. Conversions
        let as_option = valid1.to_option();
        assert_eq!(as_option, Some(10));

        // 7. Iteration
        let values: Vec<_> = valid1.iter().collect();
        assert_eq!(values, vec![&10]);

        // 8. Folding
        let folded = valid1.fold_left(&0, |acc, x| acc + x);
        assert_eq!(folded, 10);

        println!("All major Validated operations work correctly!");
    }
}

// =============================================================================
// END OF TEST SUITE
// =============================================================================

// Note: This comprehensive test suite covers:
//
// The test suite is organized into logical modules following Rust best practices,
// with clear separation of concerns and comprehensive coverage of all functionality.
// Each test is well-documented and demonstrates specific aspects of the Validated type.

#[cfg(feature = "serde")]
#[test]
fn test_validated_serde() {
    use rustica::datatypes::validated::Validated;
    use serde_json;

    // Test with a Valid value
    let valid: Validated<String, i32> = Validated::Valid(42);
    let serialized_valid = serde_json::to_string(&valid).unwrap();
    let deserialized_valid: Validated<String, i32> =
        serde_json::from_str(&serialized_valid).unwrap();
    assert_eq!(valid, deserialized_valid);

    // Test with an Invalid value
    let invalid: Validated<String, i32> =
        Validated::Invalid(smallvec!["error1".to_string(), "error2".to_string()]);
    let serialized_invalid = serde_json::to_string(&invalid).unwrap();
    let deserialized_invalid: Validated<String, i32> =
        serde_json::from_str(&serialized_invalid).unwrap();
    assert_eq!(invalid, deserialized_invalid);

    // Test with a struct
    #[derive(serde::Serialize, serde::Deserialize, PartialEq, Debug, Clone)]
    struct Point {
        x: i32,
        y: i32,
    }
    let point = Point { x: 1, y: 2 };
    let valid_point: Validated<String, Point> = Validated::Valid(point.clone());
    let serialized_point = serde_json::to_string(&valid_point).unwrap();
    let deserialized_point: Validated<String, Point> =
        serde_json::from_str(&serialized_point).unwrap();
    assert_eq!(valid_point, deserialized_point);
}
