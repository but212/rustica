use quickcheck_macros::quickcheck;
use rustica::datatypes::validated::Validated;
use rustica::prelude::*;

// --- Core Algebraic Laws & Properties ---

#[test]
fn test_validated_basic_logic() {
    let v: Validated<String, i32> = Validated::valid(42);
    let i: Validated<String, i32> = Validated::invalid("err".into());

    assert!(v.is_valid());
    assert!(i.is_invalid());
    assert_eq!(v.unwrap(), 42);
    assert_eq!(i.errors(), &["err".to_string()]);
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

// --- Accumulation & Traversal (The Core USP) ---

#[test]
fn test_validated_error_accumulation() {
    let v1: Validated<String, i32> = Validated::invalid("e1".into());
    let v2: Validated<String, i32> = Validated::invalid("e2".into());
    let v3: Validated<String, i32> = Validated::valid(100);

    // 1. Applicative: Accumulates all errors instead of short-circuiting
    let result = Validated::<String, i32>::lift3(|a, b, c| a + b + c, &v1, &v2, &v3);
    assert_eq!(result.errors(), &["e1".to_string(), "e2".to_string()]);

    // 2. Collection & Sequence
    let list = vec![v1.clone(), v2.clone(), v3.clone()];
    let collected: Validated<String, Vec<i32>> = Validated::collect(list.into_iter());
    assert_eq!(collected.errors().len(), 2);

    // 3. Owned operations for efficiency
    let combined = v1.combine_errors_owned(v2);
    assert_eq!(
        combined.error_slice(),
        &["e1".to_string(), "e2".to_string()]
    );
}

// --- Interop, Unwrap and Recovery ---

#[test]
fn test_validated_recovery_and_interop() {
    let invalid: Validated<String, i32> =
        Validated::invalid_many(["e1".to_string(), "e2".to_string()]);

    // 1. Conversions (Result/Option)
    let res = invalid.clone().to_result();
    assert_eq!(res, Err("e1".to_string())); // First error only for Result
    assert_eq!(
        Validated::<String, i32>::from_result(&Ok::<i32, String>(42)),
        Validated::valid(42)
    );

    // 2. Recovery logic
    let recovered = invalid.clone().recover_with(0);
    assert_eq!(recovered.unwrap(), 0);

    let early_recovery = invalid.clone().recover_all(|e: String| {
        if e == "e2" {
            Validated::valid(99)
        } else {
            Validated::invalid(e.clone())
        }
    });
    assert_eq!(early_recovery.unwrap(), 99);

    // 3. Unsafe/Safe Unwrap
    assert_eq!(Validated::<&str, i32>::valid(10).unwrap_or(&0), 10);
    assert_eq!(invalid.into_option(), None);
}

// --- Real-world Complex Validation Scenario ---

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

    // Scenario 1: All errors collected
    let result = Validated::<String, User>::lift3(
        |n, a, e| User {
            name: n.clone(),
            age: *a,
            email: e.clone(),
        },
        &validate_name("A"),    // error 1
        &validate_age(10),      // error 2
        &validate_email("bad"), // error 3
    );

    assert_eq!(result.errors().len(), 3);
    assert!(result.errors().contains(&"Name too short".to_string()));

    // Scenario 2: Success path
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
    let valid: Validated<String, i32> = Validated::Valid(42);
    let json = serde_json::to_string(&valid).unwrap();
    let back: Validated<String, i32> = serde_json::from_str(&json).unwrap();
    assert_eq!(valid, back);
}
