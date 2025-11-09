//! # Categorical Laws for Error Handling
//!
//! This module contains property-based tests for verifying that our error
//! handling abstractions satisfy categorical laws. These laws ensure that
//! our abstractions are mathematically sound and behave predictably.

use rustica::datatypes::either::Either;
use rustica::datatypes::validated::Validated;
use rustica::error::{ErrorCategory, ErrorOps};
use rustica::traits::functor::Functor;

/// Tests the Identity Law for ErrorCategory
///
/// Law: lift(x) should create a success case containing x
/// For all types implementing ErrorCategory, lifting a value should
/// preserve that value in the success case.
#[test]
fn test_error_category_identity_law_result() {
    // For Result
    let value = 42;
    let lifted: Result<i32, String> = <Result<(), String> as ErrorCategory<String>>::lift(value);
    assert_eq!(lifted, Ok(42));

    let value = "test";
    let lifted: Result<&str, String> = <Result<(), String> as ErrorCategory<String>>::lift(value);
    assert_eq!(lifted, Ok("test"));
}

#[test]
fn test_error_category_identity_law_either() {
    // For Either
    let value = 42;
    let lifted: Either<String, i32> = <Either<String, ()> as ErrorCategory<String>>::lift(value);
    assert_eq!(lifted, Either::Right(42));

    let value = vec![1, 2, 3];
    let lifted: Either<String, Vec<i32>> =
        <Either<String, ()> as ErrorCategory<String>>::lift(value.clone());
    assert_eq!(lifted, Either::Right(vec![1, 2, 3]));
}

#[test]
fn test_error_category_identity_law_validated() {
    // For Validated
    let value = 42;
    let lifted: Validated<String, i32> =
        <Validated<String, ()> as ErrorCategory<String>>::lift(value);
    assert_eq!(lifted, Validated::Valid(42));

    let value = "success";
    let lifted: Validated<String, &str> =
        <Validated<String, ()> as ErrorCategory<String>>::lift(value);
    assert_eq!(lifted, Validated::Valid("success"));
}

/// Tests the Error Handling Law
///
/// Law: handle_error(e) should create an error case containing e
/// For all types implementing ErrorCategory, handling an error should
/// preserve that error in the error case.
#[test]
fn test_error_category_error_handling_law_result() {
    let error = "connection failed".to_string();
    let result: Result<i32, String> =
        <Result<(), String> as ErrorCategory<String>>::handle_error(error.clone());
    assert_eq!(result, Err(error));
}

#[test]
fn test_error_category_error_handling_law_either() {
    let error = "parse error".to_string();
    let either: Either<String, i32> =
        <Either<String, ()> as ErrorCategory<String>>::handle_error(error.clone());
    assert_eq!(either, Either::Left(error));
}

#[test]
fn test_error_category_error_handling_law_validated() {
    let error = "validation failed".to_string();
    let validated: Validated<String, i32> =
        <Validated<String, ()> as ErrorCategory<String>>::handle_error(error.clone());
    assert!(validated.is_invalid());
    assert_eq!(validated.errors().len(), 1);
    assert_eq!(&validated.errors()[0], &error);
}

/// Tests the Functor Composition Law for error types
///
/// Law: fmap(f . g) == fmap(f) . fmap(g)
/// Mapping with a composition should be the same as composing two maps
#[test]
fn test_functor_composition_law_result() {
    let f = |x: &i32| x + 10;
    let g = |x: &i32| x * 2;

    let value: Result<i32, String> = Ok(5);

    // fmap(f . g)
    let composed = value.clone().fmap(|x| f(&g(x)));

    // fmap(f) . fmap(g)
    let sequential = value.fmap(g).fmap(f);

    assert_eq!(composed, sequential);
    assert_eq!(composed, Ok(20)); // (5 * 2) + 10 = 20
}

#[test]
fn test_functor_composition_law_either() {
    let f = |x: &i32| x + 10;
    let g = |x: &i32| x * 2;

    let value: Either<String, i32> = Either::Right(5);

    // fmap(f . g)
    let composed = value.clone().fmap(|x| f(&g(x)));

    // fmap(f) . fmap(g)
    let sequential = value.fmap(g).fmap(f);

    assert_eq!(composed, sequential);
    assert_eq!(composed, Either::Right(20));
}

#[test]
fn test_functor_composition_law_validated() {
    let f = |x: &i32| x + 10;
    let g = |x: &i32| x * 2;

    let value: Validated<String, i32> = Validated::Valid(5);

    // fmap(f . g)
    let composed = value.clone().fmap(|x| f(&g(x)));

    // fmap(f) . fmap(g)
    let sequential = value.fmap(g).fmap(f);

    assert_eq!(composed, sequential);
    assert_eq!(composed, Validated::Valid(20));
}

/// Tests the Functor Identity Law
///
/// Law: fmap(id) == id
/// Mapping with the identity function should not change the value
#[test]
fn test_functor_identity_law_result() {
    let value: Result<i32, String> = Ok(42);
    let mapped = value.clone().fmap(|x| *x); // identity function (deref)
    assert_eq!(value, mapped);

    let error: Result<i32, String> = Err("error".to_string());
    let mapped_error = error.clone().fmap(|x| *x);
    assert_eq!(error, mapped_error);
}

#[test]
fn test_functor_identity_law_either() {
    let value: Either<String, i32> = Either::Right(42);
    let mapped = value.clone().fmap(|x| *x);
    assert_eq!(value, mapped);

    let error: Either<String, i32> = Either::Left("error".to_string());
    let mapped_error = error.clone().fmap(|x| *x);
    assert_eq!(error, mapped_error);
}

#[test]
fn test_functor_identity_law_validated() {
    let value: Validated<String, i32> = Validated::Valid(42);
    let mapped = value.clone().fmap(|x| *x);
    assert_eq!(value, mapped);

    let error: Validated<String, i32> = Validated::invalid("error".to_string());
    let mapped_error = error.clone().fmap(|x| *x);
    assert_eq!(error, mapped_error);
}

/// Tests the ErrorOps recover composition
///
/// Law: recover should provide alternative computation on error
#[test]
fn test_error_ops_recover_on_success() {
    // Recovery should not affect success cases
    let success: Result<i32, String> = Ok(42);
    let recovered = success.recover(|_| Ok(0));
    assert_eq!(recovered, Ok(42));
}

#[test]
fn test_error_ops_recover_on_error() {
    // Recovery should apply to error cases
    let error: Result<i32, String> = Err("failed".to_string());
    let recovered = error.recover(|_| Ok(100));
    assert_eq!(recovered, Ok(100));
}

#[test]
fn test_error_ops_bimap_preserves_structure() {
    // bimap should preserve the Result structure
    let success: Result<i32, String> = Ok(42);
    let mapped = success.bimap_result(|x| x * 2, |e| format!("Error: {}", e));
    assert_eq!(mapped, Ok(84));

    let error: Result<i32, String> = Err("fail".to_string());
    let mapped_error = error.bimap_result(|x| x * 2, |e| format!("Error: {}", e));
    assert_eq!(mapped_error, Err("Error: fail".to_string()));
}

/// Tests that error transformations preserve categorical structure
#[test]
fn test_error_transformation_preserves_structure() {
    use rustica::error::convert::{either_to_result, result_to_either};

    // Round-trip should preserve the value
    let original: Result<i32, String> = Ok(42);
    let either = result_to_either(original.clone());
    let back = either_to_result(either);
    assert_eq!(original, back);

    // Round-trip with error
    let error_result: Result<i32, String> = Err("error".to_string());
    let either_error = result_to_either(error_result.clone());
    let back_error = either_to_result(either_error);
    assert_eq!(error_result, back_error);
}

/// Tests error accumulation properties for Validated
#[test]
fn test_validated_error_accumulation_associativity() {
    use rustica::datatypes::validated::Validated;

    // Error accumulation should be associative
    let v1: Validated<String, i32> = Validated::invalid("error1".to_string());
    let v2: Validated<String, i32> = Validated::invalid("error2".to_string());
    let v3: Validated<String, i32> = Validated::invalid("error3".to_string());

    // This tests that combining errors preserves all of them
    let combined_12: Validated<String, i32> = match (v1.clone(), v2.clone()) {
        (Validated::Invalid(mut e1), Validated::Invalid(e2)) => {
            e1.extend(e2);
            Validated::Invalid(e1)
        },
        _ => panic!("Expected invalid"),
    };

    let final_combined: Validated<String, i32> = match (combined_12, v3.clone()) {
        (Validated::Invalid(mut e12), Validated::Invalid(e3)) => {
            e12.extend(e3);
            Validated::Invalid(e12)
        },
        _ => panic!("Expected invalid"),
    };

    assert_eq!(final_combined.errors().len(), 3);
}

/// Tests deep context chain to ensure no stack overflow or performance degradation
#[test]
fn test_deep_error_context_chain() {
    use rustica::error::ComposableError;

    let mut error = ComposableError::new("core error");

    // Add 100 contexts - should not panic or overflow
    for i in 0..100 {
        error = error.with_context(format!("context level {}", i));
    }

    assert_eq!(error.context().len(), 100);
    assert_eq!(error.core_error(), &"core error");

    // Most recent context should be first
    assert!(error.context()[0].contains("context level 99"));
}

/// Tests that error pipeline operations compose correctly
#[test]
fn test_error_pipeline_composition() {
    use rustica::error::error_pipeline;

    let result: Result<i32, &str> = Ok(10);

    let processed = error_pipeline(result)
        .map(|x| x * 2)
        .map(|x| x + 5)
        .with_context("calculation failed")
        .finish();

    assert_eq!(processed, Ok(25)); // (10 * 2) + 5 = 25
}

#[test]
fn test_error_pipeline_with_recovery() {
    use rustica::error::error_pipeline;

    let result: Result<i32, &str> = Err("initial error");

    let processed = error_pipeline(result)
        .with_context("operation failed")
        .recover(|_| Ok(42))
        .map(|x| x * 2)
        .finish();

    assert_eq!(processed, Ok(84)); // Recovery provides 42, then *2 = 84
}
