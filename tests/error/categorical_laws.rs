use rustica::datatypes::either::Either;
use rustica::datatypes::validated::Validated;
use rustica::error::{ErrorCategory, ErrorOps};
use rustica::traits::functor::Functor;

#[test]
fn test_error_category_core_laws() {
    // 1. Identity Law (lift): Should wrap value into Success case
    let lift_res: Result<i32, String> = <Result<(), String> as ErrorCategory<String>>::lift(42);
    assert_eq!(lift_res, Ok(42));

    let lift_eith: Either<String, i32> = <Either<String, ()> as ErrorCategory<String>>::lift(42);
    assert_eq!(lift_eith, Either::Right(42));

    let lift_valid: Validated<String, i32> =
        <Validated<String, ()> as ErrorCategory<String>>::lift(42);
    assert_eq!(lift_valid, Validated::Valid(42));

    // 2. Error Handling Law (handle_error): Should wrap value into Error case
    let err = "fail".to_string();

    let hand_res: Result<i32, String> =
        <Result<(), String> as ErrorCategory<String>>::handle_error(err.clone());
    assert_eq!(hand_res, Err(err.clone()));

    let hand_eith: Either<String, i32> =
        <Either<String, ()> as ErrorCategory<String>>::handle_error(err.clone());
    assert_eq!(hand_eith, Either::Left(err.clone()));

    let hand_valid: Validated<String, i32> =
        <Validated<String, ()> as ErrorCategory<String>>::handle_error(err.clone());
    assert!(hand_valid.is_invalid());
    assert_eq!(hand_valid.errors()[0], err);
}

#[test]
fn test_error_functor_laws() {
    let f = |x: &i32| x + 10;
    let g = |x: &i32| x * 2;

    // Test Composition: fmap(f . g) == fmap(f) . fmap(g)
    let res: Result<i32, String> = Ok(5);
    assert_eq!(res.clone().fmap(|x| f(&g(x))), res.fmap(g).fmap(f));

    let eith: Either<String, i32> = Either::Right(5);
    assert_eq!(eith.clone().fmap(|x| f(&g(x))), eith.fmap(g).fmap(f));

    // Test Identity: fmap(id) == id
    let valid: Validated<String, i32> = Validated::Valid(42);
    assert_eq!(valid.clone().fmap(|x| *x), valid);
}

#[test]
fn test_error_operational_interop() {
    // 1. Recovery and Bimap Preservation
    let err: Result<i32, String> = Err("failed".into());
    assert_eq!(err.clone().recover(|_| Ok(100)), Ok(100));
    assert_eq!(Ok::<i32, String>(42).recover(|_| Ok(0)), Ok(42));

    let mapped = err.bimap_result(|x| x * 2, |e| format!("E:{}", e));
    assert_eq!(mapped, Err("E:failed".into()));

    // 2. Round-trip transformations
    use rustica::error::convert::{either_to_result, result_to_either};
    let orig: Result<i32, String> = Ok(42);
    assert_eq!(either_to_result(result_to_either(orig.clone())), orig);
}

#[test]
fn test_error_infrastructure_behavior() {
    use rustica::error::{ComposableError, error_pipeline};

    // 1. Deep Context Chain (Stack safety check)
    let mut error = ComposableError::new("root");
    for i in 0..100 {
        error = error.with_context(format!("L{}", i));
    }
    assert_eq!(error.context().len(), 100);
    assert_eq!(error.context()[0], "L99");

    // 2. Pipeline Ergonomics
    let res: Result<i32, &str> = Ok(10);
    let processed = error_pipeline(res)
        .map(|x| x * 2)
        .with_context("calc failed")
        .finish();
    assert_eq!(processed, Ok(20));

    let recovered = error_pipeline(Err("err"))
        .recover(|_| Ok(42))
        .map(|x| x * 2)
        .finish();
    assert_eq!(recovered, Ok(84));
}
