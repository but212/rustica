use rustica::datatypes::maybe::{Maybe, MaybeError};

#[test]
fn test_maybe_conversion_scenarios() {
    // 1. Result <-> Maybe (Standard conversions)
    let ok: Result<i32, &str> = Ok(42);
    let err: Result<i32, &str> = Err("err");

    assert_eq!(Maybe::<i32>::from(ok), Maybe::Just(42));
    assert_eq!(Maybe::<i32>::from(err), Maybe::Nothing);
    assert_eq!(Maybe::Just(42).to_standard_result(), Ok(42));
    assert_eq!(
        Maybe::<i32>::Nothing.to_standard_result(),
        Err(MaybeError::ValueNotPresent)
    );

    // 2. Option <-> Maybe
    assert_eq!(Maybe::from_option(Some(42)), Maybe::Just(42));
    assert_eq!(Maybe::Just(42).to_option(), Some(42));
}

#[test]
fn test_maybe_error_handling_ergonomics() {
    let just = Maybe::Just(42);
    let nothing: Maybe<i32> = Maybe::Nothing;

    // Custom error mapping
    assert_eq!(just.to_result("error"), Ok(42));
    assert_eq!(nothing.to_result("error"), Err("error"));

    // try_unwrap with detailed context
    let res = nothing.try_unwrap();
    assert!(res.is_err());
    let err = res.unwrap_err();
    assert_eq!(err.core_error(), &"Cannot unwrap Nothing value");
}
