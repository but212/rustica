use rustica::datatypes::maybe::{Maybe, MaybeError};

#[test]
fn test_maybe_with_error_trait() {
    // Test to_result on Just value
    let just = Maybe::Just(42);
    let result = just.to_result("No value present");
    assert_eq!(result, Ok(42));

    // Test to_result on Nothing value
    let nothing: Maybe<i32> = Maybe::Nothing;
    let result = nothing.to_result("No value present");
    assert_eq!(result, Err("No value present"));
}

#[test]
fn test_maybe_to_result_with_custom_error() {
    // Test Just value with custom error
    let just = Maybe::Just("success");
    let result = just.to_result("custom error");
    assert_eq!(result, Ok("success"));

    // Test Nothing value with custom error
    let nothing: Maybe<&str> = Maybe::Nothing;
    let result = nothing.to_result("custom error");
    assert_eq!(result, Err("custom error"));
}

#[test]
fn test_maybe_try_unwrap() {
    // Test try_unwrap on Just value
    let just = Maybe::Just(42);
    let result = just.try_unwrap();
    assert!(result.is_ok());
    assert_eq!(result.unwrap(), 42);

    // Test try_unwrap on Nothing value
    let nothing: Maybe<i32> = Maybe::Nothing;
    let result = nothing.try_unwrap();
    assert!(result.is_err());
    assert_eq!(
        result.clone().unwrap_err().core_error(),
        &"Cannot unwrap Nothing value"
    );
    assert_eq!(
        result.unwrap_err().context(),
        vec!["Called `try_unwrap()` on a `Nothing` value".to_string()]
    );
}

#[test]
fn test_maybe_result_conversions() {
    // Test converting Result to Maybe
    let ok_result: Result<i32, &str> = Ok(42);
    let err_result: Result<i32, &str> = Err("error");

    let maybe_from_ok: Maybe<i32> = ok_result.into();
    let maybe_from_err: Maybe<i32> = err_result.into();

    assert_eq!(maybe_from_ok, Maybe::Just(42));
    assert_eq!(maybe_from_err, Maybe::Nothing);

    // Test converting Maybe to Result
    let just = Maybe::Just(42);
    let nothing: Maybe<i32> = Maybe::Nothing;

    let result_from_just = just.to_standard_result();
    let result_from_nothing = nothing.to_standard_result();

    assert_eq!(result_from_just, Ok(42));
    assert_eq!(result_from_nothing, Err(MaybeError::ValueNotPresent));
}

#[test]
fn test_maybe_extension_trait() {
    // Test extension trait methods
    let just = Maybe::Just(42);
    let nothing: Maybe<i32> = Maybe::Nothing;

    // Test to_result with custom error
    assert_eq!(just.to_result("error"), Ok(42));
    assert_eq!(nothing.to_result("error"), Err("error"));

    // Test try_unwrap
    assert!(just.try_unwrap().is_ok());
    assert!(nothing.try_unwrap().is_err());
}

#[test]
fn test_convert_from_option() {
    // Test conversion from Option to Maybe
    let some = Some(42);
    let none: Option<i32> = None;

    let maybe_from_some = Maybe::from_option(some);
    let maybe_from_none = Maybe::from_option(none);

    assert_eq!(maybe_from_some, Maybe::Just(42));
    assert_eq!(maybe_from_none, Maybe::Nothing);

    // Test conversion from Maybe to Option
    let just = Maybe::Just(42);
    let nothing: Maybe<i32> = Maybe::Nothing;

    let option_from_just = just.to_option();
    let option_from_nothing = nothing.to_option();

    assert_eq!(option_from_just, Some(42));
    assert_eq!(option_from_nothing, None);
}
