mod categorical_laws;
mod lazy_context;
mod context_tests;

use rustica::datatypes::either::Either;
use rustica::datatypes::validated::Validated;
use rustica::error::ErrorCategory;
use rustica::error::context::{error_pipeline, with_context};
use rustica::error::convert::{either_to_result, result_to_either};
use rustica::error::types::{ComposableError, ErrorContext};

#[test]
fn test_composable_error_creation() {
    let error = ComposableError::new("core error");
    assert_eq!(error.core_error(), &"core error");
    assert!(error.context().is_empty());
    assert_eq!(error.error_code(), None);
}

#[test]
fn test_composable_error_with_context() {
    let error = ComposableError::new("core error")
        .with_context("step 1 failed".to_string())
        .with_context("operation failed".to_string());

    assert_eq!(error.core_error(), &"core error");
    assert_eq!(error.context().len(), 2);
    assert_eq!(error.context()[0], "operation failed"); // Most recent first
    assert_eq!(error.context()[1], "step 1 failed");
}

#[test]
fn test_composable_error_with_code() {
    let error = ComposableError::with_code("not found", 404);
    assert_eq!(error.core_error(), &"not found");
    assert_eq!(error.error_code(), Some(404));
}

#[test]
fn test_error_context_creation() {
    let context = ErrorContext::new("test context");
    assert_eq!(context.message(), "test context");
}

#[test]
fn test_error_category_result() {
    let success: Result<i32, String> = <Result<(), String> as ErrorCategory<String>>::lift(42);
    assert_eq!(success, Ok(42));

    let error: Result<i32, String> =
        <Result<(), String> as ErrorCategory<String>>::handle_error("failed".to_string());
    assert_eq!(error, Err("failed".to_string()));
}

#[test]
fn test_error_category_either() {
    let success: Either<String, i32> = <Either<String, ()> as ErrorCategory<String>>::lift(42);
    assert_eq!(success, Either::Right(42));

    let error: Either<String, i32> =
        <Either<String, ()> as ErrorCategory<String>>::handle_error("failed".to_string());
    assert_eq!(error, Either::Left("failed".to_string()));
}

#[test]
fn test_error_category_validated() {
    let success: Validated<String, i32> =
        <Validated<String, ()> as ErrorCategory<String>>::lift(42);
    assert_eq!(success, Validated::Valid(42));

    let error: Validated<String, i32> =
        <Validated<String, ()> as ErrorCategory<String>>::handle_error("failed".to_string());
    assert!(error.is_invalid());
    assert_eq!(error.errors().len(), 1);
    assert_eq!(error.errors()[0], "failed");
}

#[test]
fn test_binary_hkt_either() {
    use rustica::traits::hkt::BinaryHKT;

    let either: Either<&str, i32> = Either::Right(42);
    let mapped = either.map_second(|e| format!("Error: {}", e));
    assert_eq!(mapped, Either::Right(42));

    let error_either: Either<&str, i32> = Either::Left("failed");
    let mapped_error = error_either.map_second(|e| format!("Error: {}", e));
    assert_eq!(mapped_error, Either::Left("Error: failed".to_string()));
}

#[test]
fn test_conversion_functions() {
    // Test either_to_result
    let either_success: Either<String, i32> = Either::Right(42);
    assert_eq!(either_to_result(either_success), Ok(42));

    let either_error: Either<String, i32> = Either::Left("error".to_string());
    assert_eq!(either_to_result(either_error), Err("error".to_string()));

    // Test result_to_either
    let result_success: Result<i32, String> = Ok(42);
    assert_eq!(result_to_either(result_success), Either::Right(42));

    let result_error: Result<i32, String> = Err("error".to_string());
    assert_eq!(
        result_to_either(result_error),
        Either::Left("error".to_string())
    );
}

#[test]
fn test_with_context_function() {
    let error = "core error";
    let contextual = with_context(error, "operation failed");

    assert_eq!(contextual.core_error(), &"core error");
    assert_eq!(contextual.context().len(), 1);
    assert_eq!(contextual.context()[0], "operation failed");
}

#[test]
fn test_error_pipeline() {
    let result: Result<i32, &str> = Err("parse error");

    let processed = error_pipeline(result)
        .with_context("Failed to process input")
        .recover(|_| Ok(42))
        .finish();

    assert_eq!(processed, Ok(42));
}

#[test]
fn test_error_chain_formatting() {
    let error = ComposableError::new("file not found")
        .with_context("failed to load config".to_string())
        .with_context("application startup failed".to_string());

    let chain = error.error_chain();
    assert!(chain.contains("application startup failed"));
    assert!(chain.contains("failed to load config"));
    assert!(chain.contains("file not found"));
}

#[test]
fn test_from_trait_conversion() {
    // Test From<E> for ComposableError<E>
    let simple_error = "file not found";
    let composable: ComposableError<&str> = simple_error.into();

    assert_eq!(composable.core_error(), &"file not found");
    assert!(composable.context().is_empty());

    // Test with different error types
    let num_error = 404;
    let composable_num: ComposableError<i32> = num_error.into();
    assert_eq!(composable_num.core_error(), &404);
}

#[test]
fn test_core_to_composable_uses_from() {
    use rustica::error::convert::core_to_composable;

    // core_to_composable should use From trait internally
    let error = "test error";
    let composable = core_to_composable(error);

    assert_eq!(composable.core_error(), &"test error");
    assert!(composable.context().is_empty());
}

#[test]
fn test_error_pipeline_finish_unboxed() {
    use rustica::error::types::ComposableResult;

    // Test finish_unboxed returns unboxed ComposableError
    let result: Result<i32, i32> = Err(404);
    let final_result: ComposableResult<i32, i32> = error_pipeline(result)
        .with_context("Request failed")
        .with_context("Server error")
        .finish_without_box();

    match final_result {
        Ok(_) => panic!("Expected error"),
        Err(composable) => {
            assert_eq!(composable.core_error(), &404);
            assert_eq!(composable.context().len(), 2);
            assert_eq!(composable.context()[0], "Server error");
            assert_eq!(composable.context()[1], "Request failed");
        },
    }
}

#[test]
fn test_error_pipeline_finish_vs_finish_unboxed() {
    use rustica::error::types::{BoxedComposableResult, ComposableResult};

    let result1: Result<i32, &str> = Err("error");
    let result2: Result<i32, &str> = Err("error");

    // finish() returns BoxedComposableResult
    let boxed: BoxedComposableResult<i32, &str> =
        error_pipeline(result1).with_context("context").finish();

    // finish_unboxed() returns ComposableResult
    let unboxed: ComposableResult<i32, &str> = error_pipeline(result2)
        .with_context("context")
        .finish_without_box();

    // Both should have the same error and context
    match (boxed, unboxed) {
        (Err(boxed_err), Err(unboxed_err)) => {
            assert_eq!(boxed_err.core_error(), unboxed_err.core_error());
            assert_eq!(boxed_err.context(), unboxed_err.context());
        },
        _ => panic!("Both should be errors"),
    }
}

#[test]
fn test_validated_error_ops_lossy_conversion() {
    use rustica::error::ErrorOps;

    // Test that Validated recover uses only first error
    let validated: Validated<String, i32> = Validated::invalid_many(vec![
        "error1".to_string(),
        "error2".to_string(),
        "error3".to_string(),
    ]);

    let recovered = validated.recover(|first_err| {
        assert_eq!(first_err, "error1"); // Should receive only first error
        Validated::Valid(42)
    });

    assert_eq!(recovered, Validated::Valid(42));
}

#[test]
fn test_validated_bimap_result_lossy_conversion() {
    use rustica::error::ErrorOps;

    // Test that Validated bimap_result uses only first error
    let validated: Validated<i32, String> = Validated::invalid_many(vec![404, 500, 503]);

    let result: Result<usize, String> =
        validated.bimap_result(|s| s.len(), |code| format!("HTTP Error: {}", code));

    // Should only use the first error (404)
    assert_eq!(result, Err("HTTP Error: 404".to_string()));
}
