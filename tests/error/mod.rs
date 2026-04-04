mod categorical_laws;
mod context_tests;
mod lazy_context;

use rustica::datatypes::either::Either;
use rustica::error::context::error_pipeline;
use rustica::error::convert::{core_to_composable, either_to_result, result_to_either};
use rustica::error::types::{BoxedComposableResult, ComposableError, ComposableResult};

#[test]
fn test_composable_error_anatomy() {
    // 1. Creation and basic properties
    let e = ComposableError::with_code("io_error", 500)
        .with_context("layer 1".to_string())
        .with_context("layer 2".to_string());

    assert_eq!(e.core_error(), &"io_error");
    assert_eq!(e.error_code(), Some(500));
    assert_eq!(e.context().len(), 2);
    assert_eq!(e.context()[0], "layer 2"); // Most recent first

    // 2. Formatting and chain display
    let chain = e.error_chain();
    assert!(chain.contains("io_error") && chain.contains("layer 1") && chain.contains("layer 2"));
}

#[test]
fn test_error_type_conversions() {
    // 1. Either/Result mapping and HKT
    use rustica::traits::hkt::BinaryHKT;
    let eith: Either<&str, i32> = Either::Left("err");
    assert_eq!(
        eith.map_second(|e| format!("E:{}", e)),
        Either::Left("E:err".into())
    );

    // 2. Cross-type conversions
    let success: Either<String, i32> = Either::Right(42);
    assert_eq!(either_to_result(success), Ok(42));
    assert_eq!(result_to_either(Ok::<i32, String>(42)), Either::Right(42));

    // 3. Transformation to Composable
    let c1: ComposableError<&str> = "simple".into();
    let c2 = core_to_composable("func_call");
    assert_eq!(c1.core_error(), &"simple");
    assert_eq!(c2.core_error(), &"func_call");
}

#[test]
fn test_error_pipeline_ergonomics() {
    let input: Result<i32, i32> = Err(404);

    // 1. Boxed Finish (Common usage)
    let boxed: BoxedComposableResult<i32, i32> =
        error_pipeline(input).with_context("ctx1").finish();

    // 2. Unboxed Finish (Zero-allocation or specific return handling)
    let unboxed: ComposableResult<i32, i32> = error_pipeline(input)
        .with_context("ctx1")
        .finish_without_box();

    match (boxed, unboxed) {
        (Err(b), Err(u)) => {
            assert_eq!(b.core_error(), u.core_error());
            assert_eq!(b.context(), u.context());
        },
        _ => panic!("Expected errors"),
    }
}
