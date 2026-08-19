use rustica::error::convert::core_to_composable;
use rustica::error::types::ComposableError;

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
    // Transformation to Composable
    let c1: ComposableError<&str> = "simple".into();
    let c2 = core_to_composable("func_call");
    assert_eq!(c1.core_error(), &"simple");
    assert_eq!(c2.core_error(), &"func_call");
}
