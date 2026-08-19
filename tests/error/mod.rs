use rustica::datatypes::validated::Validated;
use rustica::error::convert::{
    collect_errors, core_to_composable, result_to_validated, split_validated_errors,
    validated_to_result,
};
use rustica::error::types::ComposableError;

struct NoClone(&'static str);

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

#[test]
fn owned_conversions_accept_non_clone_values() {
    let converted: Result<NoClone, NoClone> =
        validated_to_result(Validated::valid(NoClone("valid")));
    assert!(matches!(converted, Ok(NoClone("valid"))));

    assert!(matches!(
        result_to_validated::<NoClone, NoClone>(Ok(NoClone("result"))),
        Validated::Valid(NoClone("result"))
    ));

    let collected = collect_errors([NoClone("error")]);
    assert_eq!(collected.error_slice()[0].0, "error");

    let split = split_validated_errors(Validated::<NoClone, ()>::invalid(NoClone("split")));
    let mut split = split.into_iter();
    assert!(matches!(split.next(), Some(Err(NoClone("split")))));
    assert!(split.next().is_none());
}

#[test]
fn owned_validated_conversion_accepts_non_clone_values() {
    let converted = Validated::<NoClone, NoClone>::from_result_owned(Ok(NoClone("owned")));
    assert!(matches!(converted, Validated::Valid(NoClone("owned"))));
}

#[test]
fn sequence_with_error_accepts_non_clone_values() {
    let result: Result<Vec<NoClone>, NoClone> =
        rustica::error::sequence_with_error(vec![Validated::Valid(NoClone("value"))]);

    match result {
        Ok(values) => assert_eq!(values[0].0, "value"),
        Err(_) => panic!("expected success"),
    }
}
