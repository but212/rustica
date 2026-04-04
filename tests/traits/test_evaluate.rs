use rustica::datatypes::wrapper::thunk::Thunk;
use rustica::traits::evaluate::{Evaluate, EvaluateExt};

#[test]
fn test_evaluate_creation_and_basic_idempotence() {
    // 1. Basic evaluation: should result in the value
    let computation: Thunk<_, i32> = Thunk::new(|| 42);
    assert_eq!(computation.evaluate(), 42);

    // 2. Reuse and Idempotence (Referential transparency)
    let first = computation.evaluate();
    let second = computation.evaluate();
    assert_eq!(first, second);
}

#[test]
fn test_evaluate_transformation_pipelines() {
    let t1: Thunk<_, i32> = Thunk::new(|| 10);

    // 1. Map: Evaluate then transform
    let res1: String = t1.fmap_evaluate(|x| x.to_string());
    assert_eq!(res1, "10");

    // 2. Bind: Transform then evaluate results
    let res2 = t1.bind_evaluate(|x| Thunk::new(move || x * 2));
    assert_eq!(res2, 20);

    // 3. Combine: Multiply then evaluate results
    let t2: Thunk<_, i32> = Thunk::new(|| 32);
    let sum = t1.combine_evaluate(&t2, |a, b| a + b);
    assert_eq!(sum, 42);
}

#[test]
fn test_evaluate_filtering_and_lifetimes() {
    let x = "hello".to_string();
    let t: Thunk<_, String> = Thunk::new(move || x.clone());

    // 1. Filter evaluation: Pass/Fail based on predicate
    assert_eq!(
        t.filter_evaluate(|s| s.len() > 3),
        Some("hello".to_string())
    );
    assert_eq!(t.filter_evaluate(|_| false), None);

    // 2. Owned evaluation (Consumes the thunk)
    assert_eq!(t.evaluate_owned(), "hello".to_string());
}
