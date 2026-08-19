use rustica::datatypes::either::Either;
use rustica::utils::categorical_utils::*;
use rustica::utils::transform_utils::*;

#[test]
fn test_functional_transform_utilities() {
    // 1. Standard iterator filtering and sequencing
    let numbers = vec![1, 2, 3, 4];
    let filtered: Vec<_> = numbers
        .into_iter()
        .filter(|n| n % 2 == 0)
        .map(|n| n * n)
        .collect();
    assert_eq!(filtered, vec![4, 16]);

    let options = vec![Some(1), Some(2)];
    assert_eq!(
        options.into_iter().collect::<Option<Vec<_>>>(),
        Some(vec![1, 2])
    );
    assert_eq!(
        vec![Some(1), None].into_iter().collect::<Option<Vec<_>>>(),
        None
    );

    // 2. Composed utilities (compose, pipe, flip)
    let add_one = |x: i32| x + 1;
    let double = |x: i32| x * 2;
    assert_eq!(compose(double, add_one)(5), 12);
    assert_eq!(pipe(add_one, double)(5), 12);
    assert_eq!(flip(|x: i32, y: i32| x - y)(10, 3), -7);
}

#[test]
fn test_pipeline_ergonomics() {
    // 1. Complex Pipeline with Either
    let res = Pipeline::new(Either::<&str, i32>::right(10))
        .map(|&x| x * 2)
        .map(|x| x.to_string())
        .extract();
    assert_eq!(res, Either::right("20".to_string()));

    // 2. Iterator interface
    let pipeline = Pipeline::new(vec![1, 2, 3]);
    let collected: Vec<_> = pipeline.into_iter().map(|x| x + 1).collect();
    assert_eq!(collected, vec![2, 3, 4]);
}

#[test]
fn test_categorical_mapping() {
    // Test standardized mapping for std types
    assert_eq!(Some(10).map(|x| x / 2), Some(5));
    assert_eq!(bimap_result(Ok(10), |x| x + 1, |e: &str| e.len()), Ok(11));
    assert_eq!(
        bimap_result(Err("err"), |x: i32| x, |e| e.to_uppercase()),
        Err("ERR".into())
    );
}
