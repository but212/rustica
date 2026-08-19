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

    // 2. Idiomatic Rust closure chaining
    let add_one = |x: i32| x + 1;
    let double = |x: i32| x * 2;
    assert_eq!(double(add_one(5)), 12);
}

#[test]
fn test_categorical_mapping() {
    // Test standardized mapping for std types
    assert_eq!(Some(10).map(|x| x / 2), Some(5));
    let ok_res: Result<i32, &str> = Ok(10);
    assert_eq!(ok_res.map(|x| x + 1).map_err(|e| e.len()), Ok(11));
    let err_res: Result<i32, &str> = Err("err");
    assert_eq!(
        err_res.map(|x| x + 1).map_err(|e| e.to_uppercase()),
        Err("ERR".to_string())
    );
}
