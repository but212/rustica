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

#[test]
fn sequence_preserves_order_and_returns_first_error() {
    assert_eq!(
        Vec::<Result<i32, &str>>::new()
            .into_iter()
            .collect::<Result<Vec<_>, _>>(),
        Ok(Vec::<i32>::new())
    );
    assert_eq!(
        vec![Ok(1), Ok(2), Ok(3)]
            .into_iter()
            .collect::<Result<Vec<_>, &str>>(),
        Ok(vec![1, 2, 3])
    );
    assert_eq!(
        vec![Ok(1), Err("first"), Err("second")]
            .into_iter()
            .collect::<Result<Vec<_>, _>>(),
        Err("first")
    );
}

#[test]
fn traverse_preserves_order_and_stops_after_first_error() {
    let mut seen = Vec::new();
    let result: Result<Vec<_>, _> = [1, 2, 3]
        .into_iter()
        .map(|value| {
            seen.push(value);
            if value == 2 {
                Err("stop")
            } else {
                Ok(value * 10)
            }
        })
        .collect();

    assert_eq!(result, Err("stop"));
    assert_eq!(seen, vec![1, 2]);
    assert_eq!(
        [1, 2, 3]
            .into_iter()
            .map(|value| Ok::<_, &str>(value * 10))
            .collect::<Result<Vec<_>, _>>(),
        Ok(vec![10, 20, 30])
    );
}

#[test]
fn pipeline_result_handles_empty_input_and_short_circuits() {
    assert_eq!(
        pipeline_result::<_, i32, &'static str, fn(i32) -> Result<i32, &'static str>>(
            7,
            Vec::new(),
        ),
        Ok(7)
    );

    fn add_one(value: i32) -> Result<i32, &'static str> {
        Ok(value + 1)
    }
    fn stop(_: i32) -> Result<i32, &'static str> {
        Err("stop")
    }
    fn should_not_run(_: i32) -> Result<i32, &'static str> {
        panic!("pipeline continued after an error")
    }

    assert_eq!(pipeline_result(1, vec![add_one, add_one]), Ok(3));
    assert_eq!(
        pipeline_result(1, vec![add_one, stop, should_not_run]),
        Err("stop")
    );
}

#[test]
fn sequence_with_error_preserves_order_and_returns_first_error() {
    let values: Vec<Result<i32, &str>> = vec![Ok(1), Ok(2)];
    assert_eq!(sequence_with_error(values), Ok(vec![1, 2]));

    let values = vec![Ok(1), Err("first"), Err("second")];
    let result: Result<Vec<i32>, &str> = sequence_with_error(values);
    assert_eq!(result, Err("first"));

    let values: Vec<Result<i32, &str>> = Vec::new();
    assert_eq!(sequence_with_error(values), Ok(Vec::<i32>::new()));

    // Test with Validated as well
    let val_ok: Vec<Validated<&str, i32>> = vec![Validated::valid(1), Validated::valid(2)];
    assert_eq!(sequence_with_error(val_ok), Ok(vec![1, 2]));

    let val_err: Vec<Validated<&str, i32>> = vec![
        Validated::valid(1),
        Validated::invalid("first"),
        Validated::invalid("second"),
    ];
    let val_res: Result<Vec<i32>, &str> = sequence_with_error(val_err);
    assert_eq!(val_res, Err("first"));
}

use rustica::datatypes::validated::Validated;
use rustica::error::sequence_with_error;
use rustica::utils::hkt_utils::pipeline_result;
