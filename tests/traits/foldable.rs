use rustica::prelude::*;
use rustica::traits::foldable::Foldable;

#[test]
fn fold_map_combines_mapped_values() {
    let numbers = vec![1, 2, 3, 4];
    assert_eq!(numbers.fold_map(|n: &i32| Sum(*n)), Sum(10));
}

#[test]
fn fold_monoid_combines_existing_monoid_values() {
    let numbers = vec![Sum(1), Sum(2), Sum(3), Sum(4)];
    assert_eq!(numbers.fold_monoid::<Sum<i32>>(), Sum(10));
}

#[test]
fn fold_left_uses_initial_value_for_empty_variants() {
    let some_value: Option<i32> = Some(42);
    assert_eq!(some_value.fold_left(&0, |_, value| value * 2), 84);

    let none_value: Option<i32> = None;
    assert_eq!(none_value.fold_left(&100, |acc, _| *acc), 100);

    let ok_result: Result<i32, &str> = Ok(42);
    assert_eq!(ok_result.fold_left(&0, |_, value| value + 10), 52);

    let err_result: Result<i32, &str> = Err("error");
    assert_eq!(err_result.fold_left(&100, |acc, _| *acc), 100);
}
