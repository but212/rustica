//! Tests for transform_utils.rs utility functions

use rustica::datatypes::either::Either;
use rustica::datatypes::maybe::Maybe;
use rustica::utils::transform_utils::*;

#[test]
fn test_transform_all_basic() {
    let values: Vec<Maybe<i32>> = vec![
        Maybe::Just(1),
        Maybe::Just(2),
        Maybe::Nothing,
        Maybe::Just(4),
    ];
    let doubles = transform_all(&values, |&x| x * 2);
    assert_eq!(doubles[0], Maybe::Just(2));
    assert_eq!(doubles[1], Maybe::Just(4));
    assert_eq!(doubles[2], Maybe::Nothing);
    assert_eq!(doubles[3], Maybe::Just(8));
}

#[test]
fn test_transform_all_empty() {
    let values: Vec<Maybe<i32>> = vec![];
    let result = transform_all(&values, |&x| x * 2);
    assert!(result.is_empty());
}

#[test]
fn test_transform_chain_some_just() {
    let maybe_just: Option<Maybe<i32>> = Some(Maybe::Just(5));
    let result = transform_chain(maybe_just, |&x| x * 2);
    assert_eq!(result, Some(Maybe::Just(10)));
}

#[test]
fn test_transform_chain_some_nothing() {
    let maybe_nothing: Option<Maybe<i32>> = Some(Maybe::Nothing);
    let result = transform_chain(maybe_nothing, |&x| x * 2);
    assert_eq!(result, Some(Maybe::Nothing));
}

#[test]
fn test_transform_chain_none() {
    let none: Option<Maybe<i32>> = None;
    let result = transform_chain(none, |&x| x * 2);
    assert_eq!(result, None);
}

#[test]
fn test_pipeline_map_and_extract() {
    let pipeline = Pipeline::new(Some(5));
    let result = pipeline.map(|&x| x * 3).extract();
    assert_eq!(result, Some(15));
}

#[test]
fn test_pipeline_map_owned() {
    let pipeline = Pipeline::new(Some(7));
    let result = pipeline.map_owned(|x| x + 1).extract();
    assert_eq!(result, Some(8));
}

#[test]
fn test_pipeline_chain_multiple_maps() {
    let pipeline = Pipeline::new(Either::<&str, i32>::right(10))
        .map(|&x| x * 2)
        .map(|x| x.to_string());
    let result = pipeline.extract();
    assert_eq!(result, Either::right("20".to_string()));
}

#[test]
fn test_pipeline_left_value() {
    let pipeline = Pipeline::new(Either::<&str, i32>::left("error"));
    let result = pipeline.map(|&x| x * 2).extract();
    assert_eq!(result, Either::left("error"));
}

#[test]
fn test_pipeline_iterator_some() {
    let pipeline = Pipeline::new(Some(42));
    let collected: Vec<_> = pipeline.into_iter().collect();
    assert_eq!(collected, vec![42]);
}

#[test]
fn test_pipeline_iterator_vec() {
    let pipeline = Pipeline::new(vec![1, 2, 3]);
    let collected: Vec<_> = pipeline.into_iter().collect();
    assert_eq!(collected, vec![1, 2, 3]);
}

#[test]
fn test_pipeline_iterator_empty() {
    let pipeline = Pipeline::new(Vec::<i32>::new());
    let collected: Vec<_> = pipeline.into_iter().collect();
    assert!(collected.is_empty());
}
