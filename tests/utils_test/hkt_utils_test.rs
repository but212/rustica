//! Tests for hkt_utils.rs utility functions

use rustica::utils::hkt_utils::*;

#[test]
fn test_filter_map_basic() {
    let numbers = vec![1, 2, 3, 4, 5, 6];
    let result: Vec<i32> = filter_map(numbers, |&n| n % 2 == 0, |n| n * n);
    assert_eq!(result, vec![4, 16, 36]);
}

#[test]
fn test_filter_map_empty() {
    let numbers: Vec<i32> = vec![];
    let result: Vec<i32> = filter_map(numbers, |&n| n > 0, |n| n * 2);
    assert_eq!(result, vec![]);
}

#[test]
fn test_filter_map_all_filtered() {
    let numbers = vec![1, 3, 5];
    let result: Vec<i32> = filter_map(numbers, |&n| n % 2 == 0, |n| n * 2);
    assert_eq!(result, vec![]);
}

#[test]
fn test_filter_map_identity() {
    let words = vec!["a", "b", "c"];
    let result: Vec<&str> = filter_map(words.clone(), |_| true, |s| s);
    assert_eq!(result, words);
}

#[test]
fn test_filter_map_predicate_false() {
    let nums = vec![1, 2, 3];
    let result = filter_map(nums, |_| false, |n| n);
    assert!(result.is_empty());
}

#[test]
fn test_filter_map_non_copy() {
    let objects = vec![String::from("a"), String::from("bb"), String::from("ccc")];
    let result = filter_map(
        objects,
        |s| s.len() > 1,
        |mut s| {
            s.push('!');
            s
        },
    );
    assert_eq!(result, vec!["bb!", "ccc!"]);
}
