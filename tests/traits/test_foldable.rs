//! Tests for the Foldable trait and its utility methods, using TestFunctor as the base structure.

use super::TestFunctor;
use quickcheck_macros::quickcheck;
use rustica::traits::foldable::{Foldable, FoldableExt};

#[test]
fn test_fold_left_singleton() {
    let f = TestFunctor(42, Default::default());
    let sum = f.fold_left(&0, |acc, x| acc + x);
    assert_eq!(sum, 42);
}

#[test]
fn test_fold_right_singleton() {
    let f = TestFunctor(42, Default::default());
    let sum = f.fold_right(&0, |x, acc| x + acc);
    assert_eq!(sum, 42);
}

#[quickcheck]
fn test_fold_left_identity(x: i32) {
    let f = TestFunctor(x, Default::default());
    let id = f.fold_left(&0, |acc, _| *acc);
    assert_eq!(id, 0);
}

#[test]
fn test_fold_right_identity() {
    let f = TestFunctor(100, Default::default());
    let id = f.fold_right(&0, |_, acc| *acc);
    assert_eq!(id, 0);
}

#[quickcheck]
fn test_fold_left_right_consistency(x: i32) {
    let f = TestFunctor(x, Default::default());
    let left = f.fold_left(&1, |acc, x| acc * x);
    let right = f.fold_right(&1, |x, acc| x * acc);
    assert_eq!(left, right);
}

#[quickcheck]
fn test_fold_left_with_default(x: i32) {
    let f = TestFunctor(x, Default::default());
    let result: i32 = f.fold_left(&Default::default(), |acc, x| acc + x);
    assert_eq!(result, x);
}

#[quickcheck]
fn test_find_some(x: i32) {
    let f = TestFunctor(x, Default::default());
    let found = f.find(|&val| val == x);
    assert_eq!(found, Some(x));
}

#[quickcheck]
fn test_find_none(x: i32) {
    let f = TestFunctor(x, Default::default());
    // Avoid integer overflow by using a different value that's not x+1
    let different_value = if x == i32::MAX { x - 1 } else { x + 1 };
    let found = f.find(|&val| val == different_value);
    assert_eq!(found, None);
}

#[quickcheck]
fn test_all_true(x: i32) {
    let f = TestFunctor(x, Default::default());
    assert!(f.all(|&val| val == x));
}

#[quickcheck]
fn test_all_false(x: i32) {
    let f = TestFunctor(x, Default::default());
    assert!(!f.all(|&val| val != x));
}

#[quickcheck]
fn test_any_true(x: i32) {
    let f = TestFunctor(x, Default::default());
    assert!(f.any(|&val| val == x));
}

#[quickcheck]
fn test_any_false(x: i32) {
    let f = TestFunctor(x, Default::default());
    assert!(!f.any(|&val| val != x));
}

#[quickcheck]
fn test_contains_true(x: i32) {
    let f = TestFunctor(x, Default::default());
    assert!(f.contains(&x));
}

#[quickcheck]
fn test_contains_false(x: i32) {
    let f = TestFunctor(x, Default::default());
    // Avoid integer overflow by using a different value that's not x+1
    let different_value = if x == i32::MAX { x - 1 } else { x + 1 };
    assert!(!f.contains(&different_value));
}
