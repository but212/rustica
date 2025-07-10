//! Tests for the composable trait and composition utilities.

use quickcheck::{TestResult, quickcheck};
use rustica::traits::composable::*;

#[test]
fn test_basic_compose() {
    fn property(x: i32) -> TestResult {
        // Discard values that would cause integer overflow
        if !(i32::MIN / 2..=i32::MAX / 2).contains(&x) {
            return TestResult::discard();
        }

        let add_one = |x: i32| x + 1;
        let double = |x: i32| x * 2;
        let composed = compose(add_one, double);

        TestResult::from_bool(composed(x) == (x + 1) * 2)
    }
    quickcheck(property as fn(i32) -> TestResult);
}

#[test]
fn test_compose_all() {
    fn property(x: i32) -> TestResult {
        // Discard values that would cause integer overflow
        if !(i32::MIN / 2..=i32::MAX / 2).contains(&x) {
            return TestResult::discard();
        }

        let add_one = |x: i32| x + 1;
        let double = |x: i32| x * 2;
        let composed = compose_all(vec![add_one, double, add_one]);

        // Check with safe calculation that handles potential overflow
        let result = match x.checked_add(1) {
            Some(v1) => match v1.checked_mul(2) {
                Some(v2) => v2.checked_add(1),
                None => None,
            },
            None => None,
        };

        match result {
            Some(expected) => TestResult::from_bool(composed(x) == expected),
            None => TestResult::discard(), // Discard if calculation would overflow
        }
    }
    quickcheck(property as fn(i32) -> TestResult);
}

#[test]
fn test_compose_option() {
    fn property(x: i32) -> TestResult {
        if x <= 0 || x > 1000 {
            return TestResult::discard();
        }

        let s = x.to_string();
        let parse_as_int = |s: &str| s.parse::<i32>().ok();
        let double_if_positive = |n: i32| if n > 0 { Some(n * 2) } else { None };
        let composed = compose_option(parse_as_int, double_if_positive);

        TestResult::from_bool(composed(&s) == Some(x * 2))
    }
    quickcheck(property as fn(i32) -> TestResult);
}

#[test]
fn test_compose_fallible() {
    fn property(x: i32) -> TestResult {
        if x <= 0 || x > 1000 {
            return TestResult::discard();
        }

        let s = x.to_string();
        let parse_string = |s: &str| s.parse::<i32>().map_err(|_| "Parse error");
        let double_if_positive = |n: i32| {
            if n > 0 {
                Ok(n * 2)
            } else {
                Err("Number was not positive")
            }
        };
        let composed = compose_fallible(parse_string, double_if_positive);

        TestResult::from_bool(composed(&s) == Ok(x * 2))
    }
    quickcheck(property as fn(i32) -> TestResult);
}
