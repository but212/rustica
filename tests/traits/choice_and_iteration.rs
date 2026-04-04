use super::TestFunctor;
use quickcheck_macros::quickcheck;
use rustica::traits::alternative::Alternative;
use rustica::traits::foldable::{Foldable, FoldableExt};
use rustica::traits::monad_plus::MonadPlus;

// --- Choice Mechanisms (Alternative & MonadPlus) ---

#[test]
fn test_alternative_choice_logic() {
    // 1. Option: Should pick the first Some
    let a: Option<i32> = None;
    let b = Some(42);
    assert_eq!(Alternative::alt(&a, &b), b);
    assert_eq!(Option::<i32>::guard(true), Some(()));
    assert_eq!(Option::<i32>::guard(false), None);

    // 2. Vector: Should pick the first non-empty or empty if both empty
    let v1: Vec<i32> = vec![1];
    let v2: Vec<i32> = vec![2];
    assert_eq!(Vec::<i32>::empty_alt().alt(&v1), v1);
    assert_eq!(v1.alt(&v2), v1); // Choice picks first non-empty
}

#[test]
fn test_monad_plus_identity_and_binding() {
    use rustica::traits::monad::Monad;
    let some = Some(42);
    let none: Option<i32> = Option::<i32>::mzero();

    // Identity and Zero binding
    assert_eq!(none.mplus(&some), some);
    assert_eq!(none.bind(|x| Some(x + 1)), none);
}

// --- Iteration and Search (Foldable) ---

#[quickcheck]
fn foldable_properties(x: i32) -> bool {
    let f = TestFunctor::new(x);
    // 1. Fold consistency
    let left = f.fold_left(&1i32, |acc: &i32, &val: &i32| acc.saturating_mul(val));
    let right = f.fold_right(&1i32, |&val: &i32, acc: &i32| val.saturating_mul(*acc));
    let mult_ok = left == right;

    // 2. Search and filter
    let found = f.find(|&val| val == x) == Some(x);
    let all_ok = f.all(|&val| val == x);
    let any_ok = f.any(|&val| val == x);
    let contains_ok = f.contains(&x);

    mult_ok && found && all_ok && any_ok && contains_ok
}

#[test]
fn test_fold_integration() {
    let numbers = vec![1, 2, 3, 4];
    // Custom logic to find first mapped Some (MonadPlus + iteration context)
    let found = numbers
        .into_iter()
        .map(|x| if x > 2 { Some(x * 10) } else { None })
        .find(|opt| opt.is_some())
        .flatten();
    assert_eq!(found, Some(30));
}
