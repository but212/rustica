use super::TestFunctor;
use quickcheck_macros::quickcheck;
use rustica::traits::foldable::{Foldable, FoldableExt};

// --- Generic Foldable laws ---

#[quickcheck]
fn foldable_properties(x: i32) -> bool {
    let f = TestFunctor::new(x);
    // 1. Fold consistency
    let left = f.fold_left(1i32, |acc: i32, &val: &i32| acc.saturating_mul(val));
    let right = f.fold_right(1i32, |&val: &i32, acc: i32| val.saturating_mul(acc));
    let mult_ok = left == right;

    // 2. Search and filter
    let found = f.find(|&val| val == x) == Some(x);
    let all_ok = f.all(|&val| val == x);
    let any_ok = f.any(|&val| val == x);
    let contains_ok = f.contains(&x);

    mult_ok && found && all_ok && any_ok && contains_ok
}
