use super::TestFunctor;
use quickcheck_macros::quickcheck;
use rustica::traits::foldable::Foldable;

// --- Generic Foldable laws ---

#[quickcheck]
fn foldable_properties(x: i32) -> bool {
    let f = TestFunctor::new(x);
    // 1. Fold consistency
    let left = f.fold_left(1i32, |acc: i32, &val: &i32| acc.saturating_mul(val));
    let right = f.fold_right(1i32, |&val: &i32, acc: i32| val.saturating_mul(acc));
    left == right
}
