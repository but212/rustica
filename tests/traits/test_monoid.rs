extern crate quickcheck;
use super::TestFunctor;
use quickcheck_macros::quickcheck;
use rustica::traits::monoid::Monoid;
use rustica::traits::semigroup::Semigroup;

#[quickcheck]
fn monoid_left_identity(x: TestFunctor<String>) -> bool {
    TestFunctor::empty().combine(&x) == x
}

#[quickcheck]
fn monoid_right_identity(x: TestFunctor<String>) -> bool {
    x.combine(&TestFunctor::empty()) == x
}
