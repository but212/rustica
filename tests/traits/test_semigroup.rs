extern crate quickcheck;
use quickcheck_macros::quickcheck;
use rustica::traits::semigroup::Semigroup;
use super::TestFunctor;

#[quickcheck]
fn semigroup_associativity(x: TestFunctor<String>, y: TestFunctor<String>, z: TestFunctor<String>) -> bool {
    x.combine(&y).combine(&z) == x.combine(&y.combine(&z))
}
