use super::TestFunctor;
use quickcheck_macros::quickcheck;
use rustica::prelude::*;

#[quickcheck]
fn semigroup_associativity(x: TestFunctor<String>, y: TestFunctor<String>, z: TestFunctor<String>) -> bool {
    x.combine(&y).combine(&z) == x.combine(&y.combine(&z))
}
