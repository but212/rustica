use quickcheck_macros::quickcheck;
use rustica::traits::monad::Monad;
use rustica::traits::pure::Pure;
use rustica::fntype::{FnType, FnTrait};

use super::TestFunctor;

// Monad Laws

#[quickcheck]
fn monad_left_identity(x: i32) -> bool {
    let f = FnType::new(|x: i32| TestFunctor::pure(x.saturating_add(1)));
    let left = TestFunctor::pure(x).bind(f.clone());
    let right = f.call(x);
    
    left == right
}

#[quickcheck]
fn monad_right_identity(x: i32) -> bool {
    let m = TestFunctor::pure(x);
    let pure_fn = FnType::new(TestFunctor::pure);
    let left = m.clone().bind(pure_fn);
    let right = m;
    
    left == right
}

#[quickcheck]
fn monad_associativity(x: i32) -> bool {
    let m = TestFunctor::pure(x);
    let f = FnType::new(|x: i32| TestFunctor::pure(x.saturating_add(1)));
    let g = FnType::new(|x: i32| TestFunctor::pure(x.saturating_mul(2)));
    
    let left = m.clone().bind(f.clone()).bind(g.clone());
    let right = m.bind(FnType::new(move |x| f.call(x).bind(g.clone())));
    
    left == right
}
