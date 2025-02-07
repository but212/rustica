use quickcheck_macros::quickcheck;
use rustica::category::monad::Monad;
use rustica::category::pure::Pure;
use rustica::fntype::SendSyncFn;

use super::TestFunctor;

// Monad Laws

#[quickcheck]
fn monad_left_identity(x: i32) -> bool {
    let f = SendSyncFn::new(|x: i32| TestFunctor::pure(x.saturating_add(1)));
    let left = TestFunctor::pure(x).bind(f.clone());
    let right = f.call(x);
    
    left == right
}

#[quickcheck]
fn monad_right_identity(x: i32) -> bool {
    let m = TestFunctor::pure(x);
    let pure_fn = SendSyncFn::new(TestFunctor::pure);
    let left = m.clone().bind(pure_fn);
    let right = m;
    
    left == right
}

#[quickcheck]
fn monad_associativity(x: i32) -> bool {
    let m = TestFunctor::pure(x);
    let f = SendSyncFn::new(|x: i32| TestFunctor::pure(x.saturating_add(1)));
    let g = SendSyncFn::new(|x: i32| TestFunctor::pure(x.saturating_mul(2)));
    
    let left = m.clone().bind(f.clone()).bind(g.clone());
    let right = m.bind(SendSyncFn::new(move |x| f.call(x).bind(g.clone())));
    
    left == right
}
