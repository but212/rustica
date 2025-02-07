use quickcheck_macros::quickcheck;
use rustica::category::functor::Functor;
use rustica::category::pure::Pure;
use rustica::fntype::SendSyncFn;

use super::TestFunctor;

#[quickcheck]
fn functor_identity_law(x: i32) -> bool {
    let functor = TestFunctor::pure(x);
    let f = SendSyncFn::new(|x| x);
    functor.clone().map(f) == functor
}

#[quickcheck]
fn functor_composition_law(x: i32) -> bool {
    let functor = TestFunctor::pure(x);
    let f = SendSyncFn::new(|x: i32| x.saturating_add(1));
    let g = SendSyncFn::new(|x: i32| x.saturating_mul(2));
    
    let left = functor.clone().map(f.clone()).map(g.clone());
    let right = functor.map(SendSyncFn::new(move |x| g.call(f.call(x))));
    left == right
}
