use quickcheck_macros::quickcheck;
use rustica::category::functor::Functor;
use rustica::category::pure::Pure;
use rustica::fntype::{FnType, FnTrait};

use super::TestFunctor;

#[quickcheck]
fn functor_identity_law(x: i32) -> bool {
    let functor = TestFunctor::pure(x);
    let f = FnType::new(|x| x);
    functor.clone().fmap(f) == functor
}

#[quickcheck]
fn functor_composition_law(x: i32) -> bool {
    let functor = TestFunctor::pure(x);
    let f = FnType::new(|x: i32| x.saturating_add(1));
    let g = FnType::new(|x: i32| x.saturating_mul(2));
    
    let left = functor.clone().fmap(f.clone()).fmap(g.clone());
    let right = functor.fmap(FnType::new(move |x| g.call(f.call(x))));
    left == right
}
