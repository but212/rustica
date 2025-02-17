use quickcheck_macros::quickcheck;
use rustica::traits::applicative::Applicative;
use rustica::traits::pure::Pure;
use rustica::traits::functor::Functor;
use rustica::fntype::{FnType, FnTrait};

use super::TestFunctor;

#[quickcheck]
fn applicative_identity(x: i32) -> bool {
    let v = TestFunctor::pure(x);
    let id_fn = TestFunctor::pure(FnType::new(|x| x));
    let result = v.clone().apply(id_fn);
    result == v
}

#[quickcheck]
fn applicative_composition(x: i32) -> bool {
    let u = TestFunctor::pure(FnType::new(|x: i32| x.saturating_add(1)));
    let v = TestFunctor::pure(FnType::new(|x: i32| x.saturating_mul(2)));
    let w = TestFunctor::pure(x);
    
    let compose = TestFunctor::pure(FnType::new(|f: FnType<i32, i32>| {
        let f = f.clone();
        FnType::new(move |g: FnType<i32, i32>| {
            let f = f.clone();
            let g = g.clone();
            FnType::new(move |x| f.call(g.call(x)))
        })
    }));
    
    let left = w.clone()
        .apply(v.clone().apply(u.clone().apply(compose)));
    let right = w.apply(v).apply(u);
    
    left == right
}

#[quickcheck]
fn applicative_homomorphism(x: i32) -> bool {
    let f = FnType::new(|x: i32| x.saturating_add(1));
    let left = TestFunctor::pure(x).apply(TestFunctor::pure(f.clone()));
    let right = TestFunctor::pure(f.call(x));
    
    left == right
}

#[quickcheck]
fn applicative_interchange(y: i32) -> bool {
    let u = TestFunctor::pure(FnType::new(|x: i32| x.saturating_add(1)));
    let left = TestFunctor::pure(y).apply(u.clone());
    
    let apply_to = FnType::new(move |f: FnType<i32, i32>| f.call(y));
    let right = u.apply(TestFunctor::pure(apply_to));
    
    left == right
}

#[quickcheck]
fn applicative_naturality(x: i32) -> bool {
    let f = FnType::new(|x: i32| x.saturating_add(1));
    let g = FnType::new(|x: i32| x.saturating_mul(2));
    let test_x = TestFunctor::pure(x);
    let test_g = TestFunctor::pure(g);
    
    let left = TestFunctor::pure(f.call(test_x.clone().apply(test_g.clone()).0));
    
    let compose_fn = FnType::new(move |h: FnType<i32, i32>| {
        let f = f.clone();
        FnType::new(move |x| f.call(h.call(x)))
    });
    let right = test_x.apply(test_g.fmap(compose_fn));
    
    left == right
}

#[quickcheck]
fn applicative_functor_consistency(x: i32) -> bool {
    let f = FnType::new(|x: i32| x.saturating_add(1));
    let left = TestFunctor::pure(x).fmap(f.clone());
    let right = TestFunctor::pure(x).apply(TestFunctor::pure(f));
    
    left == right
}