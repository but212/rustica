use quickcheck::{Arbitrary, Gen};
use quickcheck_macros::quickcheck;

use rustica::traits::functor::Functor;
use rustica::traits::hkt::TypeConstraints;
use rustica::traits::pure::Pure;
use rustica::fntype::{FnType, FnTrait};
use rustica::datatypes::cont::Cont;

/// Test wrapper type for Cont monad
#[derive(Clone, Debug)]
struct TestCont<A>(Cont<String, A>) where A: TypeConstraints;

impl<A> Arbitrary for TestCont<A>
where
    A: TypeConstraints + Arbitrary + 'static,
{
    fn arbitrary(g: &mut Gen) -> Self {
        let value = A::arbitrary(g);
        TestCont(Cont::pure(value))
    }

    fn shrink(&self) -> Box<dyn Iterator<Item = Self>> {
        Box::new(std::iter::empty())
    }
}

/// Core Continuation Laws
#[quickcheck]
fn cont_identity(x: i32) -> bool {
    let k = FnType::new(|x: i32| x.to_string());
    let cont = Cont::pure(x);
    cont.run(k.clone()) == k.call(x)
}

#[quickcheck]
fn cont_composition(x: i32) -> bool {
    let k2 = FnType::new(|x: i32| x.to_string());
    let cont = Cont::pure(x.saturating_add(2));
    let f = FnType::new(move |x: i32| x.saturating_add(1));
    
    let left = cont.clone().fmap(f.clone()).run(k2.clone());
    let right = k2.call(f.call(x.saturating_add(2)));
    left == right
}

/// Functor Laws
#[quickcheck]
fn functor_identity(x: TestCont<i32>) -> bool {
    let k = FnType::new(|x: i32| x.to_string());
    let cont = x.0;
    
    let left = cont.clone().fmap(FnType::new(|x| x)).run(k.clone());
    let right = cont.run(k);
    left == right
}

#[quickcheck]
fn functor_composition(x: TestCont<i32>) -> bool {
    let f = FnType::new(|x: i32| x.saturating_add(1));
    let g = FnType::new(|x: i32| x.saturating_mul(2));
    let k = FnType::new(|x: i32| x.to_string());
    let cont = x.0;
    
    let left = cont.clone().fmap(f.clone()).fmap(g.clone()).run(k.clone());
    let right = cont.fmap(f).fmap(g).run(k);
    left == right
}

/// Monad Laws
#[quickcheck]
fn monad_left_identity(x: i32) -> bool {
    let k = FnType::new(|x: i32| x.to_string());
    let f = FnType::new(|x: i32| x.saturating_add(1));
    
    let left = Cont::pure(x).fmap(f.clone()).run(k.clone());
    let right = k.call(f.call(x));
    left == right
}

#[quickcheck]
fn monad_right_identity(x: TestCont<i32>) -> bool {
    let k = FnType::new(|x: i32| x.to_string());
    let cont = x.0;
    
    let left = cont.clone().fmap(FnType::new(|x| x)).run(k.clone());
    let right = cont.run(k);
    left == right
}

#[quickcheck]
fn monad_associativity(x: TestCont<i32>) -> bool {
    let k = FnType::new(|x: i32| x.to_string());
    let f = FnType::new(|x: i32| x.saturating_add(1));
    let g = FnType::new(|x: i32| x.saturating_mul(2));
    let cont = x.0;
    
    let left = cont.clone()
        .fmap(f.clone())
        .fmap(g.clone())
        .run(k.clone());
    let right = cont.fmap(f).fmap(g).run(k);
    left == right
}
