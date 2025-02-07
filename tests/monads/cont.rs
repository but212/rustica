use quickcheck::{Arbitrary, Gen};
use quickcheck_macros::quickcheck;

use rustica::category::functor::Functor;
use rustica::category::hkt::ReturnTypeConstraints;
use rustica::category::pure::Pure;
use rustica::fntype::SendSyncFn;
use rustica::monads::cont::Cont;

/// Test wrapper type for Cont monad
#[derive(Debug, Clone)]
struct TestCont<A>(Cont<String, A>) where A: ReturnTypeConstraints;

impl<A> Arbitrary for TestCont<A>
where
    A: ReturnTypeConstraints + Arbitrary + 'static,
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
    let k = SendSyncFn::new(|x: i32| x.to_string());
    let cont = Cont::pure(x);
    cont.run(k.clone()) == k.call(x)
}

#[quickcheck]
fn cont_composition(x: i32) -> bool {
    let k2 = SendSyncFn::new(|x: i32| x.to_string());
    let cont = Cont::pure(x.saturating_add(2));
    let f = SendSyncFn::new(move |x: i32| x.saturating_add(1));
    
    let left = cont.clone().map(f.clone()).run(k2.clone());
    let right = k2.call(f.call(x.saturating_add(2)));
    left == right
}

/// Functor Laws
#[quickcheck]
fn functor_identity(x: TestCont<i32>) -> bool {
    let k = SendSyncFn::new(|x: i32| x.to_string());
    let cont = x.0;
    
    let left = cont.clone().map(SendSyncFn::new(|x| x)).run(k.clone());
    let right = cont.run(k);
    left == right
}

#[quickcheck]
fn functor_composition(x: TestCont<i32>) -> bool {
    let f = SendSyncFn::new(|x: i32| x.saturating_add(1));
    let g = SendSyncFn::new(|x: i32| x.saturating_mul(2));
    let k = SendSyncFn::new(|x: i32| x.to_string());
    let cont = x.0;
    
    let left = cont.clone().map(f.clone()).map(g.clone()).run(k.clone());
    let right = cont.map(SendSyncFn::new(move |x| g.call(f.call(x)))).run(k);
    left == right
}

/// Monad Laws
#[quickcheck]
fn monad_left_identity(x: i32) -> bool {
    let k = SendSyncFn::new(|x: i32| x.to_string());
    let f = SendSyncFn::new(|x: i32| x.saturating_add(1));
    
    let left = Cont::pure(x).map(f.clone()).run(k.clone());
    let right = k.call(f.call(x));
    left == right
}

#[quickcheck]
fn monad_right_identity(x: TestCont<i32>) -> bool {
    let k = SendSyncFn::new(|x: i32| x.to_string());
    let cont = x.0;
    
    let left = cont.clone().map(SendSyncFn::new(|x| x)).run(k.clone());
    let right = cont.run(k);
    left == right
}

#[quickcheck]
fn monad_associativity(x: TestCont<i32>) -> bool {
    let k = SendSyncFn::new(|x: i32| x.to_string());
    let f = SendSyncFn::new(|x: i32| x.saturating_add(1));
    let g = SendSyncFn::new(|x: i32| x.saturating_mul(2));
    let cont = x.0;
    
    let left = cont.clone()
        .map(f.clone())
        .map(g.clone())
        .run(k.clone());
    let right = cont.map(SendSyncFn::new(move |x| g.call(f.call(x)))).run(k);
    left == right
}
