pub mod cont;

use quickcheck_macros::quickcheck;
use rustica::category::pure::Pure;
use rustica::category::functor::Functor;
use rustica::category::hkt::{HKT, ReturnTypeConstraints};
use rustica::fntype::{SendSyncFn, SendSyncFnTrait};

#[derive(Clone, Debug, PartialEq, Eq, Default)]
struct TestFunctor<A: ReturnTypeConstraints>(A);

impl<A: ReturnTypeConstraints> HKT for TestFunctor<A> {
    type Output<T: ReturnTypeConstraints> = TestFunctor<T>;
}

impl<A: ReturnTypeConstraints> Pure<A> for TestFunctor<A> {
    fn pure(x: A) -> Self {
        TestFunctor(x)
    }
}

impl<A: ReturnTypeConstraints> Functor<A> for TestFunctor<A> {
    fn map<B, F>(self, f: F) -> Self::Output<B>
    where
        B: ReturnTypeConstraints,
        F: SendSyncFnTrait<A, B>,
    {
        TestFunctor(f.call(self.0))
    }
}

// Monad Laws
#[quickcheck]
fn monad_left_identity(x: i32) -> bool {
    let k = SendSyncFn::new(|x: i32| x.to_string());
    let f = SendSyncFn::new(|x: String| TestFunctor(x));
    
    let left = TestFunctor::pure(x).map(k.clone()).map(f.clone());
    let right = TestFunctor(f.call(k.call(x)));
    left == right
}

#[quickcheck]
fn monad_right_identity(x: i32) -> bool {
    let cont = TestFunctor::pure(x);
    
    let left = cont.clone().map(SendSyncFn::new(|x| x));
    let right = cont;
    left == right
}

#[quickcheck]
fn monad_associativity(x: i32) -> bool {
    let m = TestFunctor::pure(x);
    let f = SendSyncFn::new(|x: i32| x.saturating_add(1));
    let g = SendSyncFn::new(|x: i32| x.saturating_mul(2));
    
    let left = m.clone()
        .map(f.clone())
        .map(g.clone());
    let right = m.map(SendSyncFn::new(move |x| g.call(f.call(x))));
    left == right
}
