pub mod category;
pub mod monads;

use std::fmt::Debug;
use quickcheck::{Arbitrary, Gen};
use quickcheck_macros::quickcheck;

use rustica::category::functor::Functor;
use rustica::category::pure::Pure;
use rustica::category::hkt::{HKT, ReturnTypeConstraints};
use rustica::fntype::{FnType, FnTrait};

// Helper functions for property testing
fn id<T>(x: T) -> T {
    x
}

// Test data structures
#[derive(Debug, Clone, PartialEq, Eq, Default)]
struct TestFunctor<T>(T) where T: ReturnTypeConstraints;

impl<T> HKT for TestFunctor<T>
where
    T: ReturnTypeConstraints,
{
    type Output<B> = TestFunctor<B> where B: ReturnTypeConstraints;
}

impl<T> Arbitrary for TestFunctor<T>
where
    T: Arbitrary + ReturnTypeConstraints,
{
    fn arbitrary(g: &mut Gen) -> Self {
        TestFunctor(T::arbitrary(g))
    }

    fn shrink(&self) -> Box<dyn Iterator<Item = Self>> {
        Box::new(self.0.shrink().map(TestFunctor))
    }
}

impl<T> Functor<T> for TestFunctor<T>
where
    T: ReturnTypeConstraints,
{
    fn map<U, F>(self, f: F) -> Self::Output<U>
    where
        U: ReturnTypeConstraints,
        F: FnTrait<T, U>,
    {
        TestFunctor(f.call(self.0))
    }
}

// Functor Laws
#[quickcheck]
fn functor_identity(x: TestFunctor<i32>) -> bool {
    x.clone().map(FnType::new(id)) == x
}

#[quickcheck]
fn functor_composition(x: TestFunctor<i32>) -> bool {
    // Use smaller numbers to avoid overflow
    let f = FnType::new(|x: i32| x.saturating_add(1));
    let g = FnType::new(|x: i32| x.saturating_mul(2));
    x.clone().map(f.clone()).map(g.clone()) == x.map(FnType::new(move |x| g.call(f.call(x))))
}

// Pure Laws
impl<T> Pure<T> for TestFunctor<T>
where
    T: ReturnTypeConstraints,
{
    fn pure(x: T) -> Self::Output<T> {
        TestFunctor(x)
    }
}

#[quickcheck]
fn pure_identity_preservation(x: i32) -> bool {
    let pure_x = TestFunctor::pure(x);
    pure_x.clone().map(FnType::new(id)) == pure_x
}

#[quickcheck]
fn pure_homomorphism(x: i32) -> bool {
    // Use a simpler function that won't overflow
    let f = FnType::new(|x: i32| x.saturating_add(1));
    let fx = f.call(x);
    TestFunctor::pure(fx) == TestFunctor::pure(x).map(f)
}
