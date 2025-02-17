pub mod traits;
pub mod datatypes;

use std::fmt::Debug;
use quickcheck::{Arbitrary, Gen};
use quickcheck_macros::quickcheck;

use rustica::traits::functor::Functor;
use rustica::traits::pure::Pure;
use rustica::traits::hkt::{HKT, TypeConstraints};
use rustica::fntype::{FnType, FnTrait};

// Helper functions for property testing
fn id<T>(x: T) -> T {
    x
}

// Test data structures
#[derive(Debug, Clone, PartialEq, Eq, Default)]
struct TestFunctor<T>(T) where T: TypeConstraints;

impl<T> HKT for TestFunctor<T>
where
    T: TypeConstraints,
{
    type Output<B> = TestFunctor<B> where B: TypeConstraints;
}

impl<T> Arbitrary for TestFunctor<T>
where
    T: Arbitrary + TypeConstraints,
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
    T: TypeConstraints,
{
    fn fmap<U, F>(self, f: F) -> Self::Output<U>
    where
        U: TypeConstraints,
        F: FnTrait<T, U>,
    {
        TestFunctor(f.call(self.0))
    }
}

// Functor Laws
#[quickcheck]
fn functor_identity(x: TestFunctor<i32>) -> bool {
    x.clone().fmap(FnType::new(id)) == x
}

#[quickcheck]
fn functor_composition(x: TestFunctor<i32>) -> bool {
    // Use smaller numbers to avoid overflow
    let f = FnType::new(|x: i32| x.saturating_add(1));
    let g = FnType::new(|x: i32| x.saturating_mul(2));
    x.clone().fmap(f.clone()).fmap(g.clone()) == x.fmap(FnType::new(move |x| g.call(f.call(x))))
}

// Pure Laws
impl<T> Pure<T> for TestFunctor<T>
where
    T: TypeConstraints,
{
    fn pure(x: T) -> Self::Output<T> {
        TestFunctor(x)
    }
}

#[quickcheck]
fn pure_identity_preservation(x: i32) -> bool {
    let pure_x = TestFunctor::pure(x);
    pure_x.clone().fmap(FnType::new(id)) == pure_x
}

#[quickcheck]
fn pure_homomorphism(x: i32) -> bool {
    // Use a simpler function that won't overflow
    let f = FnType::new(|x: i32| x.saturating_add(1));
    let fx = f.call(x);
    TestFunctor::pure(fx) == TestFunctor::pure(x).fmap(f)
}
