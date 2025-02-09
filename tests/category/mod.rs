pub mod functor;
pub mod monad;

use quickcheck::{Arbitrary, Gen};
use rustica::category::applicative::Applicative;
use rustica::category::functor::Functor;
use rustica::category::hkt::{HKT, ReturnTypeConstraints};
use rustica::category::identity::Identity;
use rustica::category::monad::Monad;
use rustica::category::pure::Pure;
use rustica::fntype::{FnType, FnTrait};

// Test data structures
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct TestFunctor<T>(pub T) where T: ReturnTypeConstraints;

impl<T> Arbitrary for TestFunctor<T>
where
    T: ReturnTypeConstraints + Arbitrary + 'static,
{
    fn arbitrary(g: &mut Gen) -> Self {
        let value = T::arbitrary(g);
        TestFunctor(value)
    }

    fn shrink(&self) -> Box<dyn Iterator<Item = Self>> {
        Box::new(std::iter::empty())
    }
}

impl<T> HKT for TestFunctor<T>
where
    T: ReturnTypeConstraints,
{
    type Output<U> = TestFunctor<U> where U: ReturnTypeConstraints;
}

impl<T> Identity for TestFunctor<T>
where
    T: ReturnTypeConstraints,
{
    fn identity<U>() -> Self::Output<U>
    where
        U: ReturnTypeConstraints,
    {
        TestFunctor(U::default())
    }
}

impl<T> Pure<T> for TestFunctor<T>
where
    T: ReturnTypeConstraints,
{
    fn pure(x: T) -> Self {
        TestFunctor(x)
    }
}

impl<T> Functor<T> for TestFunctor<T>
where
    T: ReturnTypeConstraints,
{
    fn map<U, F>(self, f: F) -> TestFunctor<U>
    where
        U: ReturnTypeConstraints,
        F: FnTrait<T, U>,
    {
        TestFunctor(f.call(self.0))
    }
}

impl<T> Applicative<T> for TestFunctor<T>
where
    T: ReturnTypeConstraints,
{
    fn apply<U, F>(self, other: Self::Output<F>) -> Self::Output<U>
    where
        U: ReturnTypeConstraints,
        F: FnTrait<T, U>,
    {
        let f = other.0;
        TestFunctor(f.call(self.0))
    }

    fn lift2<U, V, F>(self, b: Self::Output<U>, f: F) -> Self::Output<V>
    where
        U: ReturnTypeConstraints,
        V: ReturnTypeConstraints,
        F: FnTrait<T, FnType<U, V>>,
    {
        let g = f.call(self.0);
        TestFunctor(g.call(b.0))
    }

    fn lift3<B, C, D, F>(
            self,
            b: Self::Output<B>,
            c: Self::Output<C>,
            f: F,
        ) -> Self::Output<D>
    where
        B: ReturnTypeConstraints,
        C: ReturnTypeConstraints,
        D: ReturnTypeConstraints,
        F: FnTrait<T, FnType<B, FnType<C, D>>>,
    {
        let g = f.call(self.0);
        let h = g.call(b.0);
        TestFunctor(h.call(c.0))
    }
}

impl<T> Monad<T> for TestFunctor<T>
where
    T: ReturnTypeConstraints,
{
    fn bind<U, F>(self, f: F) -> Self::Output<U>
    where
        U: ReturnTypeConstraints,
        F: FnTrait<T, Self::Output<U>>,
    {
        f.call(self.0)
    }

    fn join<U>(self) -> Self::Output<U>
    where
        U: ReturnTypeConstraints,
        T: Into<Self::Output<U>> + Send + Sync,
    {
        self.0.into()
    }

    fn kleisli_compose<B, C, G, H>(g: G, h: H) -> FnType<T, Self::Output<C>>
    where
        B: ReturnTypeConstraints,
        C: ReturnTypeConstraints,
        G: FnTrait<T, Self::Output<B>>,
        H: FnTrait<B, Self::Output<C>>,
    {
        FnType::new(move |x| g.call(x).bind(h.clone()))
    }
}