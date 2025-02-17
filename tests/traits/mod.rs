pub mod functor;
pub mod monad;
pub mod applicative;
pub mod bifunctor;


use quickcheck::{Arbitrary, Gen};
use rustica::traits::applicative::Applicative;
use rustica::traits::functor::Functor;
use rustica::traits::hkt::{HKT, TypeConstraints};
use rustica::traits::identity::Identity;
use rustica::traits::monad::Monad;
use rustica::traits::pure::Pure;
use rustica::traits::category::Category;
use rustica::traits::arrow::Arrow;
use rustica::traits::composable::Composable;
use rustica::fntype::{FnType, FnTrait};

// Test data structures
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub struct TestFunctor<T>(pub T) where T: TypeConstraints;

impl<T> Arbitrary for TestFunctor<T>
where
    T: TypeConstraints + Arbitrary + 'static,
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
    T: TypeConstraints,
{
    type Output<U> = TestFunctor<U> where U: TypeConstraints;
}

impl<T> Identity for TestFunctor<T>
where
    T: TypeConstraints,
{}

impl<T> Pure<T> for TestFunctor<T>
where
    T: TypeConstraints,
{
    fn pure(x: T) -> Self {
        TestFunctor(x)
    }
}

impl<T> Functor<T> for TestFunctor<T>
where
    T: TypeConstraints,
{
    fn fmap<U, F>(self, f: F) -> TestFunctor<U>
    where
        U: TypeConstraints,
        F: FnTrait<T, U>,
    {
        TestFunctor(f.call(self.0))
    }
}

impl<T> Applicative<T> for TestFunctor<T>
where
    T: TypeConstraints,
{
    fn apply<U, F>(self, other: Self::Output<F>) -> Self::Output<U>
    where
        U: TypeConstraints,
        F: FnTrait<T, U>,
    {
        let f = other.0;
        TestFunctor(f.call(self.0))
    }

    fn lift2<U, V, F>(self, b: Self::Output<U>, f: F) -> Self::Output<V>
    where
        U: TypeConstraints,
        V: TypeConstraints,
        F: FnTrait<(T, U), V>,
    {
        let g = f.call((self.0, b.0));
        TestFunctor(g)
    }

    fn lift3<B, C, D, F>(
            self,
            b: Self::Output<B>,
            c: Self::Output<C>,
            f: F,
        ) -> Self::Output<D>
    where
        B: TypeConstraints,
        C: TypeConstraints,
        D: TypeConstraints,
        F: FnTrait<(T, B, C), D>,
    {
        let g = f.call((self.0, b.0, c.0));
        TestFunctor(g)
    }
}

impl<T> Monad<T> for TestFunctor<T>
where
    T: TypeConstraints,
{
    fn bind<U, F>(self, f: F) -> Self::Output<U>
    where
        U: TypeConstraints,
        F: FnTrait<T, Self::Output<U>>,
    {
        f.call(self.0)
    }

    fn join<U>(self) -> Self::Output<U>
    where
        U: TypeConstraints,
        T: Into<Self::Output<U>> + Send + Sync,
    {
        self.0.into()
    }
}

impl<T> Composable for TestFunctor<T>
where
    T: TypeConstraints,
{
    fn compose<U, V, W, F, G>(f: F, g: G) -> FnType<U, W>
    where
        U: TypeConstraints,
        V: TypeConstraints,
        W: TypeConstraints,
        F: FnTrait<U, V>,
        G: FnTrait<V, W>,
    {
        FnType::new(move |x| g.call(f.call(x)))
    }
}

impl<T> Category for TestFunctor<T>
where
    T: TypeConstraints,
{
    type Morphism<B, C> = FnType<B, C>
    where
        B: TypeConstraints,
        C: TypeConstraints;
}

impl<T: TypeConstraints> Arrow for TestFunctor<T> {}