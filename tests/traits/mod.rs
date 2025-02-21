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
pub struct TestFunctor<T: TypeConstraints>(pub T);

impl<T: TypeConstraints + Arbitrary + 'static> Arbitrary for TestFunctor<T> {
    fn arbitrary(g: &mut Gen) -> Self {
        let value = T::arbitrary(g);
        TestFunctor(value)
    }

    fn shrink(&self) -> Box<dyn Iterator<Item = Self>> {
        Box::new(std::iter::empty())
    }
}

impl<T: TypeConstraints> HKT for TestFunctor<T> {
    type Output<U> = TestFunctor<U> where U: TypeConstraints;
}

impl<T: TypeConstraints> Identity<T> for TestFunctor<T> {
    fn identity() -> Self::Output<T> {
        TestFunctor(T::default())
    }

    fn map_identity<U, F>(f: F) -> Self::Output<U>
    where
        U: TypeConstraints,
        F: FnTrait<T, U>
    {
        TestFunctor(f.call(T::default()))
    }
}

impl<T: TypeConstraints> Pure<T> for TestFunctor<T> {
    fn pure(x: T) -> Self {
        TestFunctor(x)
    }
}

impl<T: TypeConstraints> Functor<T> for TestFunctor<T> {
    fn fmap<U, F>(self, f: F) -> TestFunctor<U>
    where
        U: TypeConstraints,
        F: FnTrait<T, U>,
    {
        TestFunctor(f.call(self.0))
    }
}

impl<T: TypeConstraints> Applicative<T> for TestFunctor<T> {
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

impl<T: TypeConstraints> Monad<T> for TestFunctor<T> {
    fn bind<B, F>(self, f: F) -> Self::Output<B>
    where
        B: TypeConstraints,
        F: FnTrait<T, Self::Output<B>>,
    {
        TestFunctor(f.call(self.0).0)
    }

    fn returns<B, F>(self, f: F) -> Self::Output<B>
    where
        B: TypeConstraints,
        F: FnTrait<T, B>,
    {
        TestFunctor(f.call(self.0))
    }

    fn then<B>(self, mb: Self::Output<B>) -> Self::Output<B>
    where
        B: TypeConstraints,
    {
        mb
    }

    fn join<B>(self) -> Self::Output<B>
    where
        B: TypeConstraints,
        T: Into<Self::Output<B>>,
    {
        self.0.into()
    }
}

impl<T: TypeConstraints> Composable<T> for TestFunctor<T> {
    fn compose_with<U, F>(self, f: F) -> Self::Output<U>
    where
        U: TypeConstraints,
        F: FnTrait<T, U>,
    {
        TestFunctor(f.call(self.0))
    }
}

impl<T: TypeConstraints> Category<T> for TestFunctor<T> {
    type Morphism<B, C> = FnType<B, C>
    where
        B: TypeConstraints,
        C: TypeConstraints;
}

impl<T: TypeConstraints> Arrow<T, T> for TestFunctor<T> {}