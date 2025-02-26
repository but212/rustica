mod test_functor;
mod test_applicative;
mod test_monad;
mod test_semigroup;
mod test_monoid;

use quickcheck::{Arbitrary, Gen};
use rustica::prelude::*;
use std::marker::PhantomData;

/// A test functor implementation that wraps a single value
#[derive(Clone, PartialEq, Debug)]
pub struct TestFunctor<T>(pub T, PhantomData<T>);

impl<T> TestFunctor<T> {
    pub fn new(value: T) -> Self {
        TestFunctor(value, PhantomData)
    }
}

impl<T: Arbitrary + 'static> Arbitrary for TestFunctor<T> {
    fn arbitrary(g: &mut Gen) -> Self {
        TestFunctor::new(T::arbitrary(g))
    }

    fn shrink(&self) -> Box<dyn Iterator<Item = Self>> {
        Box::new(self.0.shrink().map(TestFunctor::new))
    }
}

impl<T> HKT for TestFunctor<T> {
    type Source = T;
    type Output<U> = TestFunctor<U>;
}

impl<T> Identity for TestFunctor<T> {
    fn value(&self) -> &Self::Source {
        &self.0
    }
}

impl<T> Pure for TestFunctor<T> {
    fn pure<U: Clone>(value: U) -> Self::Output<U> {
        TestFunctor::new(value)
    }
}

impl<T> Functor for TestFunctor<T> {
    fn fmap<B>(&self, f: &dyn Fn(&Self::Source) -> B) -> Self::Output<B> {
        TestFunctor::new(f(&self.0))
    }
}

impl<T> Applicative for TestFunctor<T> {
    fn apply<B, F>(&self, f: &Self::Output<F>) -> Self::Output<B>
    where
        F: Fn(&Self::Source) -> B,
    {
        TestFunctor::new((f.0)(&self.0))
    }

    fn lift2<B, C>(
        &self,
        b: &Self::Output<B>,
        f: &dyn Fn(&Self::Source, &B) -> C,
    ) -> Self::Output<C> {
        TestFunctor::new(f(&self.0, &b.0))
    }

    fn lift3<B, C, D>(
        &self,
        b: &Self::Output<B>,
        c: &Self::Output<C>,
        f: &dyn Fn(&Self::Source, &B, &C) -> D,
    ) -> Self::Output<D> {
        TestFunctor::new(f(&self.0, &b.0, &c.0))
    }
}

impl<T: Clone> Monad for TestFunctor<T> {
    fn bind<U>(&self, f: &dyn Fn(&Self::Source) -> Self::Output<U>) -> Self::Output<U> {
        f(&self.0)
    }

    fn join<U>(&self) -> Self::Output<U>
    where
        T: Clone + Into<Self::Output<U>>,
    {
        self.0.clone().into()
    }
}

impl<T: Clone> Semigroup for TestFunctor<T>
where
    T: Semigroup,
{
    fn combine(&self, other: &Self) -> Self {
        TestFunctor::new(self.0.combine(&other.0))
    }
}

impl<T: Clone + Default> Monoid for TestFunctor<T>
where
    T: Monoid,
{
    fn empty() -> Self {
        TestFunctor::new(T::empty())
    }
}

impl<T> Composable for TestFunctor<T> {
    fn compose<U, V>(f: &dyn Fn(Self::Source) -> U, g: &dyn Fn(U) -> V) -> impl Fn(Self::Source) -> V {
        move |x| g(f(x))
    }
}