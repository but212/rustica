mod test_functor;
mod test_applicative;
mod test_monad;
mod test_semigroup;
mod test_monoid;
mod test_identity;

use quickcheck::{Arbitrary, Gen};
use rustica::prelude::*;
use rustica::traits::semigroup::Semigroup;
use rustica::traits::monoid::Monoid;
use rustica::traits::composable::Composable;
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
    
    fn pure_identity<A>(value: A) -> Self::Output<A> {
        TestFunctor::new(value)
    }
    
    fn into_value(self) -> Self::Source {
        self.0
    }
}

impl<T> Pure for TestFunctor<T> {
    fn pure<U: Clone>(value: &U) -> Self::Output<U> {
        TestFunctor::new(value.clone())
    }
}

impl<T> Transform for TestFunctor<T> {
    fn transform<F, NewType>(&self, f: F) -> Self::Output<NewType>
    where
        F: Fn(&Self::Source) -> NewType,
    {
        TestFunctor::new(f(&self.0))
    }

    fn transform_owned<F, NewType>(self, f: F) -> Self::Output<NewType>
    where
        F: Fn(Self::Source) -> NewType,
    {
        TestFunctor::new(f(self.0))
    }
}

impl<T> Functor for TestFunctor<T> {}

impl<T> Applicative for TestFunctor<T> {
    fn apply<B, F>(&self, f: &Self::Output<F>) -> Self::Output<B>
    where
        F: Fn(&Self::Source) -> B,
    {
        TestFunctor::new(f.0(&self.0))
    }

    fn lift2<B, C, F>(
        &self,
        b: &Self::Output<B>,
        f: F,
    ) -> Self::Output<C> 
    where
        F: Fn(&Self::Source, &B) -> C,
    {
        TestFunctor::new(f(&self.0, &b.0))
    }

    fn lift3<B, C, D, F>(
        &self,
        b: &Self::Output<B>,
        c: &Self::Output<C>,
        f: F,
    ) -> Self::Output<D> 
    where
        F: Fn(&Self::Source, &B, &C) -> D,
    {
        TestFunctor::new(f(&self.0, &b.0, &c.0))
    }

    fn apply_owned<B, F>(self, f: Self::Output<F>) -> Self::Output<B>
        where
            F: Fn(Self::Source) -> B,
            Self: Sized {
        TestFunctor::new(f.0(self.0))
    }

    fn lift2_owned<B, C, F>(
            self,
            b: Self::Output<B>,
            f: F,
        ) -> Self::Output<C>
        where
            F: Fn(Self::Source, B) -> C,
            Self: Sized,
            B: Clone {
        TestFunctor::new(f(self.0, b.0))
    }

    fn lift3_owned<B, C, D, F>(
            self,
            b: Self::Output<B>,
            c: Self::Output<C>,
            f: F,
        ) -> Self::Output<D>
        where
            F: Fn(Self::Source, B, C) -> D,
            Self: Sized,
            B: Clone,
            C: Clone {
        TestFunctor::new(f(self.0, b.0, c.0))
    }
}

impl<T: Clone> Monad for TestFunctor<T> {
    fn bind<U, F>(&self, f: F) -> Self::Output<U>
    where
        F: Fn(&Self::Source) -> Self::Output<U>,
    {
        f(&self.0)
    }

    fn join<U>(&self) -> Self::Output<U>
    where
        T: Clone + Into<Self::Output<U>>,
    {
        self.0.clone().into()
    }

    fn bind_owned<U, F>(self, f: F) -> Self::Output<U>
        where
            F: Fn(Self::Source) -> Self::Output<U>,
            U: Clone,
            Self: Sized {
        f(self.0)
    }

    fn join_owned<U>(self) -> Self::Output<U>
        where
            Self::Source: Into<Self::Output<U>>,
            U: Clone,
            Self: Sized {
        self.0.into()
    }
}

impl<T: Semigroup + Clone> Semigroup for TestFunctor<T> {
    fn combine(&self, other: &Self) -> Self {
        TestFunctor::new(self.0.combine(&other.0))
    }

    fn combine_owned(self, other: Self) -> Self {
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
    fn compose<U, V, F, G>(f: F, g: G) -> impl Fn(Self::Source) -> V
    where
        F: Fn(Self::Source) -> U,
        G: Fn(U) -> V,
    {
        move |x| g(f(x))
    }
}