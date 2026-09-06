mod algebraic_laws;
mod choice_and_iteration;
mod merging_laws;

use quickcheck::{Arbitrary, Gen};
use rustica::prelude::*;
use rustica::traits::foldable::Foldable;
use rustica::traits::monoid::Monoid;
use rustica::traits::semigroup::Semigroup;
use std::fmt::Debug;
use std::marker::PhantomData;

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

impl<T> Pure for TestFunctor<T> {
    fn pure<U>(value: U) -> Self::Output<U> {
        TestFunctor::new(value)
    }
}

impl<T> Functor for TestFunctor<T> {
    fn fmap<B, F>(self, mut f: F) -> Self::Output<B>
    where
        F: FnMut(Self::Source) -> B,
    {
        TestFunctor::new(f(self.0))
    }
}

impl<T> Applicative for TestFunctor<T> {
    fn apply<A, B>(self, value: Self::Output<A>) -> Self::Output<B>
    where
        Self::Source: Fn(A) -> B,
        A: Clone,
    {
        TestFunctor::new((self.0)(value.0))
    }
    fn lift2<A, B, C, F>(f: F, fa: Self::Output<A>, fb: Self::Output<B>) -> Self::Output<C>
    where
        F: Fn(A, B) -> C,
        A: Clone,
        B: Clone,
    {
        TestFunctor::new(f(fa.0, fb.0))
    }
    fn lift3<A, B, C, D, F>(
        f: F, fa: Self::Output<A>, fb: Self::Output<B>, fc: Self::Output<C>,
    ) -> Self::Output<D>
    where
        F: Fn(A, B, C) -> D,
        A: Clone,
        B: Clone,
        C: Clone,
    {
        TestFunctor::new(f(fa.0, fb.0, fc.0))
    }
}

impl<T> Monad for TestFunctor<T> {
    fn bind<U, F>(self, mut f: F) -> Self::Output<U>
    where
        F: FnMut(Self::Source) -> Self::Output<U>,
    {
        f(self.0)
    }
    fn join<U>(self) -> Self::Output<U>
    where
        Self::Source: Into<Self::Output<U>>,
    {
        self.0.into()
    }
}

impl<T: Semigroup> Semigroup for TestFunctor<T> {
    fn combine(self, other: Self) -> Self {
        TestFunctor::new(self.0.combine(other.0))
    }
}

impl<T: Monoid + Clone + Default> Monoid for TestFunctor<T> {
    fn empty() -> Self {
        TestFunctor::new(T::empty())
    }
}

impl<T> Foldable for TestFunctor<T> {
    fn fold_left<U, F>(&self, init: U, mut f: F) -> U
    where
        F: FnMut(U, &Self::Source) -> U,
    {
        f(init, &self.0)
    }
    fn fold_right<U, F>(&self, init: U, mut f: F) -> U
    where
        F: FnMut(&Self::Source, U) -> U,
    {
        f(&self.0, init)
    }
}
