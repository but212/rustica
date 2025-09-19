mod monad_error;
mod monad_plus;
mod test_applicative;
mod test_bifunctor;
mod test_composable;
mod test_foldable;
mod test_functor;
mod test_identity;
mod test_monad;
mod test_monoid;
mod test_semigroup;

use quickcheck::{Arbitrary, Gen};
use rustica::prelude::*;
use rustica::traits::composable::Composable;
use rustica::traits::foldable::Foldable;
use rustica::traits::monad_error::{ErrorMapper, MonadError};
use rustica::traits::monoid::Monoid;
use rustica::traits::semigroup::Semigroup;
use std::fmt::Debug;
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

impl<T> Functor for TestFunctor<T> {
    fn fmap<B, F>(&self, f: F) -> Self::Output<B>
    where
        F: Fn(&Self::Source) -> B,
    {
        TestFunctor::new(f(&self.0))
    }

    fn fmap_owned<B, F>(self, f: F) -> Self::Output<B>
    where
        F: Fn(Self::Source) -> B,
    {
        TestFunctor::new(f(self.0))
    }
}

impl<T> Applicative for TestFunctor<T> {
    fn apply<A, B>(&self, value: &Self::Output<A>) -> Self::Output<B>
    where
        Self::Source: Fn(&A) -> B,
        B: Clone,
    {
        TestFunctor::new(self.0(&value.0))
    }

    fn lift2<A, B, C, F>(f: F, fa: &Self::Output<A>, fb: &Self::Output<B>) -> Self::Output<C>
    where
        F: Fn(&A, &B) -> C,
        A: Clone,
        B: Clone,
        C: Clone,
    {
        TestFunctor::new(f(&fa.0, &fb.0))
    }

    fn lift3<A, B, C, D, F>(
        f: F, fa: &Self::Output<A>, fb: &Self::Output<B>, fc: &Self::Output<C>,
    ) -> Self::Output<D>
    where
        F: Fn(&A, &B, &C) -> D,
        A: Clone,
        B: Clone,
        C: Clone,
        D: Clone,
    {
        TestFunctor::new(f(&fa.0, &fb.0, &fc.0))
    }

    fn apply_owned<U, B>(self, value: Self::Output<U>) -> Self::Output<B>
    where
        Self::Source: Fn(U) -> B,
    {
        // For TestFunctor, self.0 is the function and value.0 is the input
        TestFunctor::new((self.0)(value.0))
    }

    fn lift2_owned<A, B, C, F>(f: F, fa: Self::Output<A>, fb: Self::Output<B>) -> Self::Output<C>
    where
        F: Fn(A, B) -> C,
        A: Clone,
        B: Clone,
        C: Clone,
    {
        TestFunctor::new(f(fa.0, fb.0))
    }

    fn lift3_owned<A, B, C, D, F>(
        f: F, fa: Self::Output<A>, fb: Self::Output<B>, fc: Self::Output<C>,
    ) -> Self::Output<D>
    where
        F: Fn(A, B, C) -> D,
        A: Clone,
        B: Clone,
        C: Clone,
        D: Clone,
    {
        TestFunctor::new(f(fa.0, fb.0, fc.0))
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
        Self: Sized,
    {
        f(self.0)
    }

    fn join_owned<U>(self) -> Self::Output<U>
    where
        Self::Source: Into<Self::Output<U>>,
        U: Clone,
        Self: Sized,
    {
        self.0.into()
    }
}

impl<T: Clone> MonadError<String> for TestFunctor<T> {
    /// Creates a new instance in an error state - for TestFunctor we'll
    /// store the error message as a special marker value
    fn throw<U>(_error: String) -> Self::Output<U> {
        // In a real implementation, we'd store the error somehow
        // For the test functor, we'll create a special "error" marker value
        // Since we can't create a proper U type, we'll use a dummy value approach
        TestFunctor(unsafe { std::mem::zeroed() }, PhantomData)
    }

    /// For the test implementation, we'll assume TestFunctor can't be in an error state,
    /// so we just return self
    fn catch<F>(&self, _f: F) -> Self::Output<Self::Source>
    where
        F: Fn(&String) -> Self::Output<Self::Source>,
        Self::Source: Clone,
    {
        TestFunctor::new(self.0.clone())
    }

    /// Ownership-based version of catch
    fn catch_owned<F>(self, _f: F) -> Self::Output<Self::Source>
    where
        F: Fn(String) -> Self::Output<Self::Source>,
        Self::Source: Clone,
        Self: Sized,
    {
        self
    }
}

impl<T: Clone> ErrorMapper<String> for TestFunctor<T> {
    type Source = T;

    /// For the test implementation, we'll assume TestFunctor can't be in an error state,
    /// so mapping errors converts to Result::Ok
    fn map_error_to<NewE, F>(&self, _f: F) -> Result<Self::Source, NewE>
    where
        F: Fn(&String) -> NewE,
        Self::Source: Clone,
    {
        Ok(self.0.clone())
    }

    /// Ownership-based version of map_error_to
    fn map_error_to_owned<NewE, F>(self, _f: F) -> Result<Self::Source, NewE>
    where
        F: Fn(String) -> NewE,
        Self::Source: Clone,
        Self: Sized,
    {
        Ok(self.0)
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

impl<T> Foldable for TestFunctor<T> {
    fn fold_left<U: Clone, F>(&self, init: &U, f: F) -> U
    where
        F: Fn(&U, &Self::Source) -> U,
    {
        f(init, &self.0)
    }

    fn fold_right<U: Clone, F>(&self, init: &U, f: F) -> U
    where
        F: Fn(&Self::Source, &U) -> U,
    {
        f(&self.0, init)
    }
}
