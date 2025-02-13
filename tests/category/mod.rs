pub mod functor;
pub mod monad;

use quickcheck::{Arbitrary, Gen};
use rustica::category::applicative::Applicative;
use rustica::category::functor::Functor;
use rustica::category::hkt::{HKT, TypeConstraints};
use rustica::category::identity::Identity;
use rustica::category::monad::Monad;
use rustica::category::pure::Pure;
use rustica::category::category::Category;
use rustica::category::arrow::Arrow;
use rustica::category::composable::Composable;
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

    fn kleisli_compose<B, C, G, H>(g: G, h: H) -> FnType<T, Self::Output<C>>
    where
        B: TypeConstraints,
        C: TypeConstraints,
        G: FnTrait<T, Self::Output<B>>,
        H: FnTrait<B, Self::Output<C>>,
    {
        FnType::new(move |x: T| -> Self::Output<C> {
            g.call(x).bind(h.clone())
        })
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

    fn identity_morphism<B>() -> Self::Morphism<B, B>
    where
        B: TypeConstraints,
    {
        FnType::new(|x| x)
    }

    fn compose_morphisms<B, C, D>(
        f: Self::Morphism<B, C>,
        g: Self::Morphism<C, D>
    ) -> Self::Morphism<B, D>
    where
        B: TypeConstraints,
        C: TypeConstraints,
        D: TypeConstraints,
    {
        FnType::new(move |x| g.call(f.call(x)))
    }
}

impl<T> Arrow for TestFunctor<T>
where
    T: TypeConstraints,
{
    fn arrow<B, C, F>(f: F) -> Self::Morphism<B, C>
    where
        B: TypeConstraints,
        C: TypeConstraints,
        F: FnTrait<B, C> + Clone,
    {
        FnType::new(move |x| f.call(x))
    }

    fn first<B, C, D>(f: Self::Morphism<B, C>) -> Self::Morphism<(B, D), (C, D)>
    where
        B: TypeConstraints,
        C: TypeConstraints,
        D: TypeConstraints,
    {
        FnType::new(move |(x, y)| (f.call(x), y))
    }
}