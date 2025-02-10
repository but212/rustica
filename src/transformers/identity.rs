use crate::prelude::*;

/// Identity monad transformer.
/// This is the simplest monad transformer that adds no additional effects.
/// It is mainly used for testing and as a base case for monad transformer stacks.
/// but it's not yet implemented.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct IdentityT<M, A>
where
    M: HKT + ReturnTypeConstraints,
    M::Output<A>: ReturnTypeConstraints,
    A: ReturnTypeConstraints,
{
    run: M::Output<A>,
}

impl<M, A> IdentityT<M, A>
where
    M: HKT + ReturnTypeConstraints,
    M::Output<A>: ReturnTypeConstraints,
    A: ReturnTypeConstraints,
{
    pub fn new(m: M::Output<A>) -> Self {
        IdentityT { run: m }
    }

    pub fn run_identity_t(self) -> M::Output<A> {
        self.run
    }

    pub fn lift(m: M::Output<A>) -> Self {
        IdentityT::new(m)
    }
}

impl<M, A> Default for IdentityT<M, A>
where
    M: HKT + ReturnTypeConstraints,
    M::Output<A>: ReturnTypeConstraints + Default,
    A: ReturnTypeConstraints,
{
    fn default() -> Self {
        IdentityT::new(Default::default())
    }
}

impl<M, A> Identity for IdentityT<M, A>
where
    M: HKT + ReturnTypeConstraints,
    M::Output<A>: ReturnTypeConstraints,
    A: ReturnTypeConstraints,
{
}

impl<M, A> HKT for IdentityT<M, A>
where
    M: HKT + ReturnTypeConstraints,
    M::Output<A>: ReturnTypeConstraints,
    A: ReturnTypeConstraints,
{
    type Output<T> = IdentityT<M, T>
    where
        T: ReturnTypeConstraints,
        M::Output<T>: ReturnTypeConstraints;
}

impl<M, A> Pure<A> for IdentityT<M, A>
where
    M: HKT + ReturnTypeConstraints,
    M::Output<A>: ReturnTypeConstraints + Pure<A>,
    A: ReturnTypeConstraints,
{
    fn pure(x: A) -> Self {
        unimplemented!()
    }
}

impl<M, A> Functor<A> for IdentityT<M, A>
where
    M: HKT + ReturnTypeConstraints,
    M::Output<A>: ReturnTypeConstraints + Functor<A>,
    A: ReturnTypeConstraints,
{
    fn map<B, F>(self, f: F) -> Self::Output<B>
    where
        B: ReturnTypeConstraints,
        F: FnTrait<A, B>,
        M::Output<B>: ReturnTypeConstraints,
    {
        unimplemented!()
    }
}

impl<M, A> Applicative<A> for IdentityT<M, A>
where
    M: HKT + ReturnTypeConstraints,
    M::Output<A>: ReturnTypeConstraints + Applicative<A>,
    A: ReturnTypeConstraints,
{
    fn apply<B, F>(self, mf: Self::Output<F>) -> Self::Output<B>
    where
        B: ReturnTypeConstraints,
        F: FnTrait<A, B>,
        M::Output<B>: ReturnTypeConstraints,
        M::Output<F>: ReturnTypeConstraints,
    {
        unimplemented!()
    }

    fn lift2<B, C, F>(self, mb: Self::Output<B>, f: F) -> Self::Output<C>
    where
        B: ReturnTypeConstraints,
        C: ReturnTypeConstraints,
        F: FnTrait<A, FnType<B, C>>,
        M::Output<B>: ReturnTypeConstraints,
        M::Output<C>: ReturnTypeConstraints,
    {
        unimplemented!()
    }

    fn lift3<B, C, D, F>(
        self,
        mb: Self::Output<B>,
        mc: Self::Output<C>,
        f: F,
    ) -> Self::Output<D>
    where
        B: ReturnTypeConstraints,
        C: ReturnTypeConstraints,
        D: ReturnTypeConstraints,
        F: FnTrait<A, FnType<B, FnType<C, D>>>,
        M::Output<B>: ReturnTypeConstraints,
        M::Output<C>: ReturnTypeConstraints,
        M::Output<D>: ReturnTypeConstraints,
    {
        unimplemented!()
    }
}

impl<M, A> Composable for IdentityT<M, A>
where
    M: HKT + ReturnTypeConstraints,
    M::Output<A>: ReturnTypeConstraints + Composable,
    A: ReturnTypeConstraints,
{
    fn compose<T, U, V, F, G>(f: F, g: G) -> FnType<T, V>
        where
            T: ReturnTypeConstraints,
            U: ReturnTypeConstraints,
            V: ReturnTypeConstraints,
            F: FnTrait<T, U>,
            G: FnTrait<U, V>
    {
        unimplemented!()
    }
}

impl<M, A> Monad<A> for IdentityT<M, A>
where
    M: HKT + ReturnTypeConstraints,
    M::Output<A>: ReturnTypeConstraints + Monad<A>,
    A: ReturnTypeConstraints,
{
    fn bind<B, F>(self, f: F) -> Self::Output<B>
    where
        B: ReturnTypeConstraints,
        F: FnTrait<A, Self::Output<B>>,
        M::Output<B>: ReturnTypeConstraints,
    {
        unimplemented!()
    }

    fn join<B>(self) -> Self::Output<B>
    where
        B: ReturnTypeConstraints,
        A: Into<Self::Output<B>>,
        M::Output<B>: ReturnTypeConstraints,
    {
        unimplemented!()
    }

    fn kleisli_compose<B, C, G, H>(g: G, h: H) -> FnType<A, Self::Output<C>>
        where
            B: ReturnTypeConstraints,
            C: ReturnTypeConstraints,
            G: FnTrait<A, Self::Output<B>>,
            H: FnTrait<B, Self::Output<C>>
    {
        unimplemented!()
    }
}

impl<M, A> Category<A> for IdentityT<M, A>
where
    M: HKT + ReturnTypeConstraints,
    M::Output<A>: ReturnTypeConstraints + Category<A>,
    A: ReturnTypeConstraints,
{
    type Morphism<B, C> = IdentityT<M, C>
    where
        B: ReturnTypeConstraints,
        C: ReturnTypeConstraints,
        M::Output<C>: ReturnTypeConstraints;

    fn identity_morphism<B>() -> Self::Morphism<B, B>
    where
        B: ReturnTypeConstraints,
        M::Output<B>: ReturnTypeConstraints,
    {
        unimplemented!()
    }

    fn compose_morphisms<B, C, D>(
        f: Self::Morphism<B, C>,
        g: Self::Morphism<C, D>,
    ) -> Self::Morphism<B, D>
    where
        B: ReturnTypeConstraints,
        C: ReturnTypeConstraints,
        D: ReturnTypeConstraints,
        M::Output<B>: ReturnTypeConstraints,
        M::Output<C>: ReturnTypeConstraints,
        M::Output<D>: ReturnTypeConstraints,
    {
        unimplemented!()
    }
}

impl<M, A> Arrow<A> for IdentityT<M, A>
where
    M: HKT + ReturnTypeConstraints,
    M::Output<A>: ReturnTypeConstraints + Arrow<A>,
    A: ReturnTypeConstraints,
{
    fn arrow<B, C, F>(f: F) -> Self::Morphism<B, C>
    where
        B: ReturnTypeConstraints,
        C: ReturnTypeConstraints,
        F: FnTrait<B, C> + Clone,
        M::Output<B>: ReturnTypeConstraints,
        M::Output<C>: ReturnTypeConstraints,
    {
        unimplemented!()
    }

    fn first<B, C, D>(f: Self::Morphism<B, C>) -> Self::Morphism<(B, D), (C, D)>
    where
        B: ReturnTypeConstraints,
        C: ReturnTypeConstraints,
        D: ReturnTypeConstraints,
        M::Output<B>: ReturnTypeConstraints,
        M::Output<C>: ReturnTypeConstraints,
        M::Output<(B, D)>: ReturnTypeConstraints,
        M::Output<(C, D)>: ReturnTypeConstraints,
    {
        unimplemented!()
    }
}
