use crate::prelude::*;

/// A free monad is a monad that allows for the construction of monadic computations
/// without specifying the underlying monad.
/// but it's currently unimplemented.
///
/// # Type Parameters
/// * `S` - The functor that represents the effect
/// * `A` - The type of the value contained in the monad
#[derive(Debug, PartialEq, Eq)]
pub enum Free<S, A>
where
    S: ReturnTypeConstraints,
    A: ReturnTypeConstraints,
{
    Suspend(S),
    Pure(A),
}

impl<S, A> Free<S, A>
where
    S: ReturnTypeConstraints,
    A: ReturnTypeConstraints,
{
}

impl<S, A> Clone for Free<S, A>
where
    S: ReturnTypeConstraints,
    A: ReturnTypeConstraints,
{
    fn clone(&self) -> Self {
        match self {
            Free::Pure(x) => Free::Pure(x.clone()),
            Free::Suspend(x) => Free::Suspend(x.clone()),
        }
    }
}

impl<S, A> Default for Free<S, A>
where
    S: ReturnTypeConstraints,
    A: ReturnTypeConstraints,
{
    fn default() -> Self {
        Free::Pure(A::default())
    }
}

impl<S, A> HKT for Free<S, A>
where
    S: ReturnTypeConstraints,
    A: ReturnTypeConstraints,
{
    type Output<B> = Free<S, B> where
        B: ReturnTypeConstraints;
}

impl<S, A> Functor<A> for Free<S, A>
where
    S: ReturnTypeConstraints,
    A: ReturnTypeConstraints,
{
    fn map<B, F>(self, f: F) -> Free<S, B>
    where
        B: ReturnTypeConstraints,
        F: FnTrait<A, B>,
    {
        match self {
            Free::Pure(value) => Free::Pure(f.call(value)),
            Free::Suspend(effect) => {
                // You need to implement the logic to handle the Suspend case appropriately.
                unimplemented!("Logic to handle Suspend effect needs to be implemented.")
            }
        }
    }
}

impl<S, A> Pure<A> for Free<S, A>
where
    S: ReturnTypeConstraints,
    A: ReturnTypeConstraints,
{
    fn pure(value: A) -> Self {
        Free::Pure(value)
    }
}

impl<S, A> Applicative<A> for Free<S, A>
where
    S: ReturnTypeConstraints,
    A: ReturnTypeConstraints,
{
    fn apply<B, F>(self, f: Free<S, F>) -> Free<S, B>
    where
        B: ReturnTypeConstraints,
        F: FnTrait<A, B>,
    {
        unimplemented!()
    }

    fn lift2<B, C, F>(self, mb: Self::Output<B>, f: F) -> Self::Output<C>
    where
        B: ReturnTypeConstraints,
        C: ReturnTypeConstraints,
        F: FnTrait<A, FnType<B, C>>,
    {
        unimplemented!()
    }

    fn lift3<B, C, D, F>(self, mb1: Self::Output<B>, mb2: Self::Output<C>, f: F) -> Self::Output<D>
    where
        B: ReturnTypeConstraints,
        C: ReturnTypeConstraints,
        D: ReturnTypeConstraints,
        F: FnTrait<A, FnType<B, FnType<C, D>>>,
    {
        unimplemented!()
    }
}

impl<S, A> Monad<A> for Free<S, A>
where
    S: ReturnTypeConstraints,
    A: ReturnTypeConstraints,
{
    fn bind<B, F>(self, f: F) -> Free<S, B>
    where
        B: ReturnTypeConstraints,
        F: FnTrait<A, Free<S, B>>,
    {
        unimplemented!()
    }

    fn join<B>(self) -> Free<S, B>
    where
        B: ReturnTypeConstraints,
    {
        unimplemented!()
    }

    fn kleisli_compose<B, C, G, H>(g: G, h: H) -> FnType<A, Self::Output<C>>
    where
        B: ReturnTypeConstraints,
        C: ReturnTypeConstraints,
        G: FnTrait<A, Self::Output<B>>,
        H: FnTrait<B, Self::Output<C>>,
    {
        FnType::new(move |a| g.call(a).bind(h.clone()))
    }
}