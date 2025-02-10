use crate::prelude::*;
use crate::category::flatmap::FlatMap;
use crate::category::category::Category;
use crate::category::arrow::Arrow;
use crate::category::composable::Composable;
use crate::category::identity::Identity;

/// A free monad is a monad that allows for the construction of monadic computations
/// without specifying the underlying monad.
/// but it's currently unimplemented.
/// TODO: Implement the free monad.
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
    /// Creates a new Free monad with a pure value.
    pub fn pure(value: A) -> Self {
        Free::Pure(value)
    }

    /// Creates a new Free monad with a suspended effect.
    pub fn suspend(effect: S) -> Self {
        Free::Suspend(effect)
    }

    /// Runs the Free monad with the given interpreter.
    pub fn run<M, F>(self, interpreter: F) -> M::Output<A>
    where
        M: HKT + Pure<A>,
        M::Output<A>: ReturnTypeConstraints,
        F: FnTrait<S, M::Output<A>>,
    {
        match self {
            Free::Pure(x) => M::pure(x),
            Free::Suspend(effect) => interpreter.call(effect),
        }
    }
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
    type Output<T> = Free<S, T>
    where
        T: ReturnTypeConstraints;
}

impl<S, A> Functor<A> for Free<S, A>
where
    S: ReturnTypeConstraints,
    A: ReturnTypeConstraints,
{
    fn map<B, F>(self, f: F) -> Self::Output<B>
    where
        B: ReturnTypeConstraints,
        F: FnTrait<A, B>,
    {
        match self {
            Free::Pure(x) => Free::Pure(f.call(x)),
            Free::Suspend(effect) => Free::Suspend(effect),
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
    fn apply<B, F>(self, mf: Self::Output<F>) -> Self::Output<B>
    where
        B: ReturnTypeConstraints,
        F: FnTrait<A, B>,
    {
        match (self, mf) {
            (Free::Pure(x), Free::Pure(f)) => Free::Pure(f.call(x)),
            (Free::Suspend(effect), _) => Free::Suspend(effect),
            (_, Free::Suspend(effect)) => Free::Suspend(effect),
        }
    }

    fn lift2<B, C, F>(self, mb: Self::Output<B>, f: F) -> Self::Output<C>
    where
        B: ReturnTypeConstraints,
        C: ReturnTypeConstraints,
        F: FnTrait<A, FnType<B, C>>,
    {
        match (self, mb) {
            (Free::Pure(a), Free::Pure(b)) => Free::Pure(f.call(a).call(b)),
            (Free::Suspend(effect), _) => Free::Suspend(effect),
            (_, Free::Suspend(effect)) => Free::Suspend(effect),
        }
    }

    fn lift3<B, C, D, F>(
        self,
        mb1: Self::Output<B>,
        mb2: Self::Output<C>,
        f: F,
    ) -> Self::Output<D>
    where
        B: ReturnTypeConstraints,
        C: ReturnTypeConstraints,
        D: ReturnTypeConstraints,
        F: FnTrait<A, FnType<B, FnType<C, D>>>,
    {
        match (self, mb1, mb2) {
            (Free::Pure(a), Free::Pure(b), Free::Pure(c)) => {
                Free::Pure(f.call(a).call(b).call(c))
            }
            (Free::Suspend(effect), _, _) => Free::Suspend(effect),
            (_, Free::Suspend(effect), _) => Free::Suspend(effect),
            (_, _, Free::Suspend(effect)) => Free::Suspend(effect),
        }
    }
}

impl<S, A> Monad<A> for Free<S, A>
where
    S: ReturnTypeConstraints,
    A: ReturnTypeConstraints,
{
    fn bind<B, F>(self, f: F) -> Self::Output<B>
    where
        B: ReturnTypeConstraints,
        F: FnTrait<A, Self::Output<B>>,
    {
        match self {
            Free::Pure(x) => f.call(x),
            Free::Suspend(effect) => Free::Suspend(effect),
        }
    }

    fn join<B>(self) -> Self::Output<B>
    where
        B: ReturnTypeConstraints,
        A: Into<Self::Output<B>>,
    {
        match self {
            Free::Pure(x) => x.into(),
            Free::Suspend(effect) => Free::Suspend(effect),
        }
    }

    fn kleisli_compose<B, C, G, H>(g: G, h: H) -> FnType<A, Self::Output<C>>
    where
        B: ReturnTypeConstraints,
        C: ReturnTypeConstraints,
        G: FnTrait<A, Self::Output<B>> + Clone,
        H: FnTrait<B, Self::Output<C>> + Clone,
    {
        let h = h.clone();
        FnType::new(move |x| {
            let fx = g.call(x);
            fx.bind(h.clone())
        })
    }
}

impl<S, A> FlatMap<A> for Free<S, A>
where
    S: ReturnTypeConstraints,
    A: ReturnTypeConstraints,
{
    fn flat_map<B, F>(self, f: F) -> Self::Output<B>
    where
        B: ReturnTypeConstraints,
        F: FnTrait<A, Self::Output<B>>,
    {
        self.bind(f)
    }
}

impl<S, A> Identity for Free<S, A>
where
    S: ReturnTypeConstraints,
    A: ReturnTypeConstraints,
{
    fn identity<T>(x: T) -> T
    where
        T: ReturnTypeConstraints,
    {
        x
    }
}

impl<S, A> Composable for Free<S, A>
where
    S: ReturnTypeConstraints,
    A: ReturnTypeConstraints,
{
    fn compose<T, U, V, F, G>(f: F, g: G) -> FnType<T, V>
    where
        T: ReturnTypeConstraints,
        U: ReturnTypeConstraints,
        V: ReturnTypeConstraints,
        F: FnTrait<T, U>,
        G: FnTrait<U, V>,
    {
        FnType::new(move |x| g.call(f.call(x)))
    }
}

impl<S, A> Category<A> for Free<S, A>
where
    S: ReturnTypeConstraints,
    A: ReturnTypeConstraints,
{
    type Morphism<B, C> = Free<S, C>
    where
        B: ReturnTypeConstraints,
        C: ReturnTypeConstraints;

    fn identity_morphism<B>() -> Self::Morphism<B, B>
    where
        B: ReturnTypeConstraints,
    {
        Free::Pure(B::default())
    }

    fn compose_morphisms<B, C, D>(
        f: Self::Morphism<B, C>,
        g: Self::Morphism<C, D>
    ) -> Self::Morphism<B, D>
    where
        B: ReturnTypeConstraints,
        C: ReturnTypeConstraints,
        D: ReturnTypeConstraints,
    {
        match (f, g) {
            (Free::Pure(_), Free::Pure(d)) => Free::Pure(d),
            (Free::Pure(_), Free::Suspend(s)) => Free::Suspend(s),
            (Free::Suspend(s), _) => Free::Suspend(s),
        }
    }
}

impl<S, A> Arrow<A> for Free<S, A>
where
    S: ReturnTypeConstraints,
    A: ReturnTypeConstraints,
{
    fn arrow<B, C, F>(f: F) -> Self::Morphism<B, C>
    where
        B: ReturnTypeConstraints,
        C: ReturnTypeConstraints,
        F: FnTrait<B, C> + Clone,
    {
        Free::Pure(f.call(B::default()))
    }

    fn first<B, C, D>(f: Self::Morphism<B, C>) -> Self::Morphism<(B, D), (C, D)>
    where
        B: ReturnTypeConstraints,
        C: ReturnTypeConstraints,
        D: ReturnTypeConstraints,
    {
        match f {
            Free::Pure(c) => Free::Pure((c, D::default())),
            Free::Suspend(s) => Free::Suspend(s),
        }
    }
}