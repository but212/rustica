use crate::prelude::*;
use crate::category::composable::Composable;
use crate::category::evaluate::Evaluate;
use crate::category::identity::Identity;
use crate::category::monoid::Monoid;
use crate::category::pure::Pure;
use crate::category::semigroup::Semigroup;

/// The IO monad.
/// it still needs a lot of work, Unimplemented!
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct IO<A>
where
    A: ReturnTypeConstraints,
{
    pub run: SendSyncFn<(), A>,
}

impl<A> IO<A>
where
    A: ReturnTypeConstraints,
{
    /// Creates a new IO computation.
    pub fn new(f: SendSyncFn<(), A>) -> Self
    {
        IO { run: f }
    }

    /// Runs the IO computation.
    pub fn run(&self) -> A {
        self.clone().evaluate()
    }
}

impl<A> HKT for IO<A>
where
    A: ReturnTypeConstraints,
{
    type Output<T> = IO<T> where T: ReturnTypeConstraints;
}

impl<A> Pure<A> for IO<A>
where
    A: ReturnTypeConstraints,
{
    fn pure(value: A) -> Self::Output<A> {
        Self::new(SendSyncFn::new(move |_s| value.clone()))
    }
}

impl<A> Functor<A> for IO<A>
where
    A: ReturnTypeConstraints,
{
    fn map<B, F>(self, f: F) -> Self::Output<B>
    where
        B: ReturnTypeConstraints,
        F: SendSyncFnTrait<A, B>,
    {
        let f = SendSyncFn::new(move |_s| f.call(self.run()));
        IO { run: f }
    }
}

impl<A> Applicative<A> for IO<A>
where
    A: ReturnTypeConstraints,
{
    fn apply<B, F>(self, f: Self::Output<F>) -> Self::Output<B>
    where
        B: ReturnTypeConstraints,
        F: ApplyFn<A, B>,
    {
        let f = SendSyncFn::new(move |_s| {
            let func = f.run.call(());
            func.call(self.run.call(()))
        });
        IO { run: f }
    }

    fn lift2<B, C, F>(self, mb: Self::Output<B>, f: F) -> Self::Output<C>
    where
        B: ReturnTypeConstraints,
        C: ReturnTypeConstraints,
        F: ApplyFn<A, SendSyncFn<B, C>>,
    {
        let f = SendSyncFn::new(move |_s| {
            let fa = f.call(self.run.call(()));
            fa.call(mb.run.call(()))
        });
        IO { run: f }
    }

    fn lift3<B, C, D, F>(self, mb: Self::Output<B>, mc: Self::Output<C>, f: F) -> Self::Output<D>
    where
        B: ReturnTypeConstraints,
        C: ReturnTypeConstraints,
        D: ReturnTypeConstraints,
        F: ApplyFn<A, SendSyncFn<B, SendSyncFn<C, D>>>,
    {
        let f = SendSyncFn::new(move |_s| {
            let fa = f.call(self.run.call(()));
            let fb = fa.call(mb.run.call(()));
            fb.call(mc.run.call(()))
        });
        IO { run: f }
    }
}

impl<A> Monad<A> for IO<A>
where
    A: ReturnTypeConstraints,
{
    fn bind<B, F>(self, f: F) -> Self::Output<B>
    where
        B: ReturnTypeConstraints,
        F: SendSyncFnTrait<A, Self::Output<B>>,
    {
        let f = SendSyncFn::new(move |_s| f.call(self.run.call(())).run.call(()));
        IO { run: f }
    }

    fn join<B>(self) -> Self::Output<B>
    where
        B: ReturnTypeConstraints,
        A: Into<Self::Output<B>>,
    {
        self.bind(SendSyncFn::new(move |x: A| x.into()))
    }

    fn kleisli_compose<B, C, G, H>(g: G, h: H) -> SendSyncFn<A, Self::Output<C>>
    where
        B: ReturnTypeConstraints,
        C: ReturnTypeConstraints,
        G: MonadFn<A, B, Self::Output<B>>,
        H: MonadFn<B, C, Self::Output<C>>,
    {
        SendSyncFn::new(move |x| -> Self::Output<C> {
            g.call(x).bind(h.clone())
        })
    }
}

impl<A> Composable for IO<A>
where
    A: ReturnTypeConstraints,
{
    fn compose<T, U, V, F, G>(f: F, g: G) -> SendSyncFn<T, V>
    where
        T: ReturnTypeConstraints,
        U: ReturnTypeConstraints,
        V: ReturnTypeConstraints,
        F: SendSyncFnTrait<T, U>,
        G: SendSyncFnTrait<U, V>,
    {
        SendSyncFn::new(move |x: T| {
            let u: U = f.call(x);
            g.call(u)
        })
    }
}


impl<A> Evaluate<A> for IO<A>
where
    A: ReturnTypeConstraints,
{
    fn evaluate(self) -> A {
        self.run.call(())
    }
}

impl<A> Identity for IO<A>
where
    A: ReturnTypeConstraints,
{
    fn identity<T>() -> Self::Output<T>
    where
        T: ReturnTypeConstraints,
    {
        IO { run: SendSyncFn::new(|_| panic!("Not implemented")) }
    }
}

impl<A> Semigroup for IO<A>
where
    A: Semigroup + ReturnTypeConstraints,
{
    fn combine(self, other: Self) -> Self {
        let f = SendSyncFn::new(move |_s| self.run.call(()).combine(other.run.call(())));
        IO { run: f }
    }
}

impl<A> Monoid for IO<A>
where
    A: Monoid + ReturnTypeConstraints,
{
    fn empty() -> Self {
        IO::new(SendSyncFn::new(|_| A::empty()))
    }
}
