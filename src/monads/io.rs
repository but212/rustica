use crate::prelude::*;

/// The IO monad.
/// it still needs a lot of work, Unimplemented!
#[derive(Debug, Clone, Default, PartialEq)]
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
    pub fn new<F>(f: F) -> Self
    where
        F: SendSyncFnTrait<(), A>,
    {
        IO { run: SendSyncFn::new(move |s| f.call(s)) }
    }

    /// Runs the IO computation.
    pub fn run(&self) -> A {
        self.run.call(())
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
        unimplemented!()
    }

    fn lift2<B, C, F>(self, mb: Self::Output<B>, f: F) -> Self::Output<C>
    where
        B: ReturnTypeConstraints,
        C: ReturnTypeConstraints,
        F: ApplyFn<A, SendSyncFn<B, C>>,
    {
        unimplemented!()
    }

    fn lift3<B, C, D, F>(self, mb: Self::Output<B>, mc: Self::Output<C>, f: F) -> Self::Output<D>
    where
        B: ReturnTypeConstraints,
        C: ReturnTypeConstraints,
        D: ReturnTypeConstraints,
        F: ApplyFn<A, SendSyncFn<B, SendSyncFn<C, D>>>,
    {
        unimplemented!()
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
        unimplemented!()
    }

    fn join<B>(self) -> Self::Output<B>
    where
        B: ReturnTypeConstraints,
    {
        unimplemented!()
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