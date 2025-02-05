use std::fmt::Debug;
use std::sync::Arc;

use crate::category::{Applicative, Functor, HKT, Monad, Monoid, Pure, ReturnTypeConstraints};
use crate::fntype::{SendSyncFn, SendSyncFnTrait, ApplyFn, BindFn, MonadFn};

/// The writer monad.
#[derive(Clone, Default)]
pub struct Writer<W, A>
where
    W: ReturnTypeConstraints + Monoid,
    A: ReturnTypeConstraints,
{
    run_writer: SendSyncFn<(), (A, W)>,
}

impl<W, A> Debug for Writer<W, A>
where
    W: ReturnTypeConstraints + Monoid,
    A: ReturnTypeConstraints,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let (a, w) = self.run();
        write!(f, "Writer({:?}, {:?})", a, w)
    }
}

impl<W, A> PartialEq for Writer<W, A>
where
    W: ReturnTypeConstraints + Monoid,
    A: ReturnTypeConstraints,
{
    fn eq(&self, other: &Self) -> bool {
        let (a1, w1) = self.run();
        let (a2, w2) = other.run();
        a1 == a2 && w1 == w2
    }
}

impl<W, A> Eq for Writer<W, A>
where
    W: ReturnTypeConstraints + Monoid,
    A: ReturnTypeConstraints,
{}

impl<W, A> Writer<W, A>
where
    W: ReturnTypeConstraints + Monoid,
    A: ReturnTypeConstraints,
{
    /// Creates a new Writer from a value and a log.
    pub fn new(value: A, log: W) -> Self {
        let value = Arc::new(value);
        let log = Arc::new(log);
        Writer {
            run_writer: SendSyncFn::new(move |_| ((*value).clone(), (*log).clone())),
        }
    }

    /// Creates a new Writer that writes a log.
    pub fn tell(log: W) -> Writer<W, ()> {
        Writer::new((), log)
    }

    /// Runs the writer computation.
    pub fn run(&self) -> (A, W) {
        self.run_writer.call(())
    }

    /// Gets the value.
    pub fn value(&self) -> A {
        self.run().0
    }

    /// Gets the log.
    pub fn log(&self) -> W {
        self.run().1
    }
}

impl<W, A> HKT for Writer<W, A>
where
    W: ReturnTypeConstraints + Monoid,
    A: ReturnTypeConstraints,
{
    type Output<T> = Writer<W, T> where T: ReturnTypeConstraints;
}

impl<W, A> Pure<A> for Writer<W, A>
where
    W: ReturnTypeConstraints + Monoid,
    A: ReturnTypeConstraints,
{
    fn pure(value: A) -> Self::Output<A> {
        Writer::new(value, W::empty())
    }
}

impl<W, A> Functor<A> for Writer<W, A>
where
    W: ReturnTypeConstraints + Monoid,
    A: ReturnTypeConstraints,
{
    fn map<B, F>(self, f: F) -> Self::Output<B>
    where
        B: ReturnTypeConstraints,
        F: SendSyncFnTrait<A, B>,
    {
        Writer {
            run_writer: SendSyncFn::new(move |_| {
                let (a, w) = self.run();
                (f.call(a), w)
            }),
        }
    }
}

impl<W, A> Applicative<A> for Writer<W, A>
where
    W: ReturnTypeConstraints + Monoid,
    A: ReturnTypeConstraints,
{
    fn apply<B, F>(self, mf: Self::Output<F>) -> Self::Output<B>
    where
        B: ReturnTypeConstraints,
        F: ApplyFn<A, B>,
    {
        Writer {
            run_writer: SendSyncFn::new(move |_| {
                let (f, w1) = mf.run();
                let (a, w2) = self.run();
                (f.call(a), w1.combine(w2))
            }),
        }
    }

    fn lift2<B, C, F>(self, mb: Self::Output<B>, f: F) -> Self::Output<C>
    where
        B: ReturnTypeConstraints,
        C: ReturnTypeConstraints,
        F: ApplyFn<A, SendSyncFn<B, C>>,
    {
        Writer {
            run_writer: SendSyncFn::new(move |_| {
                let (a, w1) = self.run();
                let (b, w2) = mb.run();
                (f.call(a).call(b), w1.combine(w2))
            }),
        }
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
        F: ApplyFn<A, SendSyncFn<B, SendSyncFn<C, D>>>,
    {
        Writer {
            run_writer: SendSyncFn::new(move |_| {
                let (a, w1) = self.run();
                let (b, w2) = mb.run();
                let (c, w3) = mc.run();
                (f.call(a).call(b).call(c), w1.combine(w2).combine(w3))
            }),
        }
    }
}

impl<W, A> Monad<A> for Writer<W, A>
where
    W: ReturnTypeConstraints + Monoid,
    A: ReturnTypeConstraints,
{
    fn bind<B, F>(self, f: F) -> Self::Output<B>
    where
        B: ReturnTypeConstraints,
        F: BindFn<A, B, Self::Output<B>>,
    {
        Writer {
            run_writer: SendSyncFn::new(move |_| {
                let (a, w1) = self.run();
                let (b, w2) = f.call(a).run();
                (b, w1.combine(w2))
            }),
        }
    }

    fn join<B>(self) -> Self::Output<B>
    where
        B: ReturnTypeConstraints,
        A: Into<Self::Output<B>>,
    {
        Writer {
            run_writer: SendSyncFn::new(move |_| {
                let (ma, w1) = self.run();
                let (b, w2) = ma.into().run();
                (b, w1.combine(w2))
            }),
        }
    }

    fn kleisli_compose<B, C, G, H>(g: G, h: H) -> SendSyncFn<A, Self::Output<C>>
    where
        B: ReturnTypeConstraints,
        C: ReturnTypeConstraints,
        G: MonadFn<A, B, Self::Output<B>>,
        H: MonadFn<B, C, Self::Output<C>>,
    {
        SendSyncFn::new(move |x: A| -> Self::Output<C> {
            g.call(x).bind(h.clone())
        })
    }
}