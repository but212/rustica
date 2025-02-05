use crate::prelude::*;

/// A Reader monad that represents a computation with access to an environment.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Reader<E, A>
where
    E: ReturnTypeConstraints,
    A: ReturnTypeConstraints,
{
    /// The function that reads from the environment.
    run: SendSyncFn<E, A>,
}

impl<E, A> Reader<E, A>
where
    E: ReturnTypeConstraints,
    A: ReturnTypeConstraints,
{
    /// Creates a new reader computation.
    pub fn new<F>(f: F) -> Self
    where
        F: SendSyncFnTrait<E, A>,
    {
        Reader {
            run: SendSyncFn::new(move |e| f.call(e)),
        }
    }

    /// Runs the reader computation with the given environment.
    pub fn run_reader(&self, e: E) -> A {
        self.run.call(e)
    }
}

impl<E, A> HKT for Reader<E, A>
where
    E: ReturnTypeConstraints,
    A: ReturnTypeConstraints,
{
    type Output<T> = Reader<E, T> where T: ReturnTypeConstraints;
}

impl<E, A> Pure<A> for Reader<E, A>
where
    E: ReturnTypeConstraints,
    A: ReturnTypeConstraints,
{
    fn pure(value: A) -> Self::Output<A>
    {
        let value = value.clone();
        Reader::new(SendSyncFn::new(move |_: E| value.clone()))
    }
}

impl<E, A> Functor<A> for Reader<E, A>
where
    E: ReturnTypeConstraints,
    A: ReturnTypeConstraints,
{
    fn map<B, F>(self, f: F) -> Self::Output<B>
    where
        B: ReturnTypeConstraints,
        F: SendSyncFnTrait<A, B>,
    {
        let f = SendSyncFn::new(move |e: E| f.call(self.run_reader(e)));
        Reader { run: f }
    }
}

impl<E, A> Applicative<A> for Reader<E, A>
where
    E: ReturnTypeConstraints,
    A: ReturnTypeConstraints,
{
    fn apply<B, F>(self, mf: Self::Output<F>) -> Self::Output<B>
    where
        B: ReturnTypeConstraints,
        F: ApplyFn<A, B> + Default,
    {
        let f = SendSyncFn::new(move |e: E| {
            let f = mf.run_reader(e.clone());
            f.call(self.run_reader(e))
        });
        Reader { run: f }
    }

    fn lift2<B, C, F>(self, mb: Self::Output<B>, f: F) -> Self::Output<C>
    where
        B: ReturnTypeConstraints,
        C: ReturnTypeConstraints,
        F: ApplyFn<A, SendSyncFn<B, C>>,
    {
        let f = SendSyncFn::new(move |e: E| {
            let a = self.run_reader(e.clone());
            let b = mb.run_reader(e);
            f.call(a).call(b)
        });
        Reader { run: f }
    }

    fn lift3<B, C, D, F>(self, mb: Self::Output<B>, mc: Self::Output<C>, f: F) -> Self::Output<D>
    where
        B: ReturnTypeConstraints,
        C: ReturnTypeConstraints,
        D: ReturnTypeConstraints,
        F: ApplyFn<A, SendSyncFn<B, SendSyncFn<C, D>>>,
    {
        let f = SendSyncFn::new(move |e: E| {
            let a = self.run_reader(e.clone());
            let b = mb.run_reader(e.clone());
            let c = mc.run_reader(e);
            f.call(a).call(b).call(c)
        });
        Reader { run: f }
    }
}

impl<E, A> Monad<A> for Reader<E, A>
where
    E: ReturnTypeConstraints,
    A: ReturnTypeConstraints,
{
    fn bind<B, F>(self, f: F) -> Self::Output<B>
    where
        B: ReturnTypeConstraints,
        F: SendSyncFnTrait<A, Self::Output<B>>,
    {
        let f = SendSyncFn::new(move |e: E| {
            let a = self.run_reader(e.clone());
            f.call(a).run_reader(e)
        });
        Reader { run: f }
    }

    fn join<B>(self) -> Self::Output<B>
    where
        B: ReturnTypeConstraints,
        A: Into<Self::Output<B>>,
    {
        let f = SendSyncFn::new(move |e: E| {
            let inner = self.run_reader(e.clone());
            inner.into().run_reader(e)
        });
        Reader { run: f }
    }

    fn kleisli_compose<B, C, G, H>(g: G, h: H) -> SendSyncFn<A, Self::Output<C>>
    where
        B: ReturnTypeConstraints,
        C: ReturnTypeConstraints,
        G: MonadFn<A, B, Self::Output<B>> + Clone,
        H: MonadFn<B, C, Self::Output<C>> + Clone,
    {
        SendSyncFn::new(move |x| -> Self::Output<C> {
            g.call(x).bind(h.clone())
        })
    }
}

/// Gets the environment from a Reader.
pub fn ask<E>() -> Reader<E, E>
where
    E: ReturnTypeConstraints,
{
    Reader::new(SendSyncFn::new(|e: E| e))
}

/// Gets a function of the environment from a Reader.
pub fn asks<E, A, F>(f: F) -> Reader<E, A>
where
    E: ReturnTypeConstraints,
    A: ReturnTypeConstraints,
    F: SendSyncFnTrait<E, A>,
{
    Reader::new(f)
}

/// Modifies the environment before running a Reader.
pub fn local<E, A, F>(f: F, reader: Reader<E, A>) -> Reader<E, A>
where
    E: ReturnTypeConstraints,
    A: ReturnTypeConstraints,
    F: SendSyncFnTrait<E, E>,
{
    let f = SendSyncFn::new(move |e: E| reader.run_reader(f.call(e)));
    Reader { run: f }
}
