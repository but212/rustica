use std::fmt::Debug;
use std::future::Future;
use futures::future::FutureExt;

use crate::category::{Applicative, Functor, HKT, Monad, Pure, ReturnTypeConstraints};
use crate::fntype::{SendSyncFn, SendSyncFnTrait, ApplyFn, MonadFn};

/// An async monad that represents an asynchronous computation.
#[derive(Clone, Default)]
pub struct AsyncM<A>
where
    A: ReturnTypeConstraints,
{
    /// The function that produces the future.
    run: SendSyncFn<(), A>,
}

impl<A> Debug for AsyncM<A>
where
    A: ReturnTypeConstraints,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("AsyncM")
            .field("run", &"<future>")
            .finish()
    }
}

impl<A> PartialEq for AsyncM<A>
where
    A: ReturnTypeConstraints,
{
    fn eq(&self, _other: &Self) -> bool {
        // Futures cannot be compared for equality
        false
    }
}

impl<A> Eq for AsyncM<A>
where
    A: ReturnTypeConstraints,
{}

impl<A> AsyncM<A>
where
    A: ReturnTypeConstraints,
{
    /// Creates a new async computation.
    pub fn new<F>(future: F) -> Self
    where
        F: Future<Output = A> + Send + Sync + 'static,
    {
        let shared = future.shared();
        AsyncM {
            run: SendSyncFn::new(move |_| {
                let shared = shared.clone();
                shared.now_or_never().unwrap_or_default()
            }),
        }
    }

    /// Gets the value, if available without waiting.
    pub fn try_get(&self) -> A {
        self.run.call(())
    }
}

impl<A> HKT for AsyncM<A>
where
    A: ReturnTypeConstraints,
{
    type Output<T> = AsyncM<T> where T: ReturnTypeConstraints;
}

impl<A> Pure<A> for AsyncM<A>
where
    A: ReturnTypeConstraints,
{
    fn pure(value: A) -> Self::Output<A> {
        AsyncM {
            run: SendSyncFn::new(move |_| value.clone()),
        }
    }
}

impl<A> Functor<A> for AsyncM<A>
where
    A: ReturnTypeConstraints,
{
    fn map<B, F>(self, f: F) -> Self::Output<B>
    where
        B: ReturnTypeConstraints,
        F: SendSyncFnTrait<A, B>,
    {
        let f = f.clone();
        AsyncM {
            run: SendSyncFn::new(move |_| {
                let a = self.try_get();
                f.call(a)
            }),
        }
    }
}

impl<A> Applicative<A> for AsyncM<A>
where
    A: ReturnTypeConstraints,
{
    fn apply<B, F>(self, mf: Self::Output<F>) -> Self::Output<B>
    where
        B: ReturnTypeConstraints,
        F: ApplyFn<A, B> + Default,
    {
        AsyncM {
            run: SendSyncFn::new(move |_| {
                let f = mf.try_get();
                let a = self.try_get();
                f.call(a)
            }),
        }
    }

    fn lift2<B, C, F>(self, mb: Self::Output<B>, f: F) -> Self::Output<C>
    where
        B: ReturnTypeConstraints,
        C: ReturnTypeConstraints,
        F: ApplyFn<A, SendSyncFn<B, C>>,
    {
        AsyncM {
            run: SendSyncFn::new(move |_| {
                let a = self.try_get();
                let b = mb.try_get();
                f.call(a).call(b)
            }),
        }
    }

    fn lift3<B, C, D, F>(self, mb: Self::Output<B>, mc: Self::Output<C>, f: F) -> Self::Output<D>
    where
        B: ReturnTypeConstraints,
        C: ReturnTypeConstraints,
        D: ReturnTypeConstraints,
        F: ApplyFn<A, SendSyncFn<B, SendSyncFn<C, D>>>,
    {
        AsyncM {
            run: SendSyncFn::new(move |_| {
                let a = self.try_get();
                let b = mb.try_get();
                let c = mc.try_get();
                f.call(a).call(b).call(c)
            }),
        }
    }
}

impl<A> Monad<A> for AsyncM<A>
where
    A: ReturnTypeConstraints,
{
    fn bind<B, F>(self, f: F) -> Self::Output<B>
    where
        B: ReturnTypeConstraints,
        F: SendSyncFnTrait<A, Self::Output<B>>,
    {
        AsyncM {
            run: SendSyncFn::new(move |_| {
                let a = self.try_get();
                f.call(a).try_get()
            }),
        }
    }

    fn join<B>(self) -> Self::Output<B>
    where
        B: ReturnTypeConstraints,
        A: Into<Self::Output<B>>,
    {
        AsyncM {
            run: SendSyncFn::new(move |_| {
                let inner = self.try_get();
                inner.into().try_get()
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
        SendSyncFn::new(move |x| -> Self::Output<C> {
            g.call(x).bind(h.clone())
        })
    }
}
