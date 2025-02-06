use std::fmt::Debug;
use std::future::Future;
use futures::future::FutureExt;

use crate::category::hkt::{HKT, ReturnTypeConstraints};
use crate::category::applicative::Applicative;
use crate::category::functor::Functor;
use crate::category::pure::Pure;
use crate::category::monad::Monad;
use crate::fntype::{SendSyncFn, SendSyncFnTrait, ApplyFn, MonadFn};

/// An async monad that represents an asynchronous computation.
/// 
/// # Type Parameters
/// * `A` - The type to be computed asynchronously.
#[derive(Clone, Default, Debug, PartialEq, Eq)]
pub struct AsyncM<A>
where
    A: ReturnTypeConstraints,
{
    /// The function that produces the future.
    run: SendSyncFn<(), A>,
}

impl<A> AsyncM<A>
where
    A: ReturnTypeConstraints,
{
    /// Creates a new async computation.
    /// 
    /// # Type Parameters
    /// * `F` - The type of the future.
    /// 
    /// # Arguments
    /// * `future` - The future to be converted into an async computation.
    /// 
    /// Returns
    /// * `AsyncM<A>` - The new async computation.
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
    /// 
    /// Returns
    /// * `A` - The value of the async computation.
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
    /// Creates a new async computation that produces a pure value.
    /// 
    /// Returns
    /// * `AsyncM<A>` - The new async computation.
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
    /// Maps a function over the async computation.
    /// 
    /// # Type Parameters
    /// * `B` - The type of the result.
    /// * `F` - The type of the function.
    /// 
    /// Returns
    /// * `AsyncM<B>` - The new async computation.
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
    /// Applies a function to the async computation.
    /// 
    /// # Type Parameters
    /// * `B` - The type of the result.
    /// * `F` - The type of the function.
    /// 
    /// Returns
    /// * `AsyncM<B>` - The new async computation.
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

    /// Lifts a binary function into async computations.
    /// 
    /// # Type Parameters
    /// * `B` - The type of the first argument.
    /// * `C` - The type of the second argument.
    /// * `F` - The type of the function.
    /// 
    /// Returns
    /// * `AsyncM<C>` - The new async computation.
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

    /// Lifts a ternary function into async computations.
    /// 
    /// # Type Parameters
    /// * `B` - The type of the first argument.
    /// * `C` - The type of the second argument.
    /// * `D` - The type of the third argument.
    /// * `F` - The type of the function.
    /// 
    /// Returns
    /// * `AsyncM<D>` - The new async computation.
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
    /// Binds a function over the async computation.
    /// 
    /// # Type Parameters
    /// * `B` - The type of the result.
    /// * `F` - The type of the function.
    /// 
    /// Returns
    /// * `AsyncM<B>` - The new async computation.
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

    /// Joins two async computations.
    /// 
    /// # Type Parameters
    /// * `B` - The type of the result.
    /// 
    /// Returns
    /// * `AsyncM<B>` - The new async computation.
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

    /// Composes two monadic functions.
    /// 
    /// # Type Parameters
    /// * `B` - The type of the first argument.
    /// * `C` - The type of the second argument.
    /// * `G` - The type of the first monadic function.
    /// * `H` - The type of the second monadic function.
    /// 
    /// Returns
    /// * `SendSyncFn<A, Self::Output<C>>` - The new async computation.
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
