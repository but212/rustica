use crate::prelude::*;
use std::future::Future;
use std::pin::Pin;
use std::fmt;

/// A monad for asynchronous computations
/// 
/// `AsyncM` represents a computation that will produce a value of type `A` asynchronously.
/// It encapsulates a `Future` that can be run to obtain the final value.
/// 
/// # Type Parameters
/// 
/// * `A`: The type of value that will be produced asynchronously
/// 
/// # Examples
/// 
/// ```
/// use rustica::datatypes::async_monad::AsyncM;
/// use std::time::Duration;
/// use tokio::time::sleep;
/// 
/// # #[tokio::main]
/// # async fn main() {
/// let async_m = AsyncM::new(|| async {
///     sleep(Duration::from_secs(1)).await;
///     42
/// });
/// 
/// let result = async_m.run().await;
/// assert_eq!(result, 42);
/// # }
/// ```
pub struct AsyncM<A> {
    run: Pin<Box<dyn Future<Output = A> + Send + Sync + 'static>>,
}

impl<A> AsyncM<A>
where
    A: Send + Sync + 'static,
{
    /// Creates a new `AsyncM` from a function that produces a `Future`
    /// 
    /// # Type Parameters
    /// 
    /// * `Fut`: The type of the `Future` returned by `f`
    /// * `F`: The type of the function that produces the `Future`
    /// 
    /// # Arguments
    /// 
    /// * `f`: A function that, when called, produces a `Future`
    /// 
    /// # Returns
    /// 
    /// A new `AsyncM` instance encapsulating the `Future` produced by `f`
    pub fn new<Fut, F>(f: F) -> Self
    where
        Fut: Future<Output = A> + Send + Sync + 'static,
        F: FnOnce() -> Fut + Send + Sync + 'static,
    {
        AsyncM {
            run: Box::pin(f()),
        }
    }

    /// Runs the async computation and returns the result
    /// 
    /// # Returns
    /// 
    /// The value of type `A` produced by the async computation
    pub async fn run(self) -> A {
        self.run.await
    }
}

impl<A> fmt::Debug for AsyncM<A> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("AsyncM")
            .field("run", &"<future>")
            .finish()
    }
}

impl<A> Clone for AsyncM<A>
where
    A: Send + Sync + 'static,
{
    fn clone(&self) -> Self {
        // We can't clone futures, so we create a new one that returns a future
        AsyncM {
            run: Box::pin(async move { panic!("AsyncM::clone is not supported") }),
        }
    }
}

impl<A> Default for AsyncM<A>
where
    A: Default + Send + Sync + 'static,
{
    fn default() -> Self {
        AsyncM {
            run: Box::pin(std::future::ready(Default::default())),
        }
    }
}

impl<A> PartialEq for AsyncM<A>
where
    A: PartialEq + Send + Sync + 'static,
{
    fn eq(&self, _other: &Self) -> bool {
        // Futures cannot be compared for equality
        false
    }
}

impl<A> Eq for AsyncM<A> where A: Eq + Send + Sync + 'static {}

impl<A> HKT for AsyncM<A>
where
    A: TypeConstraints,
{
    type Output<T> = AsyncM<T> where T: TypeConstraints;
}

impl<A> Identity<A> for AsyncM<A>
where
    A: TypeConstraints,
{
    fn map_identity<B, F>(_f: F) -> Self::Output<B>
    where
        B: TypeConstraints,
        F: FnTrait<A, B>,
    {
        AsyncM::pure(B::default())
    }
}

impl<A> Functor<A> for AsyncM<A>
where
    A: TypeConstraints,
{
    fn fmap<B, F>(self, f: F) -> Self::Output<B>
    where
        B: TypeConstraints,
        F: FnTrait<A, B>,
    {
        AsyncM {
            run: Box::pin(async move {
                let a = self.run.await;
                f.call(a)
            }),
        }
    }
}

impl<A> Pure<A> for AsyncM<A>
where
    A: TypeConstraints,
{
    fn pure(a: A) -> Self {
        AsyncM {
            run: Box::pin(std::future::ready(a)),
        }
    }
}

impl<A> Applicative<A> for AsyncM<A>
where
    A: TypeConstraints,
{
    fn apply<B, F>(self, f: Self::Output<F>) -> Self::Output<B>
    where
        B: TypeConstraints,
        F: FnTrait<A, B>,
    {
        AsyncM {
            run: Box::pin(async move {
                let a = self.run.await;
                let f = f.run.await;
                f.call(a)
            }),
        }
    }

    fn lift2<B, C, F>(self, mb: Self::Output<B>, f: F) -> Self::Output<C>
    where
        B: TypeConstraints,
        C: TypeConstraints,
        F: FnTrait<(A, B), C>,
    {
        AsyncM {
            run: Box::pin(async move {
                let a = self.run.await;
                let b = mb.run.await;
                f.call((a, b))
            }),
        }
    }

    fn lift3<B, C, D, F>(self, mb: Self::Output<B>, mc: Self::Output<C>, f: F) -> Self::Output<D>
    where
        B: TypeConstraints,
        C: TypeConstraints,
        D: TypeConstraints,
        F: FnTrait<(A, B, C), D>,
    {
        AsyncM {
            run: Box::pin(async move {
                let a = self.run.await;
                let b = mb.run.await;
                let c = mc.run.await;
                f.call((a, b, c))
            }),
        }
    }
}

impl<A> Composable<A> for AsyncM<A>
where
    A: TypeConstraints,
{
    fn compose_with<B, F>(self, f: F) -> Self::Output<B>
    where
        B: TypeConstraints,
        F: FnTrait<A, B>,
    {
        AsyncM {
            run: Box::pin(async move {
                let a = self.run.await;
                f.call(a)
            }),
        }
    }
}

impl<A> Monad<A> for AsyncM<A>
where
    A: TypeConstraints,
{
    fn bind<B, F>(self, f: F) -> Self::Output<B>
    where
        B: TypeConstraints,
        F: FnTrait<A, AsyncM<B>>,
    {
        AsyncM {
            run: Box::pin(async move {
                let a = self.run.await;
                f.call(a).run.await
            }),
        }
    }

    fn join<B>(self) -> Self::Output<B>
    where
        B: TypeConstraints,
        A: Into<Self::Output<B>>,
    {
        AsyncM {
            run: Box::pin(async move {
                let ma = self.run.await;
                ma.into().run.await
            }),
        }
    }

    fn returns<B, F>(self, f: F) -> Self::Output<B>
    where
        B: TypeConstraints,
        F: FnTrait<A, B>,
    {
        self.fmap(f)
    }

    fn then<B>(self, mb: Self::Output<B>) -> Self::Output<B>
    where
        B: TypeConstraints,
    {
        AsyncM {
            run: Box::pin(async move {
                let _ = self.run.await;
                mb.run.await
            }),
        }
    }
}

impl<A> Category<A> for AsyncM<A>
where
    A: TypeConstraints,
{
    type Morphism<B, C> = FnType<B, C>
    where
        B: TypeConstraints,
        C: TypeConstraints;
}