use std::future::Future;
use futures::future::FutureExt;

use crate::category::hkt::{HKT, ReturnTypeConstraints};
use crate::category::applicative::Applicative;
use crate::category::functor::Functor;
use crate::category::pure::Pure;
use crate::category::monad::Monad;
use crate::category::category::Category;
use crate::category::composable::Composable;
use crate::category::identity::Identity;

use crate::fntype::{FnType, FnTrait};

/// An async monad that represents an asynchronous computation.
///
/// # Examples
///
/// ```
/// use rustica::monads::async_monad::AsyncM;
/// use rustica::category::pure::Pure;
/// use rustica::category::monad::Monad;
/// use rustica::fntype::{FnType, FnTrait};
///
/// let async_value = AsyncM::pure(42);
/// let doubled = async_value.bind(FnType::new(|x| AsyncM::pure(x * 2)));
/// assert_eq!(doubled.try_get(), 84);
/// ```
#[derive(Clone, Debug, PartialEq, Eq, Default)]
pub struct AsyncM<A>
where
    A: ReturnTypeConstraints,
{
    run: FnType<(), A>,
}

impl<A> AsyncM<A>
where
    A: ReturnTypeConstraints,
{
    /// Creates a new `AsyncM` instance from a given future.
    ///
    /// This function takes a future and wraps it in an `AsyncM`, allowing it to be used
    /// with the async monad interface.
    ///
    /// # Arguments
    ///
    /// * `future` - A future that will eventually resolve to a value of type `A`.
    ///
    /// # Returns
    ///
    /// Returns a new `AsyncM<A>` instance.
    ///
    /// # Type Parameters
    ///
    /// * `F` - The type of the future, which must implement `Future<Output = A>`,
    ///         `Send`, `Sync`, `Clone`, and have a `'static` lifetime.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::monads::async_monad::AsyncM;
    /// use std::future::Future;
    /// use futures::future::ready;
    ///
    /// let future = ready(42);
    /// let async_m = AsyncM::new(future);
    /// assert_eq!(async_m.try_get(), 42);
    /// ```
    pub fn new<F>(future: F) -> Self
    where
        F: Future<Output = A> + Send + Sync + Clone + 'static,
    {
        let shared = future.shared();
        AsyncM {
            run: FnType::new(move |_| {
                let shared = shared.clone();
                shared.now_or_never().unwrap_or_default()
            }),
        }
    }

    /// Attempts to retrieve the value from the `AsyncM` immediately.
    ///
    /// This method executes the internal computation synchronously and returns the result.
    /// If the computation hasn't completed yet, it will return the default value for type `A`.
    ///
    /// # Returns
    ///
    /// The computed value of type `A`, or its default if not ready.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::monads::async_monad::AsyncM;
    /// use rustica::category::pure::Pure;
    ///
    /// let async_value = AsyncM::pure(42);
    /// assert_eq!(async_value.try_get(), 42);
    /// ```
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
            run: FnType::new(move |_| value.clone()),
        }
    }
}

impl<A> Functor<A> for AsyncM<A>
where
    A: ReturnTypeConstraints,
{
    fn fmap<B, F>(self, f: F) -> Self::Output<B>
    where
        B: ReturnTypeConstraints,
        F: FnTrait<A, B>,
    {
        AsyncM {
            run: FnType::new(move |_| {
                let value = self.run.call(());
                f.call(value)
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
        F: FnTrait<A, B>,
    {
        self.fmap(FnType::new(move |a| mf.try_get().call(a)))
    }

    fn lift2<B, C, F>(self, mb: Self::Output<B>, f: F) -> Self::Output<C>
    where
        B: ReturnTypeConstraints,
        C: ReturnTypeConstraints,
        F: FnTrait<(A, B), C>,
    {
        AsyncM {
            run: FnType::new(move |_| {
                let a = self.try_get();
                let b = mb.try_get();
                f.call((a, b))
            }),
        }
    }

    fn lift3<B, C, D, F>(self, mb: Self::Output<B>, mc: Self::Output<C>, f: F) -> Self::Output<D>
    where
        B: ReturnTypeConstraints,
        C: ReturnTypeConstraints,
        D: ReturnTypeConstraints,
        F: FnTrait<(A, B, C), D>,
    {
        AsyncM {
            run: FnType::new(move |_| {
                let a = self.try_get();
                let b = mb.try_get();
                let c = mc.try_get();
                f.call((a, b, c))
            }),
        }
    }
}

impl<A: ReturnTypeConstraints> Identity for AsyncM<A> {}

impl<A: ReturnTypeConstraints> Composable for AsyncM<A> {}

impl<A: ReturnTypeConstraints> Category for AsyncM<A> {
    type Morphism<B, C> = FnType<B, C>
    where
        B: ReturnTypeConstraints,
        C: ReturnTypeConstraints;
}

impl<A> Monad<A> for AsyncM<A>
where
    A: ReturnTypeConstraints,
{
    fn bind<B, F>(self, f: F) -> Self::Output<B>
    where
        B: ReturnTypeConstraints,
        F: FnTrait<A, Self::Output<B>>,
    {
        self.fmap(FnType::new(move |a: A| f.call(a).try_get()))
    }

    fn join<B>(self) -> Self::Output<B>
    where
        B: ReturnTypeConstraints,
        A: Into<Self::Output<B>>,
    {
        self.bind(FnType::new(move |x: A| x.into()))
    }

    fn kleisli_compose<B, C, G, H>(g: G, h: H) -> FnType<A, Self::Output<C>>
    where
        B: ReturnTypeConstraints,
        C: ReturnTypeConstraints,
        G: FnTrait<A, Self::Output<B>>,
        H: FnTrait<B, Self::Output<C>>,
    {
        FnType::new(move |x| g.call(x).bind(h.clone()))
    }
}