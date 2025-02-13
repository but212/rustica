use std::future::Future;
use futures::future::FutureExt;

use crate::traits::hkt::{HKT, TypeConstraints};
use crate::traits::applicative::Applicative;
use crate::traits::functor::Functor;
use crate::traits::pure::Pure;
use crate::traits::monad::Monad;
use crate::traits::category::Category;
use crate::traits::composable::Composable;
use crate::traits::identity::Identity;

use crate::fntype::{FnType, FnTrait};

/// An async monad that represents an asynchronous computation.
///
/// # Examples
///
/// ```
/// use rustica::datatypes::async_monad::AsyncM;
/// use rustica::traits::pure::Pure;
/// use rustica::traits::monad::Monad;
/// use rustica::fntype::{FnType, FnTrait};
///
/// let async_value = AsyncM::pure(42);
/// let doubled = async_value.bind(FnType::new(|x| AsyncM::pure(x * 2)));
/// assert_eq!(doubled.try_get(), 84);
/// ```
#[derive(Clone, Debug, PartialEq, Eq, Default)]
pub struct AsyncM<A>
where
    A: TypeConstraints,
{
    run: FnType<(), A>,
}

impl<A> AsyncM<A>
where
    A: TypeConstraints,
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
    /// use rustica::datatypes::async_monad::AsyncM;
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
    /// use rustica::datatypes::async_monad::AsyncM;
    /// use rustica::traits::pure::Pure;
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
    A: TypeConstraints,
{
    type Output<T> = AsyncM<T> where T: TypeConstraints;
}

impl<A> Pure<A> for AsyncM<A>
where
    A: TypeConstraints,
{
    fn pure(value: A) -> Self::Output<A> {
        AsyncM {
            run: FnType::new(move |_| value.clone()),
        }
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
            run: FnType::new(move |_| {
                let value = self.run.call(());
                f.call(value)
            }),
        }
    }
}

impl<A> Applicative<A> for AsyncM<A>
where
    A: TypeConstraints,
{
    fn apply<B, F>(self, mf: Self::Output<F>) -> Self::Output<B>
    where
        B: TypeConstraints,
        F: FnTrait<A, B>,
    {
        self.fmap(FnType::new(move |a| mf.try_get().call(a)))
    }

    fn lift2<B, C, F>(self, mb: Self::Output<B>, f: F) -> Self::Output<C>
    where
        B: TypeConstraints,
        C: TypeConstraints,
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
        B: TypeConstraints,
        C: TypeConstraints,
        D: TypeConstraints,
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

impl<A: TypeConstraints> Identity for AsyncM<A> {}

impl<A: TypeConstraints> Composable for AsyncM<A> {}

impl<A: TypeConstraints> Category for AsyncM<A> {
    type Morphism<B, C> = FnType<B, C>
    where
        B: TypeConstraints,
        C: TypeConstraints;
}

impl<A> Monad<A> for AsyncM<A>
where
    A: TypeConstraints,
{
    fn bind<B, F>(self, f: F) -> Self::Output<B>
    where
        B: TypeConstraints,
        F: FnTrait<A, Self::Output<B>>,
    {
        self.fmap(FnType::new(move |a: A| f.call(a).try_get()))
    }

    fn join<B>(self) -> Self::Output<B>
    where
        B: TypeConstraints,
        A: Into<Self::Output<B>>,
    {
        self.bind(FnType::new(move |x: A| x.into()))
    }
}