use std::fmt::Debug;
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
/// # Type Parameters
/// * `A` - The type to be computed asynchronously.
///
/// # Laws
/// An AsyncM instance must satisfy these laws in addition to the standard Monad laws:
/// 1. Asynchronous Identity: For any value `x`,
///    `AsyncM::pure(x).try_get() = x`
/// 2. Asynchronous Bind: For any async computation `m` and function `f`,
///    `m.bind(f)` must execute `m` before applying `f`
/// 3. Future Consistency: For any Future `f`,
///    `AsyncM::new(f).bind(pure) = AsyncM::new(f)`
/// 4. Error Preservation: For any async computation `m` and function `f`,
///    If `m` fails with error `e`, then `m.bind(f)` must also fail with `e`
/// 5. Cancellation Preservation: For any async computation `m`,
///    `m.bind(f)` must preserve cancellation semantics of `m`
/// 6. Non-Blocking: `try_get()` must not block the current thread
/// 7. Resource Safety: For any async computation,
///    resources must be properly managed regardless of completion or failure
#[derive(Clone, Default, Debug, PartialEq, Eq)]
pub struct AsyncM<A>
where
    A: ReturnTypeConstraints,
{
    /// The function that produces the future.
    run: FnType<(), A>,
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
            run: FnType::new(move |_| {
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
            run: FnType::new(move |_| value.clone()),
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
        F: FnTrait<A, B>,
    {
        AsyncM {
            run: FnType::new(move |_| f.clone().call(self.try_get())),
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
        F: FnTrait<A, B>,
    {
        self.map(FnType::new(move |a| mf.try_get().call(a)))
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
        F: FnTrait<A, FnType<B, C>>,
    {
        self.map(FnType::new(move |a| f.call(a).call(mb.try_get())))
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
        F: FnTrait<A, FnType<B, FnType<C, D>>>,
    {
        self.map(FnType::new(move |a| f.call(a).call(mb.try_get()).call(mc.try_get())))
    }
}

impl<A> Identity for AsyncM<A>
where
    A: ReturnTypeConstraints,
{
    fn identity<T>(x: T) -> T
    where
        T: ReturnTypeConstraints,
    {
        x
    }
}

impl<A> Composable for AsyncM<A>
where
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

impl<A> Category<A> for AsyncM<A>
where
    A: ReturnTypeConstraints,
{
    type Morphism<B, C> = AsyncM<C>
    where
        B: ReturnTypeConstraints,
        C: ReturnTypeConstraints;

    fn identity_morphism<B>() -> Self::Morphism<B, B>
    where
        B: ReturnTypeConstraints,
    {
        AsyncM::pure(B::default())
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
        AsyncM::new(async move {
            let _c = f.try_get();
            g.try_get()
        })
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
        F: FnTrait<A, Self::Output<B>>,
    {
        self.map(FnType::new(move |a| f.call(a).try_get()))
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
        self.bind(FnType::new(move |x: A| x.into()))
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
    /// * `FnType<A, Self::Output<C>>` - The new async computation.
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
