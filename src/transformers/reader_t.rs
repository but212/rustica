//! Reader monad transformer.
//!
//! `ReaderT<E, M, A>` represents an environment-dependent computation whose
//! base monad `M` contains `A`. The `HKT<Source = A>` bound makes that
//! relationship part of the type instead of a convention maintained by callers.

use super::MonadTransformer;
use crate::error::{ComposableError, ComposableResult, IntoErrorContext};
use crate::traits::hkt::HKT;
use crate::traits::monad::Monad;
use std::marker::PhantomData;
use std::sync::Arc;

type ReaderRun<E, M> = dyn Fn(E) -> M + Send + Sync;

/// An environment-dependent computation in a base monad containing `A`.
pub struct ReaderT<E, M, A>
where
    M: HKT<Source = A>,
{
    run_reader_fn: Arc<ReaderRun<E, M>>,
    _value: PhantomData<A>,
}

impl<E, M, A> Clone for ReaderT<E, M, A>
where
    M: HKT<Source = A>,
{
    fn clone(&self) -> Self {
        Self {
            run_reader_fn: Arc::clone(&self.run_reader_fn),
            _value: PhantomData,
        }
    }
}

impl<E, M, A> ReaderT<E, M, A>
where
    E: 'static,
    M: HKT<Source = A> + 'static,
    A: 'static,
{
    /// Creates a reader from an environment-to-monad function.
    #[inline]
    pub fn new<F>(f: F) -> Self
    where
        F: Fn(E) -> M + Send + Sync + 'static,
    {
        Self {
            run_reader_fn: Arc::new(f),
            _value: PhantomData,
        }
    }

    /// Runs the computation with an environment.
    #[inline]
    pub fn run_reader(&self, env: E) -> M {
        (self.run_reader_fn)(env)
    }

    /// Runs the computation after transforming its environment.
    #[inline]
    pub fn local<F>(&self, f: F) -> Self
    where
        F: Fn(E) -> E + Send + Sync + 'static,
    {
        let run = Arc::clone(&self.run_reader_fn);
        Self::new(move |env| run(f(env)))
    }

    /// Creates a reader that returns its environment.
    pub fn ask<P>(pure: P) -> ReaderT<E, M::Output<E>, E>
    where
        P: Fn(E) -> M::Output<E> + Send + Sync + 'static,
        M::Output<E>: 'static,
    {
        ReaderT::new(pure)
    }

    /// Maps the environment into a value and lifts it into the base family.
    pub fn asks<B, F, P>(f: F, pure: P) -> ReaderT<E, M::Output<B>, B>
    where
        F: Fn(E) -> B + Send + Sync + 'static,
        P: Fn(B) -> M::Output<B> + Send + Sync + 'static,
        B: 'static,
        M::Output<B>: 'static,
    {
        ReaderT::new(move |env| pure(f(env)))
    }

    /// Borrowing form of [`ReaderT::asks`].
    pub fn ask_with<B, F, P>(f: F, pure: P) -> ReaderT<E, M::Output<B>, B>
    where
        F: Fn(&E) -> B + Send + Sync + 'static,
        P: Fn(B) -> M::Output<B> + Send + Sync + 'static,
        B: 'static,
        M::Output<B>: 'static,
    {
        ReaderT::new(move |env| pure(f(&env)))
    }

    /// Selects and transforms part of the environment before lifting it.
    pub fn asks_with<B, C, Select, Transform, P>(
        select: Select, transform: Transform, pure: P,
    ) -> ReaderT<E, M::Output<C>, C>
    where
        Select: Fn(&E) -> B + Send + Sync + 'static,
        Transform: Fn(B) -> C + Send + Sync + 'static,
        P: Fn(C) -> M::Output<C> + Send + Sync + 'static,
        B: 'static,
        C: 'static,
        M::Output<C>: 'static,
    {
        ReaderT::new(move |env| pure(transform(select(&env))))
    }

    /// Runs and returns the base monad.
    #[inline]
    pub fn unwrap_with(self, env: E) -> M {
        self.run_reader(env)
    }

    /// Returns a reusable binary-reader lifting function.
    #[allow(clippy::type_complexity)]
    pub fn lift2<B, C, F, CombineFn>(
        f: F, combine_fn: CombineFn,
    ) -> impl Fn(&ReaderT<E, M, A>, &ReaderT<E, M::Output<B>, B>) -> ReaderT<E, M::Output<C>, C>
    + Send
    + Sync
    + 'static
    where
        E: Clone,
        F: Fn(A, B) -> C + Clone + Send + Sync + 'static,
        CombineFn: Fn(M, M::Output<B>, F) -> M::Output<C> + Clone + Send + Sync + 'static,
        B: 'static,
        C: 'static,
        M::Output<B>: 'static,
        M::Output<C>: 'static,
    {
        move |left, right| {
            let left_fn = Arc::clone(&left.run_reader_fn);
            let right_fn = Arc::clone(&right.run_reader_fn);
            let combine = combine_fn.clone();
            let f = f.clone();
            ReaderT::new(move |env: E| combine(left_fn(env.clone()), right_fn(env), f.clone()))
        }
    }

    /// Lifts a pure value into the base monad without reading the environment.
    pub fn pure<F>(value: A, pure_fn: F) -> Self
    where
        E: Send + Sync,
        A: Clone + Send + Sync,
        F: Fn(A) -> M + Send + Sync + 'static,
    {
        Self::new(move |_| pure_fn(value.clone()))
    }
}

impl<E, M, A> ReaderT<E, M, A>
where
    E: Clone + 'static,
    M: Monad<Source = A> + Clone + 'static,
    A: Clone + 'static,
{
    /// Maps the base monad while changing its contained type.
    pub fn fmap<B, F>(&self, f: F) -> ReaderT<E, M::Output<B>, B>
    where
        F: Fn(A) -> B + Clone + Send + Sync + 'static,
        B: Clone + 'static,
        M::Output<B>: 'static,
    {
        let run = Arc::clone(&self.run_reader_fn);
        ReaderT::new(move |env| {
            let mapper = f.clone();
            run(env).fmap(move |value| mapper(value.clone()))
        })
    }

    /// Sequences computations in the same base-monad family.
    pub fn bind<B, F>(&self, f: F) -> ReaderT<E, M::Output<B>, B>
    where
        F: Fn(A) -> ReaderT<E, M::Output<B>, B> + Clone + Send + Sync + 'static,
        B: Clone + 'static,
        M::Output<B>: 'static,
    {
        let run = Arc::clone(&self.run_reader_fn);
        ReaderT::new(move |env: E| {
            let next_env = env.clone();
            let next = f.clone();
            run(env).bind(move |value| next(value.clone()).run_reader(next_env.clone()))
        })
    }

    /// Combines two readers that share an environment and monad family.
    pub fn combine<B, C, F>(
        &self, other: &ReaderT<E, M::Output<B>, B>, f: F,
    ) -> ReaderT<E, M::Output<C>, C>
    where
        M: HKT<Output<A> = M>,
        F: Fn(A, B) -> C + Clone + Send + Sync + 'static,
        B: Clone + 'static,
        C: Clone + 'static,
        M::Output<B>: Clone + 'static,
        M::Output<C>: 'static,
    {
        let left = Arc::clone(&self.run_reader_fn);
        let right = Arc::clone(&other.run_reader_fn);
        ReaderT::new(move |env: E| {
            let combine = f.clone();
            M::lift2(
                move |a: &A, b: &B| combine(a.clone(), b.clone()),
                &left(env.clone()),
                &right(env),
            )
        })
    }

    /// Applies a reader-held function to this reader's value.
    pub fn apply<B, Func>(
        &self, functions: &ReaderT<E, M::Output<Func>, Func>,
    ) -> ReaderT<E, M::Output<B>, B>
    where
        M: HKT<Output<A> = M>,
        Func: Fn(A) -> B + Clone + Send + Sync + 'static,
        B: Clone + 'static,
        M::Output<Func>: Clone + 'static,
        M::Output<B>: 'static,
    {
        self.combine(functions, |value, function| function(value))
    }
}

impl<E, Err, A> ReaderT<E, Result<A, Err>, A>
where
    E: Clone + 'static,
    Err: Clone + 'static,
    A: Clone + 'static,
{
    pub fn try_run_reader(&self, env: E) -> ComposableResult<A, Err> {
        self.run_reader(env).map_err(ComposableError::new)
    }

    pub fn try_run_reader_with_context<C>(&self, env: E, context: C) -> ComposableResult<A, Err>
    where
        C: IntoErrorContext,
    {
        let context = context.into_error_context();
        self.run_reader(env)
            .map_err(|error| ComposableError::new(error).with_context(context.clone()))
    }

    pub fn map_error<F, Err2>(&self, f: F) -> ReaderT<E, Result<A, Err2>, A>
    where
        F: Fn(Err) -> Err2 + Send + Sync + 'static,
        Err2: Clone + 'static,
    {
        let run = Arc::clone(&self.run_reader_fn);
        ReaderT::new(move |env| run(env).map_err(&f))
    }
}

impl<E, M, A> MonadTransformer for ReaderT<E, M, A>
where
    E: Clone + 'static,
    M: Monad<Source = A> + Send + Sync + Clone + 'static,
    A: Clone + 'static,
{
    type BaseMonad = M;

    fn lift(base: M) -> Self {
        ReaderT::new(move |_| base.clone())
    }
}

#[cfg(test)]
mod tests {
    use super::ReaderT;

    #[test]
    fn type_changing_operations_use_the_hkt_output() {
        type Formatter = fn(i32) -> String;
        type FunctionReader = ReaderT<i32, Option<Formatter>, Formatter>;

        let value: ReaderT<i32, Option<i32>, i32> = ReaderT::new(Some);
        let mapped: ReaderT<i32, Option<String>, String> = value.fmap(|n| n.to_string());
        assert_eq!(mapped.run_reader(7), Some("7".to_owned()));

        let bound: ReaderT<i32, Option<String>, String> =
            value.bind(|n| ReaderT::new(move |env| Some(format!("{env}:{n}"))));
        assert_eq!(bound.run_reader(7), Some("7:7".to_owned()));

        let suffix: ReaderT<i32, Option<&'static str>, &'static str> = ReaderT::new(|_| Some("!"));
        let combined: ReaderT<i32, Option<String>, String> =
            value.combine(&suffix, |n, suffix| format!("{n}{suffix}"));
        assert_eq!(combined.run_reader(7), Some("7!".to_owned()));

        let functions: FunctionReader =
            ReaderT::new(|_| Some((|n| format!("value={n}")) as Formatter));
        let applied: ReaderT<i32, Option<String>, String> = value.apply(&functions);
        assert_eq!(applied.run_reader(7), Some("value=7".to_owned()));
    }
}

#[cfg(miri)]
mod miri_tests {
    use super::ReaderT;

    #[test]
    fn bind_owns_strings_without_aliasing_or_double_drop() {
        let reader: ReaderT<(), Option<String>, String> =
            ReaderT::new(|()| Some(String::from("owned")));
        let bound: ReaderT<(), Option<String>, String> =
            reader.bind(|value| ReaderT::new(move |()| Some(format!("{value}-next"))));
        assert_eq!(bound.run_reader(()), Some(String::from("owned-next")));
    }
}
