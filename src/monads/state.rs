use std::fmt::Debug;

use crate::category::{Applicative, Functor, HKT, Monad, Pure, ReturnTypeConstraints};
use crate::fntype::{SendSyncFn, SendSyncFnTrait, ApplyFn, MonadFn};

/// A state monad that represents a computation with access to mutable state.
#[derive(Clone)]
pub struct State<S, A>
where
    S: ReturnTypeConstraints,
    A: ReturnTypeConstraints,
{
    /// The function that transforms the state and produces a value.
    run: SendSyncFn<S, (A, S)>,
}

impl<S, A> Debug for State<S, A>
where
    S: ReturnTypeConstraints,
    A: ReturnTypeConstraints,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("State")
            .field("run", &"<function>")
            .finish()
    }
}

impl<S, A> Default for State<S, A>
where
    S: ReturnTypeConstraints,
    A: ReturnTypeConstraints,
{
    fn default() -> Self {
        State {
            run: SendSyncFn::default(),
        }
    }
}

impl<S, A> PartialEq for State<S, A>
where
    S: ReturnTypeConstraints,
    A: ReturnTypeConstraints,
{
    fn eq(&self, other: &Self) -> bool {
        self.run == other.run
    }
}

impl<S, A> Eq for State<S, A>
where
    S: ReturnTypeConstraints,
    A: ReturnTypeConstraints,
{}

impl<S, A> State<S, A>
where
    S: ReturnTypeConstraints,
    A: ReturnTypeConstraints,
{
    /// Creates a new state computation.
    pub fn new<F>(f: F) -> Self
    where
        F: SendSyncFnTrait<S, (A, S)>,
    {
        State {
            run: SendSyncFn::new(move |s| f.call(s)),
        }
    }

    /// Runs the state computation with the given initial state.
    pub fn run_state(&self, s: S) -> (A, S) {
        self.run.call(s)
    }

    /// Gets the value from the state computation.
    pub fn eval_state(&self, s: S) -> A {
        let (a, _) = self.run_state(s);
        a
    }

    /// Gets the final state from the state computation.
    pub fn exec_state(&self, s: S) -> S {
        let (_, s) = self.run_state(s);
        s
    }
}

impl<S, A> HKT for State<S, A>
where
    S: ReturnTypeConstraints,
    A: ReturnTypeConstraints,
{
    type Output<T> = State<S, T> where T: ReturnTypeConstraints;
}

impl<S, A> Pure<A> for State<S, A>
where
    S: ReturnTypeConstraints,
    A: ReturnTypeConstraints,
{
    fn pure(value: A) -> Self::Output<A> {
        let value = value.clone();
        State::new(SendSyncFn::new(move |s| (value.clone(), s)))
    }
}

impl<S, A> Functor<A> for State<S, A>
where
    S: ReturnTypeConstraints,
    A: ReturnTypeConstraints,
{
    fn map<B, F>(self, f: F) -> Self::Output<B>
    where
        B: ReturnTypeConstraints,
        F: SendSyncFnTrait<A, B>,
    {
        let f = SendSyncFn::new(move |s| {
            let (a, s) = self.run_state(s);
            (f.call(a), s)
        });
        State { run: f }
    }
}

impl<S, A> Applicative<A> for State<S, A>
where
    S: ReturnTypeConstraints,
    A: ReturnTypeConstraints,
{
    fn apply<B, F>(self, mf: Self::Output<F>) -> Self::Output<B>
    where
        B: ReturnTypeConstraints,
        F: ApplyFn<A, B> + Default,
    {
        let f = SendSyncFn::new(move |s: S| {
            let (f, s) = mf.run_state(s.clone());
            let (a, s) = self.run_state(s);
            (f.call(a), s)
        });
        State { run: f }
    }

    fn lift2<B, C, F>(self, mb: Self::Output<B>, f: F) -> Self::Output<C>
    where
        B: ReturnTypeConstraints,
        C: ReturnTypeConstraints,
        F: ApplyFn<A, SendSyncFn<B, C>>,
    {
        let f = SendSyncFn::new(move |s: S| {
            let (a, s) = self.run_state(s.clone());
            let (b, s) = mb.run_state(s);
            (f.call(a).call(b), s)
        });
        State { run: f }
    }

    fn lift3<B, C, D, F>(self, mb: Self::Output<B>, mc: Self::Output<C>, f: F) -> Self::Output<D>
    where
        B: ReturnTypeConstraints,
        C: ReturnTypeConstraints,
        D: ReturnTypeConstraints,
        F: ApplyFn<A, SendSyncFn<B, SendSyncFn<C, D>>>,
    {
        let f = SendSyncFn::new(move |s: S| {
            let (a, s) = self.run_state(s.clone());
            let (b, s) = mb.run_state(s.clone());
            let (c, s) = mc.run_state(s);
            (f.call(a).call(b).call(c), s)
        });
        State { run: f }
    }
}

impl<S, A> Monad<A> for State<S, A>
where
    S: ReturnTypeConstraints,
    A: ReturnTypeConstraints,
{
    fn bind<B, F>(self, f: F) -> Self::Output<B>
    where
        B: ReturnTypeConstraints,
        F: SendSyncFnTrait<A, Self::Output<B>>,
    {
        let f = SendSyncFn::new(move |s: S| {
            let (a, s) = self.run_state(s.clone());
            f.call(a).run_state(s)
        });
        State { run: f }
    }

    fn join<B>(self) -> Self::Output<B>
    where
        B: ReturnTypeConstraints,
        A: Into<Self::Output<B>>,
    {
        let f = SendSyncFn::new(move |s: S| {
            let (inner, s) = self.run_state(s.clone());
            inner.into().run_state(s)
        });
        State { run: f }
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

/// Gets the current state.
pub fn get<S>() -> State<S, S>
where
    S: ReturnTypeConstraints,
{
    State::new(SendSyncFn::new(|s: S| (s.clone(), s)))
}

/// Sets the state.
pub fn put<S>(s: S) -> State<S, ()>
where
    S: ReturnTypeConstraints,
{
    State::new(SendSyncFn::new(move |_| ((), s.clone())))
}

/// Modifies the state.
pub fn modify<S, F>(f: F) -> State<S, ()>
where
    S: ReturnTypeConstraints,
    F: SendSyncFnTrait<S, S>,
{
    State::new(SendSyncFn::new(move |s| ((), f.call(s))))
}