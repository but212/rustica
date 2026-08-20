//! State monad transformer.
//!
//! The only representable state is an executable transition `S -> M`, where
//! the base monad contains the canonical `(S, A)` pair.

use super::MonadTransformer;
use crate::datatypes::id::Id;
use crate::error::{ComposableError, ComposableResult, IntoErrorContext};
use crate::traits::functor::Functor;
use crate::traits::hkt::HKT;
use crate::traits::monad::Monad;
use std::marker::PhantomData;
use std::sync::Arc;

type StateRun<S, M> = dyn Fn(S) -> M + Send + Sync;

/// Maps the state/value pair while preserving the state component.
pub type StateValueMapper<S, A, B> = dyn Fn((S, A)) -> (S, B) + Send + Sync;

/// A state transition whose base monad contains `(state, value)`.
pub struct StateT<S, M, A>
where
    M: HKT<Source = (S, A)>,
{
    run_state_fn: Arc<StateRun<S, M>>,
    _value: PhantomData<A>,
}

impl<S, M, A> Clone for StateT<S, M, A>
where
    M: HKT<Source = (S, A)>,
{
    fn clone(&self) -> Self {
        Self {
            run_state_fn: Arc::clone(&self.run_state_fn),
            _value: PhantomData,
        }
    }
}

impl<S, M, A> StateT<S, M, A>
where
    S: 'static,
    M: HKT<Source = (S, A)> + 'static,
    A: 'static,
{
    /// Creates an executable state transition.
    pub fn new<F>(f: F) -> Self
    where
        F: Fn(S) -> M + Send + Sync + 'static,
    {
        Self {
            run_state_fn: Arc::new(f),
            _value: PhantomData,
        }
    }

    /// Runs the transition with an initial state.
    #[inline]
    pub fn run_state(&self, state: S) -> M {
        (self.run_state_fn)(state)
    }

    /// Creates a transition that returns a value without changing state.
    pub fn pure<P>(value: A, pure_fn: P) -> Self
    where
        S: Send + Sync,
        A: Clone + Send + Sync,
        P: Fn((S, A)) -> M + Send + Sync + 'static,
    {
        Self::new(move |state| pure_fn((state, value.clone())))
    }

    /// Returns the current state as the value.
    pub fn get<P>(pure_fn: P) -> StateT<S, M::Output<(S, S)>, S>
    where
        S: Clone + Send + Sync,
        P: Fn((S, S)) -> M::Output<(S, S)> + Send + Sync + 'static,
        M::Output<(S, S)>: 'static,
    {
        StateT::new(move |state: S| pure_fn((state.clone(), state)))
    }

    /// Replaces the state and returns the previous state.
    pub fn put<P>(new_state: S, pure_fn: P) -> StateT<S, M::Output<(S, S)>, S>
    where
        S: Clone + Send + Sync,
        P: Fn((S, S)) -> M::Output<(S, S)> + Send + Sync + 'static,
        M::Output<(S, S)>: 'static,
    {
        StateT::new(move |old_state: S| pure_fn((new_state.clone(), old_state)))
    }

    /// Modifies the current state and returns unit.
    pub fn modify<F, P>(f: F, pure_fn: P) -> StateT<S, M::Output<(S, ())>, ()>
    where
        F: Fn(S) -> S + Send + Sync + 'static,
        P: Fn((S, ())) -> M::Output<(S, ())> + Send + Sync + 'static,
        M::Output<(S, ())>: 'static,
    {
        StateT::new(move |state| pure_fn((f(state), ())))
    }

    /// Maps with a caller-provided operation from the same HKT family.
    pub fn fmap_with<B, F, MapFn>(&self, f: F, map_fn: MapFn) -> StateT<S, M::Output<(S, B)>, B>
    where
        F: Fn(A) -> B + Clone + Send + Sync + 'static,
        MapFn: for<'a> Fn(M, &'a StateValueMapper<S, A, B>) -> M::Output<(S, B)>
            + Send
            + Sync
            + 'static,
        B: 'static,
        M::Output<(S, B)>: 'static,
    {
        let run = Arc::clone(&self.run_state_fn);
        StateT::new(move |state| {
            let mapper = f.clone();
            let map_pair = move |(next_state, value)| (next_state, mapper(value));
            map_fn(run(state), &map_pair)
        })
    }

    /// Binds with a caller-provided operation from the same HKT family.
    pub fn bind_with<B, F, BindFn>(&self, f: F, bind_fn: BindFn) -> StateT<S, M::Output<(S, B)>, B>
    where
        S: Clone + Send + Sync,
        A: Send + Sync,
        F: Fn(A) -> StateT<S, M::Output<(S, B)>, B> + Clone + Send + Sync + 'static,
        BindFn: for<'a> Fn(
                M,
                &'a (dyn Fn((S, A)) -> M::Output<(S, B)> + Send + Sync),
            ) -> M::Output<(S, B)>
            + Send
            + Sync
            + 'static,
        B: 'static,
        M::Output<(S, B)>: 'static,
    {
        let run = Arc::clone(&self.run_state_fn);
        StateT::new(move |state| {
            let next = f.clone();
            let binder = move |(next_state, value)| next(value).run_state(next_state);
            bind_fn(run(state), &binder)
        })
    }

    /// Combines transitions left-to-right with a caller-provided bind operation.
    pub fn combine_with<B, C, F, BindFn>(
        &self, other: &StateT<S, M::Output<(S, B)>, B>, f: F, bind_fn: BindFn,
    ) -> StateT<S, M::Output<(S, C)>, C>
    where
        S: Clone + Send + Sync,
        A: Clone + Send + Sync,
        B: Clone + Send + Sync + 'static,
        C: Clone + 'static,
        F: Fn(A, B) -> C + Clone + Send + Sync + 'static,
        BindFn: for<'a> Fn(
                M,
                &'a (dyn Fn((S, A)) -> M::Output<(S, C)> + Send + Sync),
            ) -> M::Output<(S, C)>
            + Send
            + Sync
            + 'static,
        M::Output<(S, B)>: Functor<Source = (S, B), Output<(S, C)> = M::Output<(S, C)>> + 'static,
        M::Output<(S, C)>: 'static,
    {
        let left = Arc::clone(&self.run_state_fn);
        let right = Arc::clone(&other.run_state_fn);
        StateT::new(move |state| {
            let right = Arc::clone(&right);
            let combine = f.clone();
            let binder = move |(next_state, left_value): (S, A)| {
                let combine = combine.clone();
                right(next_state).fmap(move |pair| {
                    let (final_state, right_value) = pair;
                    (
                        final_state.clone(),
                        combine(left_value.clone(), right_value.clone()),
                    )
                })
            };
            bind_fn(left(state), &binder)
        })
    }

    /// Runs a base-level flattening operation without introducing state variants.
    pub fn join<OuterM, JoinFn>(&self, join_fn: JoinFn) -> StateT<S, OuterM, A>
    where
        OuterM: HKT<Source = (S, A)> + 'static,
        JoinFn: Fn(M) -> OuterM + Send + Sync + 'static,
    {
        let run = Arc::clone(&self.run_state_fn);
        StateT::new(move |state| join_fn(run(state)))
    }

    /// Runs the transition and lets the caller project the base result.
    pub fn exec_state<F, B>(&self, state: S, extract: F) -> B
    where
        F: FnOnce(M) -> B,
    {
        extract(self.run_state(state))
    }
}

impl<S, M, A> StateT<S, M, A>
where
    S: Clone + 'static,
    M: Monad<Source = (S, A)> + Clone + 'static,
    A: Clone + 'static,
{
    /// Maps the value while preserving the produced state.
    pub fn fmap<B, F>(&self, f: F) -> StateT<S, M::Output<(S, B)>, B>
    where
        F: Fn(A) -> B + Clone + Send + Sync + 'static,
        B: Clone + 'static,
        M::Output<(S, B)>: 'static,
    {
        let run = Arc::clone(&self.run_state_fn);
        StateT::new(move |state| {
            let mapper = f.clone();
            run(state).fmap(move |pair| {
                let (next_state, value) = pair;
                (next_state.clone(), mapper(value.clone()))
            })
        })
    }

    /// Sequences transitions and threads the produced state into the next step.
    pub fn bind<B, F>(&self, f: F) -> StateT<S, M::Output<(S, B)>, B>
    where
        F: Fn(A) -> StateT<S, M::Output<(S, B)>, B> + Clone + Send + Sync + 'static,
        B: Clone + 'static,
        M::Output<(S, B)>: 'static,
    {
        let run = Arc::clone(&self.run_state_fn);
        StateT::new(move |state| {
            let next = f.clone();
            run(state).bind(move |pair| {
                let (next_state, value) = pair;
                next(value.clone()).run_state(next_state.clone())
            })
        })
    }

    /// Combines transitions left-to-right while threading state.
    pub fn combine<B, C, F>(
        &self, other: &StateT<S, M::Output<(S, B)>, B>, f: F,
    ) -> StateT<S, M::Output<(S, C)>, C>
    where
        B: Clone + 'static,
        C: Clone + 'static,
        F: Fn(A, B) -> C + Clone + Send + Sync + 'static,
        M::Output<(S, B)>: Functor<Source = (S, B), Output<(S, C)> = M::Output<(S, C)>> + 'static,
        M::Output<(S, C)>: 'static,
    {
        let left = Arc::clone(&self.run_state_fn);
        let right = Arc::clone(&other.run_state_fn);
        StateT::new(move |state| {
            let right = Arc::clone(&right);
            let combine = f.clone();
            left(state).bind(move |pair| {
                let (next_state, left_value) = pair;
                let combine = combine.clone();
                right(next_state.clone()).fmap(move |right_pair| {
                    let (final_state, right_value) = right_pair;
                    (
                        final_state.clone(),
                        combine(left_value.clone(), right_value.clone()),
                    )
                })
            })
        })
    }

    /// Applies a state-held function to the next state-held value.
    pub fn apply<B, C>(
        &self, other: &StateT<S, M::Output<(S, B)>, B>,
    ) -> StateT<S, M::Output<(S, C)>, C>
    where
        A: Fn(B) -> C,
        B: Clone + 'static,
        C: Clone + 'static,
        M::Output<(S, B)>: Functor<Source = (S, B), Output<(S, C)> = M::Output<(S, C)>> + 'static,
        M::Output<(S, C)>: 'static,
    {
        self.combine(other, |function, value| function(value))
    }
}

impl<S, M, A> MonadTransformer for StateT<S, M, A>
where
    S: Clone + Send + Sync + 'static,
    M: Monad<Source = (S, A)> + Clone + 'static,
    A: Clone + Send + Sync + 'static,
    M::Output<A>: Monad<Source = A> + HKT<Output<(S, A)> = M> + Clone + Send + Sync + 'static,
{
    type BaseMonad = M::Output<A>;

    fn lift(base: Self::BaseMonad) -> Self {
        StateT::new(move |state: S| base.fmap(|value| (state.clone(), value.clone())))
    }
}

impl<S, E, A> StateT<S, Result<(S, A), E>, A>
where
    S: Clone + 'static,
    E: Clone + 'static,
    A: Clone + 'static,
{
    pub fn try_run_state(&self, state: S) -> ComposableResult<(S, A), E> {
        self.run_state(state).map_err(ComposableError::new)
    }

    pub fn try_run_state_with_context<C>(&self, state: S, context: C) -> ComposableResult<(S, A), E>
    where
        C: IntoErrorContext,
    {
        let context = context.into_error_context();
        self.run_state(state)
            .map_err(|error| ComposableError::new(error).with_context(context.clone()))
    }

    pub fn map_error<F, E2>(&self, f: F) -> StateT<S, Result<(S, A), E2>, A>
    where
        F: Fn(E) -> E2 + Send + Sync + 'static,
        E2: Clone + 'static,
    {
        let run = Arc::clone(&self.run_state_fn);
        StateT::new(move |state| run(state).map_err(&f))
    }

    pub fn try_eval_state(&self, state: S) -> ComposableResult<A, E> {
        self.try_run_state(state).map(|(_, value)| value)
    }

    pub fn try_eval_state_with_context<C>(&self, state: S, context: C) -> ComposableResult<A, E>
    where
        C: IntoErrorContext,
    {
        self.try_run_state_with_context(state, context)
            .map(|(_, value)| value)
    }

    pub fn try_exec_state(&self, state: S) -> ComposableResult<S, E> {
        self.try_run_state(state)
            .map(|(final_state, _)| final_state)
    }
}

impl<S, A> StateT<S, Id<(S, A)>, A>
where
    S: Clone + Send + Sync + 'static,
    A: Clone + Send + Sync + 'static,
{
    /// Converts to `State`, preserving its public `(value, state)` result order.
    pub fn to_state(self) -> crate::datatypes::state::State<S, A> {
        self.into()
    }

    /// Converts from `State` into the canonical `(state, value)` transformer form.
    pub fn from_state(state: crate::datatypes::state::State<S, A>) -> Self {
        state.into()
    }
}

#[cfg(test)]
mod tests {
    use super::StateT;
    use crate::datatypes::state::State;
    use crate::transformers::MonadTransformer;

    #[test]
    fn type_changes_and_state_is_threaded_left_to_right() {
        type Formatter = fn(i32) -> String;
        type FunctionState = StateT<i32, Option<(i32, Formatter)>, Formatter>;

        let first: StateT<i32, Option<(i32, i32)>, i32> =
            StateT::new(|state| Some((state + 1, state)));
        let bound: StateT<i32, Option<(i32, String)>, String> = first
            .bind(|value| StateT::new(move |state| Some((state * 2, format!("{value}:{state}")))));
        assert_eq!(bound.run_state(3), Some((8, "3:4".to_owned())));

        let second: StateT<i32, Option<(i32, &'static str)>, &'static str> =
            StateT::new(|state| Some((state * 2, "done")));
        let combined = first.combine(&second, |value, label| format!("{value}:{label}"));
        assert_eq!(combined.run_state(3), Some((8, "3:done".to_owned())));

        let mapped: StateT<i32, Option<(i32, String)>, String> =
            first.fmap(|value| value.to_string());
        assert_eq!(mapped.run_state(3), Some((4, "3".to_owned())));

        let functions: FunctionState =
            StateT::new(|state| Some((state + 1, (|value| format!("value={value}")) as Formatter)));
        let values: StateT<i32, Option<(i32, i32)>, i32> =
            StateT::new(|state| Some((state * 2, state)));
        let applied: StateT<i32, Option<(i32, String)>, String> = functions.apply(&values);
        assert_eq!(applied.run_state(3), Some((8, "value=4".to_owned())));
    }

    #[test]
    fn lift_preserves_the_input_state() {
        let lifted: StateT<String, Option<(String, usize)>, usize> = StateT::lift(Some(7));
        assert_eq!(
            lifted.run_state("state".to_owned()),
            Some(("state".to_owned(), 7))
        );
    }

    #[test]
    fn state_round_trip_keeps_public_value_state_order() {
        let state: State<String, usize> = State::new(|current: String| {
            let value = current.len();
            (value, format!("{current}!"))
        });
        let transformed = StateT::from_state(state);
        assert_eq!(
            transformed.run_state("abc".to_owned()).unwrap(),
            ("abc!".to_owned(), 3)
        );

        let state_again = transformed.to_state();
        assert_eq!(
            state_again.run_state("rust".to_owned()),
            (4, "rust!".to_owned())
        );
    }
}
