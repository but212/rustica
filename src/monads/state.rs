use crate::category::hkt::{HKT, ReturnTypeConstraints};
use crate::category::functor::Functor;
use crate::category::applicative::Applicative;
use crate::category::monad::Monad;
use crate::category::pure::Pure;
use crate::category::category::Category;
use crate::category::arrow::Arrow;
use crate::category::composable::Composable;
use crate::category::identity::Identity;
use crate::fntype::{FnType, FnTrait};

/// State struct representing a stateful computation.
///
/// # Type Parameters
/// * `S` - The state type.
/// * `A` - The output type.
///
/// # Laws
/// A State instance must satisfy these laws in addition to the standard Monad laws:
/// 1. Get-Put Identity: For any state `s`,
///    `get().bind(|x| put(x)).run_state(s) = ((), s)`
/// 2. Put-Get Identity: For any state `s`,
///    `put(s).bind(|_| get()).run_state(_) = (s, s)`
/// 3. State Independence: For any value `x` and state `s`,
///    `pure(x).run_state(s) = (x, s)`
/// 4. Modify Consistency: For function `f`,
///    `modify(f).run_state(s) = ((), f(s))`
///
/// # Examples
/// ```
/// use rustica::monads::state::State;
/// use rustica::fntype::{FnType, FnTrait};
///
/// let state = State::new(FnType::new(|s: i32| (s + 1, s * 2)));
/// assert_eq!(state.run_state(5), (6, 10));
/// ```
#[derive(Clone, Debug, PartialEq, Eq, Default)]
pub struct State<S, A>
where
    S: ReturnTypeConstraints,
    A: ReturnTypeConstraints,
{
    pub run: FnType<S, (A, S)>,
}

impl<S, A> State<S, A>
where
    S: ReturnTypeConstraints,
    A: ReturnTypeConstraints,
{
    pub fn new<F>(f: F) -> Self
    where
        F: FnTrait<S, (A, S)>,
    {
        State { run: FnType::new(move |s| f.call(s)) }
    }

    pub fn run_state(&self, s: S) -> (A, S) {
        self.run.call(s)
    }

    pub fn eval_state(&self, s: S) -> A {
        let (a, _) = self.run_state(s);
        a
    }

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
        State::new(FnType::new(move |s| (value.clone(), s)))
    }
}

impl<S, A> Functor<A> for State<S, A>
where
    S: ReturnTypeConstraints,
    A: ReturnTypeConstraints,
{
    fn fmap<B, F>(self, f: F) -> Self::Output<B>
    where
        B: ReturnTypeConstraints,
        F: FnTrait<A, B>,
    {
        let f = FnType::new(move |s| {
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
        F: FnTrait<A, B>,
    {
        let f = FnType::new(move |s: S| {
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
        F: FnTrait<(A, B), C>,
    {
        let f = FnType::new(move |s: S| {
            let (a, s) = self.run_state(s.clone());
            let (b, s) = mb.run_state(s);
            (f.call((a, b)), s)
        });
        State { run: f }
    }

    fn lift3<B, C, D, F>(self, mb: Self::Output<B>, mc: Self::Output<C>, f: F) -> Self::Output<D>
    where
        B: ReturnTypeConstraints,
        C: ReturnTypeConstraints,
        D: ReturnTypeConstraints,
        F: FnTrait<(A, B, C), D>,
    {
        let f = FnType::new(move |s: S| {
            let (a, s) = self.run_state(s.clone());
            let (b, s) = mb.run_state(s.clone());
            let (c, s) = mc.run_state(s);
            (f.call((a, b, c)), s)
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
        F: FnTrait<A, Self::Output<B>>,
    {
        let f = FnType::new(move |s: S| {
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
        self.bind(FnType::new(move |inner: A| inner.into()))
    }

    fn kleisli_compose<B, C, G, H>(g: G, h: H) -> FnType<A, Self::Output<C>>
    where
        B: ReturnTypeConstraints,
        C: ReturnTypeConstraints,
        G: FnTrait<A, Self::Output<B>>,
        H: FnTrait<B, Self::Output<C>>,
    {
        FnType::new(move |x| {
            g.call(x).bind(h.clone())
        })
    }
}

impl<S: ReturnTypeConstraints, A: ReturnTypeConstraints> Identity for State<S, A> {}

impl<S: ReturnTypeConstraints, A: ReturnTypeConstraints> Composable for State<S, A> {}

impl<S: ReturnTypeConstraints, A: ReturnTypeConstraints> Category for State<S, A>
where
    S: ReturnTypeConstraints,
    A: ReturnTypeConstraints,
{
    type Morphism<B, C> = FnType<B, C>
    where
        B: ReturnTypeConstraints,
        C: ReturnTypeConstraints;
}

impl<S: ReturnTypeConstraints, A: ReturnTypeConstraints> Arrow for State<S, A> {}

/// Creates a stateful computation that returns the current state.
///
/// # Examples
/// ```
/// use rustica::monads::state::{State, get};
///
/// let state = get::<i32>();
/// assert_eq!(state.run_state(5), (5, 5));
/// ```
pub fn get<S>() -> State<S, S>
where
    S: ReturnTypeConstraints,
{
    State::new(FnType::new(|s: S| (s.clone(), s)))
}

/// Creates a stateful computation that updates the state and returns ().
///
/// # Examples
/// ```
/// use rustica::monads::state::{State, put};
///
/// let state = put(10);
/// assert_eq!(state.run_state(5), ((), 10));
/// ```
pub fn put<S>(s: S) -> State<S, ()>
where
    S: ReturnTypeConstraints,
{
    State::new(FnType::new(move |_| ((), s.clone())))
}

/// Creates a stateful computation that modifies the state using a function and returns ().
///
/// # Examples
/// ```
/// use rustica::monads::state::{State, modify};
/// use rustica::fntype::{FnType, FnTrait};
///
/// let state = modify(FnType::new(|x: i32| x * 2));
/// assert_eq!(state.run_state(5), ((), 10));
/// ```
pub fn modify<S, F>(f: F) -> State<S, ()>
where
    S: ReturnTypeConstraints,
    F: FnTrait<S, S>,
{
    State::new(FnType::new(move |s| ((), f.call(s))))
}