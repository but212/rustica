use crate::category::hkt::{HKT, TypeConstraints};
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
    S: TypeConstraints,
    A: TypeConstraints,
{
    /// The stateful computation function that takes a state `S` and returns a tuple `(A, S)`.
    /// `A` is the result of the computation, and `S` is the new state.
    pub run: FnType<S, (A, S)>,
}

impl<S, A> State<S, A>
where
    S: TypeConstraints,
    A: TypeConstraints,
{
    /// Creates a new `State` instance with the given state transition function.
    ///
    /// # Arguments
    ///
    /// * `f` - A function that takes the current state and returns a tuple of (result, new state).
    ///
    /// # Returns
    ///
    /// A new `State` instance encapsulating the given state transition function.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::monads::state::State;
    /// use rustica::fntype::{FnType, FnTrait};
    ///
    /// let state = State::new(FnType::new(|s: i32| (s + 1, s * 2)));
    /// assert_eq!(state.run_state(5), (6, 10));
    /// ```
    pub fn new<F>(f: F) -> Self
    where
        F: FnTrait<S, (A, S)>,
    {
        State { run: FnType::new(move |s| f.call(s)) }
    }

    /// Runs the state computation with the given initial state.
    ///
    /// # Arguments
    ///
    /// * `s` - The initial state.
    ///
    /// # Returns
    ///
    /// A tuple containing the result of the computation and the final state.
    pub fn run_state(&self, s: S) -> (A, S) {
        self.run.call(s)
    }

    /// Evaluates the state computation with the given initial state and returns only the result.
    ///
    /// This function runs the state computation but discards the final state,
    /// returning only the result of the computation.
    ///
    /// # Arguments
    ///
    /// * `s` - The initial state.
    ///
    /// # Returns
    ///
    /// The result of the computation.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::monads::state::State;
    /// use rustica::fntype::{FnType, FnTrait};
    ///
    /// let state = State::new(FnType::new(|s: i32| (s + 1, s * 2)));
    /// assert_eq!(state.eval_state(5), 6);
    /// ```
    pub fn eval_state(&self, s: S) -> A {
        let (a, _) = self.run_state(s);
        a
    }

    /// Executes the state computation with the given initial state and returns only the final state.
    ///
    /// This function runs the state computation but discards the result,
    /// returning only the final state.
    ///
    /// # Arguments
    ///
    /// * `s` - The initial state.
    ///
    /// # Returns
    ///
    /// The final state after running the computation.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::monads::state::State;
    /// use rustica::fntype::{FnType, FnTrait};
    ///
    /// let state = State::new(FnType::new(|s: i32| (s + 1, s * 2)));
    /// assert_eq!(state.exec_state(5), 10);
    /// ```
    pub fn exec_state(&self, s: S) -> S {
        let (_, s) = self.run_state(s);
        s
    }
}

impl<S, A> HKT for State<S, A>
where
    S: TypeConstraints,
    A: TypeConstraints,
{
    type Output<T> = State<S, T> where T: TypeConstraints;
}

impl<S, A> Pure<A> for State<S, A>
where
    S: TypeConstraints,
    A: TypeConstraints,
{
    fn pure(value: A) -> Self::Output<A> {
        State::new(FnType::new(move |s| (value.clone(), s)))
    }
}

impl<S, A> Functor<A> for State<S, A>
where
    S: TypeConstraints,
    A: TypeConstraints,
{
    fn fmap<B, F>(self, f: F) -> Self::Output<B>
    where
        B: TypeConstraints,
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
    S: TypeConstraints,
    A: TypeConstraints,
{
    fn apply<B, F>(self, mf: Self::Output<F>) -> Self::Output<B>
    where
        B: TypeConstraints,
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
        B: TypeConstraints,
        C: TypeConstraints,
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
        B: TypeConstraints,
        C: TypeConstraints,
        D: TypeConstraints,
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
    S: TypeConstraints,
    A: TypeConstraints,
{
    fn bind<B, F>(self, f: F) -> Self::Output<B>
    where
        B: TypeConstraints,
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
        B: TypeConstraints,
        A: Into<Self::Output<B>>,
    {
        self.bind(FnType::new(move |inner: A| inner.into()))
    }

    fn kleisli_compose<B, C, G, H>(g: G, h: H) -> FnType<A, Self::Output<C>>
    where
        B: TypeConstraints,
        C: TypeConstraints,
        G: FnTrait<A, Self::Output<B>>,
        H: FnTrait<B, Self::Output<C>>,
    {
        FnType::new(move |x| {
            g.call(x).bind(h.clone())
        })
    }
}

impl<S: TypeConstraints, A: TypeConstraints> Identity for State<S, A> {}

impl<S: TypeConstraints, A: TypeConstraints> Composable for State<S, A> {}

impl<S: TypeConstraints, A: TypeConstraints> Category for State<S, A>
where
    S: TypeConstraints,
    A: TypeConstraints,
{
    type Morphism<B, C> = FnType<B, C>
    where
        B: TypeConstraints,
        C: TypeConstraints;
}

impl<S: TypeConstraints, A: TypeConstraints> Arrow for State<S, A> {}

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
    S: TypeConstraints,
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
    S: TypeConstraints,
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
    S: TypeConstraints,
    F: FnTrait<S, S>,
{
    State::new(FnType::new(move |s| ((), f.call(s))))
}