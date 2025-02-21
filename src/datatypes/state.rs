use crate::traits::hkt::{HKT, TypeConstraints};
use crate::traits::functor::Functor;
use crate::traits::applicative::Applicative;
use crate::traits::monad::Monad;
use crate::traits::pure::Pure;
use crate::traits::category::Category;
use crate::traits::arrow::Arrow;
use crate::traits::composable::Composable;
use crate::traits::identity::Identity;
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
/// use rustica::datatypes::state::State;
/// use rustica::fntype::{FnType, FnTrait};
///
/// let state = State::new(FnType::new(|s: i32| (s + 1, s * 2)));
/// assert_eq!(state.run_state(5), (6, 10));
/// ```
#[derive(Clone, Debug, PartialEq, Eq, Default)]
pub struct State<S: TypeConstraints, A: TypeConstraints> {
    /// The stateful computation function that takes a state `S` and returns a tuple `(A, S)`.
    /// `A` is the result of the computation, and `S` is the new state.
    pub run: FnType<S, (A, S)>,
}

impl<S: TypeConstraints, A: TypeConstraints> State<S, A> {
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
    /// use rustica::datatypes::state::State;
    /// use rustica::fntype::{FnType, FnTrait};
    ///
    /// let state = State::new(FnType::new(|s: i32| (s + 1, s * 2)));
    /// assert_eq!(state.run_state(5), (6, 10));
    /// ```
    pub fn new<F: FnTrait<S, (A, S)>>(f: F) -> Self {
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
    /// use rustica::datatypes::state::State;
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
    /// use rustica::datatypes::state::State;
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

impl<S: TypeConstraints, A: TypeConstraints> HKT for State<S, A> {
    type Output<T> = State<S, T> where T: TypeConstraints;
}

impl<S: TypeConstraints, A: TypeConstraints> Pure<A> for State<S, A> {
    fn pure(value: A) -> Self::Output<A> {
        State::new(FnType::new(move |s| (value.clone(), s)))
    }
}

impl<S: TypeConstraints, A: TypeConstraints> Functor<A> for State<S, A> {
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

impl<S: TypeConstraints, A: TypeConstraints> Applicative<A> for State<S, A> {
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

impl<S: TypeConstraints, A: TypeConstraints> Monad<A> for State<S, A> {
    fn bind<B, F>(self, f: F) -> Self::Output<B>
    where
        B: TypeConstraints,
        F: FnTrait<A, Self::Output<B>>,
    {
        State::new(FnType::new(move |s: S| {
            let (a, s1) = self.run_state(s);
            f.call(a).run_state(s1)
        }))
    }

    fn join<B>(self) -> Self::Output<B>
    where
        B: TypeConstraints,
        A: Into<Self::Output<B>>,
    {
        State::new(FnType::new(move |s: S| {
            let (ma, s1) = self.run_state(s);
            ma.into().run_state(s1)
        }))
    }

    fn then<B: TypeConstraints>(self, mb: Self::Output<B>) -> Self::Output<B> {
        self.bind(FnType::new(move |_| mb.clone()))
    }

    fn returns<B, F>(self, f: F) -> Self::Output<B>
    where
        B: TypeConstraints,
        F: FnTrait<A, B>,
    {
        State::new(FnType::new(move |s: S| {
            let (a, s1) = self.run_state(s);
            (f.call(a), s1)
        }))
    }
}

impl<S: TypeConstraints, A: TypeConstraints> Identity<A> for State<S, A> {
    fn map_identity<B, F>(f: F) -> Self::Output<B>
    where
        B: TypeConstraints,
        F: FnTrait<A, B>,
    {
        State::new(FnType::new(move |s| (f.call(A::default()), s)))
    }
}

impl<S: TypeConstraints, A: TypeConstraints> Composable<A> for State<S, A> {
    fn compose_with<B, F>(self, f: F) -> Self::Output<B>
    where
        B: TypeConstraints,
        F: FnTrait<A, B>,
    {
        State::new(FnType::new(move |s| {
            let (a, s1) = self.run_state(s);
            (f.call(a), s1)
        }))
    }
}

impl<S: TypeConstraints, A: TypeConstraints> Category<A> for State<S, A> {
    type Morphism<B, C> = FnType<B, C> where B: TypeConstraints, C: TypeConstraints;
}

impl<S: TypeConstraints, A: TypeConstraints> Arrow<A, A> for State<S, A> {}

/// Creates a stateful computation that returns the current state.
///
/// # Examples
/// ```
/// use rustica::datatypes::state::{State, get};
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
/// use rustica::datatypes::state::{State, put};
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
/// use rustica::datatypes::state::{State, modify};
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