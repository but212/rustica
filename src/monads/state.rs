use crate::category::hkt::{HKT, ReturnTypeConstraints};
use crate::category::functor::Functor;
use crate::category::applicative::Applicative;
use crate::category::monad::Monad;
use crate::category::pure::Pure;
use crate::fntype::{SendSyncFn, SendSyncFnTrait, MonadFn, ApplyFn};

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
/// 3. Get-Get Identity: For any state `s`,
///    `get().bind(|x| get().bind(|y| pure((x,y)))).run_state(s) = ((s,s), s)`
/// 4. Put-Put Identity: For states `s1`, `s2`,
///    `put(s1).bind(|_| put(s2)).run_state(_) = ((), s2)`
/// 5. State Independence: For any value `x` and state `s`,
///    `pure(x).run_state(s) = (x, s)`
/// 6. State Threading: For state computations `m1`, `m2`,
///    `m1.bind(m2).run_state(s)` must thread state from `m1` to `m2`
/// 7. Modify Consistency: For function `f`,
///    `modify(f).run_state(s) = ((), f(s))`
/// 8. Evaluation Consistency: For state computation `m` and state `s`,
///    `m.eval_state(s) = fst(m.run_state(s))`
#[derive(Clone, Default, Eq, PartialEq, Debug)]
pub struct State<S, A>
where
    S: ReturnTypeConstraints,
    A: ReturnTypeConstraints,
{
    /// Function that runs the stateful computation.
    pub run: SendSyncFn<S, (A, S)>,
}

impl<S, A> State<S, A>
where
    S: ReturnTypeConstraints,
    A: ReturnTypeConstraints,
{
    /// Creates a new State instance.
    /// 
    /// # Arguments
    /// * `f` - The function to be called.
    ///
    /// # Returns
    /// * `Self` - The new State instance.
    pub fn new<F>(f: F) -> Self
    where
        F: SendSyncFnTrait<S, (A, S)>,
    {
        State { run: SendSyncFn::new(move |s| f.call(s)) }
    }

    /// Runs the stateful computation and returns the result and the new state.
    ///
    /// # Arguments
    /// * `s` - The initial state.
    ///
    /// # Returns
    /// * `(A, S)` - The result and the new state.
    pub fn run_state(&self, s: S) -> (A, S) {
        self.run.call(s)
    }

    /// Evaluates the stateful computation and returns the result, discarding the new state.
    /// 
    /// # Arguments
    /// * `s` - The initial state.
    /// 
    /// # Returns
    /// * `A` - The result.
    pub fn eval_state(&self, s: S) -> A {
        let (a, _) = self.run_state(s);
        a
    }

    /// Executes the stateful computation and returns the new state, discarding the result.
    /// 
    /// # Arguments
    /// * `s` - The initial state.
    /// 
    /// # Returns
    /// * `S` - The new state.
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
    /// Creates a stateful computation that produces a pure value.
    /// 
    /// # Arguments
    /// * `value` - The value to be produced.
    /// 
    /// # Returns
    /// * `State<S, A>` - The new stateful computation.
    fn pure(value: A) -> Self::Output<A> {
        State::new(SendSyncFn::new(move |s| (value.clone(), s)))
    }
}

impl<S, A> Functor<A> for State<S, A>
where
    S: ReturnTypeConstraints,
    A: ReturnTypeConstraints,
{
    /// Maps a function over the output of a stateful computation.
    /// 
    /// # Arguments
    /// * `f` - The function to map with.
    /// 
    /// # Returns
    /// * `State<S, B>` - The new stateful computation.
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
    /// Applies a function wrapped in an Applicative computation to the result of another Applicative computation.
    /// 
    /// # Arguments
    /// * `mf` - The function to apply.
    /// 
    /// # Returns
    /// * `State<S, B>` - The applied value.
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

    /// Lifts a binary function into State computations.
    /// 
    /// # Arguments
    /// * `mb` - The second argument to the function.
    /// * `f` - The function to lift.
    /// 
    /// # Returns
    /// * `State<S, C>` - The new stateful computation.
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

    /// Lifts a ternary function into State computations.
    /// 
    /// # Arguments
    /// * `mb` - The second argument to the function.
    /// * `mc` - The third argument to the function.
    /// * `f` - The function to lift.
    /// 
    /// # Returns
    /// * `State<S, D>` - The new stateful computation.
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
    /// Binds a function over the output of a stateful computation.
    /// 
    /// # Arguments
    /// * `f` - The function to bind.
    /// 
    /// # Returns
    /// * `State<S, B>` - The new stateful computation.
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

    /// Joins a stateful computation by returning the inner value.
    /// 
    /// # Returns
    /// * `State<S, B>` - The inner value.
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

    /// Composes two stateful computations.
    /// 
    /// # Type Parameters
    /// * `B` - The type of the first argument.
    /// * `C` - The type of the second argument.
    /// * `G` - The type of the first function.
    /// * `H` - The type of the second function.
    /// 
    /// # Returns
    /// * `SendSyncFn<A, Self::Output<C>>` - The composed function.
    fn kleisli_compose<B, C, G, H>(g: G, h: H) -> SendSyncFn<A, Self::Output<C>>
    where
        B: ReturnTypeConstraints,
        C: ReturnTypeConstraints,
        G: MonadFn<A, B, Self::Output<B>>,
        H: MonadFn<B, C, Self::Output<C>>,
    {
        SendSyncFn::new(move |x| {
            g.call(x).bind(h.clone())
        })
    }
}

/// Creates a stateful computation that returns the current state.
/// 
/// # Type Parameters
/// * `S` - The state type.
/// 
/// # Returns
/// * `State<S, S>` - The stateful computation.
pub fn get<S>() -> State<S, S>
where
    S: ReturnTypeConstraints,
{
    State::new(SendSyncFn::new(|s: S| (s.clone(), s)))
}

/// Creates a stateful computation that updates the state and returns ().
/// 
/// # Type Parameters
/// * `S` - The state type.
/// 
/// # Arguments
/// * `s` - The new state.
/// 
/// # Returns
/// * `State<S, ()>` - The stateful computation.
pub fn put<S>(s: S) -> State<S, ()>
where
    S: ReturnTypeConstraints,
{
    State::new(SendSyncFn::new(move |_| ((), s.clone())))
}

/// Creates a stateful computation that modifies the state using a function and returns ().
/// 
/// # Type Parameters
/// * `S` - The state type.
/// * `F` - The function type.
/// 
/// # Arguments
/// * `f` - The function to modify the state with.
/// 
/// # Returns
/// * `State<S, ()>` - The stateful computation.
pub fn modify<S, F>(f: F) -> State<S, ()>
where
    S: ReturnTypeConstraints,
    F: SendSyncFnTrait<S, S>,
{
    State::new(SendSyncFn::new(move |s| ((), f.call(s))))
}