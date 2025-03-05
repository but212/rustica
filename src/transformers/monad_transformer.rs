use crate::traits::enhanced_hkt::{EnhancedHKT, HKTApply, HKTBind, HKTLift};

pub trait MonadTransformer<M>: EnhancedHKT
where
    M: EnhancedHKT,
{
    /// Lifts a monad `M<A>` into the transformer `T<M<A>>`.
    fn lift<A>(m: M) -> Self
    where
        M: HKTApply<A>,
        Self: HKTApply<A>;

    /// Maps a function over the inner value.
    fn map<A, B, F>(self, f: F) -> <Self as HKTApply<B>>::Applied
    where
        F: FnOnce(A) -> B,
        Self: HKTApply<A> + HKTApply<B>;

    /// Binds a function that returns a transformed monad.
    fn bind<A, B, F>(self, f: F) -> <Self as HKTApply<B>>::Applied
    where
        F: FnOnce(A) -> <Self as HKTApply<B>>::Applied,
        Self: HKTApply<A> + HKTApply<B>;

    /// Runs the transformer, returning the inner monad.
    fn run<A>(self) -> M
    where
        Self: HKTApply<A>;
}

pub struct OptionT<M> {
    inner: M,
}

impl<M> OptionT<M> {
    /// Creates a new `OptionT` with the given inner monad.
    pub fn new(inner: M) -> Self {
        OptionT { inner }
    }

    /// Creates an `OptionT` with `Some` value.
    pub fn some<A, T>(value: A) -> Self
    where
        M: HKTLift,
        M: HKTApply<Option<A>, Applied = T>,
        T: Into<M>,
    {
        OptionT {
            inner: M::lift(Some(value)),
        }
    }

    /// Creates an `OptionT` with `None` value.
    pub fn none<A, T>() -> Self
    where
        M: HKTLift,
        M: HKTApply<Option<A>, Applied = T>,
        T: Into<M>,
    {
        OptionT {
            inner: M::lift(None),
        }
    }
}

impl<M, T> EnhancedHKT for OptionT<M>
where
    M: EnhancedHKT<Parameter = Option<T>>,
{
    type Parameter = T;
}

impl<M, T, U> HKTApply<U> for OptionT<M>
where
    M: EnhancedHKT<Parameter = Option<T>>,
    M: HKTApply<Option<U>>,
{
    type Applied = OptionT<M::Applied>;
}

impl<M, T> MonadTransformer<M> for OptionT<M>
where
    M: EnhancedHKT<Parameter = Option<T>>,
    M: HKTBind,
{
    fn lift<A>(m: M) -> Self
    where
        M: HKTApply<A>,
        Self: HKTApply<A>,
    {
        OptionT { inner: m }
    }

    fn map<A, B, F>(self, f: F) -> <Self as HKTApply<B>>::Applied
    where
        F: FnOnce(A) -> B + 'static,
        Self: HKTApply<A> + HKTApply<B>,
        M: HKTApply<Option<A>> + HKTApply<Option<B>> + HKTBind,
    {
        OptionT {
            inner: self.inner.bind(move |opt| {
                M::lift(opt.map(f))
            }),
        }
    }

    fn bind<A, B, F>(self, f: F) -> <Self as HKTApply<B>>::Applied
    where
        F: FnOnce(A) -> <Self as HKTApply<B>>::Applied + 'static,
        Self: HKTApply<A> + HKTApply<B>,
        M: HKTApply<Option<A>> + HKTApply<Option<B>> + HKTBind + HKTLift,
    {
        OptionT {
            inner: self.inner.bind(move |opt| {
                match opt {
                    Some(value) => {
                        let OptionT { inner } = f(value);
                        inner
                    }
                    None => M::lift(None),
                }
            }),
        }
    }

    fn run<A>(self) -> M
    where
        Self: HKTApply<A>,
    {
        self.inner
    }
}

pub struct ResultT<M> {
    inner: M,
}

impl<M> ResultT<M> {
    /// Creates a new `ResultT` with the given inner monad.
    pub fn new(inner: M) -> Self {
        ResultT { inner }
    }

    /// Creates a `ResultT` with `Ok` value.
    pub fn ok<A, E, T>(value: A) -> Self
    where
        M: HKTLift,
        M: HKTApply<Result<A, E>, Applied = T>,
        T: Into<M>,
    {
        ResultT {
            inner: M::lift(Ok(value)),
        }
    }

    /// Creates a `ResultT` with `Err` value.
    pub fn err<A, E, T>(error: E) -> Self
    where
        M: HKTLift,
        M: HKTApply<Result<A, E>, Applied = T>,
        T: Into<M>,
    {
        ResultT {
            inner: M::lift(Err(error)),
        }
    }
}

impl<M, T, E> EnhancedHKT for ResultT<M>
where
    M: EnhancedHKT<Parameter = Result<T, E>>,
{
    type Parameter = T;
}

impl<M, T, E, U> HKTApply<U> for ResultT<M>
where
    M: EnhancedHKT<Parameter = Result<T, E>>,
    M: HKTApply<Result<U, E>>,
{
    type Applied = ResultT<M::Applied>;
}

impl<M, T, E> MonadTransformer<M> for ResultT<M>
where
    M: EnhancedHKT<Parameter = Result<T, E>>,
    M: HKTBind,
    E: Clone + 'static,
{
    fn lift<A>(m: M) -> Self
    where
        M: HKTApply<A>,
        Self: HKTApply<A>,
    {
        ResultT { inner: m }
    }

    fn map<A, B, F>(self, f: F) -> <Self as HKTApply<B>>::Applied
    where
        F: FnOnce(A) -> B + 'static,
        Self: HKTApply<A> + HKTApply<B>,
        M: HKTApply<Result<A, E>> + HKTApply<Result<B, E>> + HKTBind,
    {
        ResultT {
            inner: self.inner.bind(move |res| {
                M::lift(res.map(f))
            }),
        }
    }

    fn bind<A, B, F>(self, f: F) -> <Self as HKTApply<B>>::Applied
    where
        F: FnOnce(A) -> <Self as HKTApply<B>>::Applied + 'static,
        Self: HKTApply<A> + HKTApply<B>,
        M: HKTApply<Result<A, E>> + HKTApply<Result<B, E>> + HKTBind + HKTLift,
    {
        ResultT {
            inner: self.inner.bind(move |res| {
                match res {
                    Ok(value) => {
                        let ResultT { inner } = f(value);
                        inner
                    }
                    Err(e) => M::lift(Err(e)),
                }
            }),
        }
    }

    fn run<A>(self) -> M
    where
        Self: HKTApply<A>,
    {
        self.inner
    }
}

pub struct StateT<M, S> {
    run_state: Box<dyn FnOnce(S) -> M>,
    _phantom: std::marker::PhantomData<S>,
}

impl<M, S> StateT<M, S> {
    /// Creates a new `StateT` with the given state transformation function.
    pub fn new<F>(f: F) -> Self
    where
        F: FnOnce(S) -> M + 'static,
    {
        StateT {
            run_state: Box::new(f),
            _phantom: std::marker::PhantomData,
        }
    }

    /// Runs the state transformation with the given initial state.
    pub fn run_state(self, s: S) -> M {
        (self.run_state)(s)
    }
}

impl<M, S, A> EnhancedHKT for StateT<M, S>
where
    M: EnhancedHKT<Parameter = (A, S)>,
{
    type Parameter = A;
}

impl<M, S, A, B> HKTApply<B> for StateT<M, S>
where
    M: EnhancedHKT<Parameter = (A, S)>,
    M: HKTApply<(B, S)>,
{
    type Applied = StateT<M::Applied, S>;
}

impl<M, S, A> MonadTransformer<M> for StateT<M, S>
where
    M: EnhancedHKT<Parameter = (A, S)>,
    M: HKTBind + HKTLift,
    S: Clone + 'static,
    A: 'static,
{
    fn lift<T>(m: M) -> Self
    where
        M: HKTApply<T>,
        Self: HKTApply<T>,
    {
        StateT::new(move |s| {
            m.bind(move |a| M::lift((a, s)))
        })
    }

    fn map<T, B, F>(self, f: F) -> <Self as HKTApply<B>>::Applied
    where
        F: FnOnce(T) -> B + 'static,
        Self: HKTApply<T> + HKTApply<B>,
        M: HKTApply<(T, S)> + HKTApply<(B, S)> + HKTBind,
    {
        StateT::new(move |s| {
            self.run_state(s).bind(move |(a, s)| {
                M::lift((f(a), s))
            })
        })
    }

    fn bind<T, B, F>(self, f: F) -> <Self as HKTApply<B>>::Applied
    where
        F: FnOnce(T) -> <Self as HKTApply<B>>::Applied + 'static,
        Self: HKTApply<T> + HKTApply<B>,
        M: HKTApply<(T, S)> + HKTApply<(B, S)> + HKTBind,
    {
        StateT::new(move |s| {
            self.run_state(s).bind(move |(a, s)| {
                f(a).run_state(s)
            })
        })
    }

    fn run<T>(self) -> M
    where
        Self: HKTApply<T>,
        S: Default,
    {
        self.run_state(S::default())
    }
}
