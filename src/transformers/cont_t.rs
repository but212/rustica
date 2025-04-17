//! # Continuation Monad Transformer (ContT)
//!
//! The `ContT` monad transformer generalizes the continuation monad to operate over an arbitrary monad `M`.
//! It enables computations in continuation-passing style to be composed with effects from another monad.
//!
//! ## Type
//!
//! `ContT<R, M, A>` wraps a function `(A -> M<R>) -> M<R>`
//!
//! ## Use Cases
//!
//! - Composing advanced control flow with side effects (IO, state, etc.)
//! - Implementing early exit, backtracking, coroutines within effectful computations
//!
//! ## Examples
//!
//! ```rust
//! use rustica::transformers::cont_t::ContT;
//! use rustica::datatypes::id::Id;
//!
//! // Create a simple ContT over Id
//! let cont = ContT::<i32, Id<i32>, i32>::pure(42);
//! let result = cont.run(|x| Id::new(x * 2));
//! assert_eq!(result, Id::new(84));
//!
//! // Chain ContT computations
//! let cont2 = cont.bind(|x| ContT::pure(x + 1));
//! let result2 = cont2.run(|x| Id::new(x * 2));
//! assert_eq!(result2, Id::new(86));
//! ```

use crate::traits::monad::Monad;
use std::marker::PhantomData;
use std::sync::Arc;

/// Type alias for the core continuation transformer function type
pub type ContTFn<M, A> = dyn Fn(Arc<dyn Fn(A) -> M + Send + Sync>) -> M + Send + Sync;

/// The continuation monad transformer: ContT<R, M, A> wraps a function `(A -> M<R>) -> M<R>`.
#[derive(Clone)]
pub struct ContT<R, M, A> {
    pub run_cont: Arc<ContTFn<M, A>>,
    _phantom: PhantomData<(R, A)>,
}

impl<R, M, A> ContT<R, M, A> {
    /// Create a new ContT from a function.
    pub fn new<F>(f: F) -> Self
    where
        F: Fn(Arc<dyn Fn(A) -> M + Send + Sync>) -> M + Send + Sync + 'static,
    {
        ContT {
            run_cont: Arc::new(f),
            _phantom: PhantomData,
        }
    }

    /// Run the continuation transformer with a final continuation.
    pub fn run<FN>(&self, k: FN) -> M
    where
        FN: Fn(A) -> M + Send + Sync + 'static,
    {
        (self.run_cont)(Arc::new(k))
    }

    /// Lift a value into the continuation transformer context.
    pub fn pure(a: A) -> Self
    where
        M: Clone + 'static,
        A: Clone + Send + Sync + 'static,
        R: 'static,
    {
        ContT::new(move |k| k(a.clone()))
    }
}

impl<R, M, A> ContT<R, M, A> {
    /// Monadic bind for ContT.
    pub fn bind<B, F>(self, f: F) -> ContT<R, M, B>
    where
        F: Fn(A) -> ContT<R, M, B> + Send + Sync + 'static,
        A: Send + Sync + 'static,
        B: Send + Sync + 'static,
        M: 'static,
    {
        let f = Arc::new(f);
        ContT::new(move |k| {
            let run_cont = self.run_cont.clone();
            let f = f.clone();
            run_cont(Arc::new(move |a| {
                let fb = f.clone()(a);
                (fb.run_cont)(k.clone())
            }))
        })
    }

    /// Functor fmap for ContT.
    pub fn fmap<B, F>(self, f: F) -> ContT<R, M, B>
    where
        F: Fn(A) -> B + Send + Sync + 'static,
        A: Send + Sync + 'static,
        B: Send + Sync + 'static,
        M: 'static,
    {
        let f = Arc::new(f);
        ContT::new(move |k| {
            let run_cont = self.run_cont.clone();
            let f = f.clone();
            run_cont(Arc::new(move |a| k(f.clone()(a))))
        })
    }

    /// Applicative apply for ContT.
    pub fn apply<B>(self, cf: ContT<R, M, Arc<dyn Fn(A) -> B + Send + Sync>>) -> ContT<R, M, B>
    where
        A: Send + Sync + 'static,
        B: Send + Sync + 'static,
        M: 'static,
    {
        ContT::new(move |k| {
            let run_val = self.run_cont.clone();
            let run_func = cf.run_cont.clone();
            let k = Arc::new(k);
            run_func(Arc::new(move |f| {
                let run_val = run_val.clone();
                let k = k.clone();
                run_val(Arc::new(move |a| k.clone()(f(a))))
            }))
        })
    }

    /// Example: call_cc (call-with-current-continuation)
    pub fn call_cc<B, F>(f: F) -> ContT<R, M, A>
    where
        F: Fn(Arc<dyn Fn(A) -> ContT<R, M, B> + Send + Sync>) -> ContT<R, M, A>
            + Send
            + Sync
            + 'static,
        A: Clone + Send + Sync + 'static,
        B: Send + Sync + 'static,
        M: 'static,
    {
        let f = Arc::new(f);
        ContT::new(move |k| {
            let k_clone = k.clone();
            let escape = Arc::new(move |a: A| {
                let k_inner = k_clone.clone();
                ContT::new(move |_ignored| k_inner(a.clone()))
            });
            f.clone()(escape).run_cont.clone()(k)
        })
    }
}

use crate::transformers::MonadTransformer;

impl<R, M: Monad + Clone + Send + Sync + 'static, A: Send + Sync + 'static> MonadTransformer
    for ContT<R, M, A>
{
    type BaseMonad = M;

    fn lift(base: Self::BaseMonad) -> Self {
        ContT::new(move |_k| base.clone())
    }
}
