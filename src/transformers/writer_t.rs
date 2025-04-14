//! The `WriterT` transformer adds the ability to produce a log alongside a computation.
//!
//! This module provides the `WriterT` transformer, which extends a monad with the ability
//! to accumulate a log alongside computations. It's useful for tasks like:
//!
//! - **Logging**: Adding logging to computations in a pure functional way
//! - **Collecting Metrics with Effects**: Gathering statistics during computation that may include other effects
//! - **Building Audit Trails**: Tracking the history of operations that may succeed or fail
//! - **Accumulating Results**: Collecting intermediate results alongside the main computation with optional effects
//!
//! ## Basic Usage
//!
//! ```rust
//! use rustica::transformers::WriterT;
//! use rustica::traits::monoid::Monoid;
//! use rustica::traits::semigroup::Semigroup;
//! use rustica::prelude::*;
//!
//! // Define a simple log type using Vec<String>
//! #[derive(Clone, Debug, PartialEq)]
//! struct Log(Vec<String>);
//!
//! impl Semigroup for Log {
//!     fn combine(&self, other: &Self) -> Self {
//!         let mut combined = self.0.clone();
//!         combined.extend(other.0.clone());
//!         Log(combined)
//!     }
//!
//!     fn combine_owned(self, other: Self) -> Self {
//!         let mut combined = self.0;
//!         combined.extend(other.0);
//!         Log(combined)
//!     }
//! }
//!
//! impl Monoid for Log {
//!     fn empty() -> Self {
//!         Log(Vec::new())
//!     }
//! }
//!
//! // Create a WriterT over Option
//! let writer_t: WriterT<Log, Option<(Log, i32)>, i32> = WriterT::tell_with::<_, ()>(
//!     Log(vec!["Start".to_string()]),
//!     42,
//!     |w, v| Some((w, v))
//! );
//!
//! // Run the writer transformer to get the option containing log and value
//! let result: Option<(Log, i32)> = writer_t.run_writer();
//! assert_eq!(result, Some((Log(vec!["Start".to_string()]), 42)));
//! ```

use super::MonadTransformer;
use crate::traits::functor::Functor;
use crate::traits::hkt::HKT;
use crate::traits::monad::Monad;
use crate::traits::monoid::Monoid;
use crate::traits::semigroup::Semigroup;
use std::marker::PhantomData;
use std::sync::Arc;

/// Type alias for a function that combines two WriterT instances with the same log and monad types
/// but potentially different value types, producing a new WriterT.
pub type WriterCombineFn<W, M1, A1, B1, C1> =
    dyn Fn(&WriterT<W, M1, A1>, &WriterT<W, M1, B1>) -> WriterT<W, M1, C1> + Send + Sync;

/// The `WriterT` monad transformer adds logging capabilities to any base monad.
///
/// `WriterT<W, M, A>` represents a computation that produces a log of type `W` and a value of type `A`
/// within the context of monad `M`.
///
/// # Type Parameters
///
/// * `W` - The log type, which must implement the `Monoid` trait
/// * `M` - The base monad type constructor
/// * `A` - The result type
#[derive(Clone, Debug)]
pub struct WriterT<W, M, A> {
    /// The inner value of the writer transformer
    run: M,
    /// Phantom types for W and A
    phantom: PhantomData<(W, A)>,
}

impl<W, M, A> WriterT<W, M, A>
where
    W: 'static + Clone,
    M: 'static + Clone,
    A: 'static + Clone,
{
    /// Creates a new `WriterT` transformer.
    ///
    /// # Parameters
    ///
    /// * `m` - A monadic value that contains a tuple of log and value
    ///
    /// # Returns
    ///
    /// A new `WriterT` instance
    #[inline]
    pub fn new(m: M) -> Self {
        WriterT {
            run: m,
            phantom: PhantomData,
        }
    }

    /// Runs the writer transformer to extract the base monad's value.
    ///
    /// # Returns
    ///
    /// The base monad containing the log and value pair
    #[inline]
    pub fn run_writer(&self) -> M {
        self.run.clone()
    }

    /// Creates a `WriterT` that produces the given log and value.
    ///
    /// # Parameters
    ///
    /// * `w` - The log to produce
    /// * `a` - The value to produce
    /// * `pure` - Function to lift the log and value into the base monad
    ///
    /// # Returns
    ///
    /// A new `WriterT` instance
    #[inline]
    pub fn tell_with<P, F>(w: W, a: A, pure: P) -> Self
    where
        P: Fn(W, A) -> M + 'static,
        F: 'static,
    {
        WriterT::new(pure(w, a))
    }

    /// Creates a `WriterT` with just a log and unit value.
    ///
    /// # Parameters
    ///
    /// * `w` - The log to produce
    /// * `pure` - Function to lift the log and unit value into the base monad
    ///
    /// # Returns
    ///
    /// A new `WriterT` instance with unit value
    #[inline]
    pub fn tell_log_with<P, F>(w: W, pure: P) -> WriterT<W, M, ()>
    where
        P: Fn(W, ()) -> M + 'static,
        F: 'static,
    {
        WriterT::tell_with::<P, F>(w, (), pure)
    }

    /// Extracts the value from the writer transformer.
    ///
    /// # Parameters
    ///
    /// * `extract` - Function to extract the value from the log-value pair
    ///
    /// # Returns
    ///
    /// The base monad containing just the value
    #[inline]
    pub fn extract_with<F, N>(self, extract: F) -> N
    where
        F: Fn(M) -> N + 'static,
    {
        extract(self.run)
    }

    /// Maps a function over the values inside this WriterT.
    ///
    /// # Parameters
    ///
    /// * `f` - Function to apply to the values
    /// * `map_fn` - Function that knows how to map over the base monad
    ///
    /// # Returns
    ///
    /// A new WriterT with the function applied to its values
    #[inline]
    pub fn fmap_with<F, MapFn, B>(&self, f: F, map_fn: MapFn) -> WriterT<W, M, B>
    where
        F: Fn(A) -> B + Clone + 'static,
        MapFn: Fn(M, F) -> M + 'static,
        B: Clone + 'static,
        M: Clone,
    {
        WriterT::new(map_fn(self.run.clone(), f))
    }

    /// Applies a function from another WriterT to the values in this WriterT.
    ///
    /// # Parameters
    ///
    /// * `f` - WriterT containing functions to apply
    /// * `ap_fn` - Function that knows how to perform function application in the base monad
    ///
    /// # Returns
    ///
    /// A new WriterT with the functions applied
    pub fn apply_with<Func, B, ApFn>(
        &self, f: &WriterT<W, M, Func>, ap_fn: ApFn,
    ) -> WriterT<W, M, B>
    where
        Func: Fn(A) -> B + Clone + 'static,
        B: Clone + 'static,
        W: Semigroup + Clone + 'static,
        A: Clone + 'static,
        M: Clone + 'static,
        ApFn: Fn(M, M, fn((W, A), (W, Func)) -> (W, B)) -> M + 'static,
    {
        // Function to apply the function from f to the value in self
        let apply_fn = |(w1, a): (W, A), (w2, func): (W, Func)| {
            // Combine the logs and apply the function to the value
            (w1.combine(&w2), func(a))
        };

        // Apply the function using the provided ap_fn
        WriterT::new(ap_fn(self.run.clone(), f.run.clone(), apply_fn))
    }

    /// Binds this WriterT with a function that produces another WriterT.
    ///
    /// # Parameters
    ///
    /// * `f` - Function that takes a value and returns a new WriterT
    /// * `bind_fn` - Function that knows how to perform bind on the base monad
    ///
    /// # Returns
    ///
    /// A new WriterT representing the sequenced computation
    pub fn bind_with<F, B, N, BindFn>(&self, f: F, bind_fn: BindFn) -> WriterT<W, N, B>
    where
        F: Fn(&A) -> WriterT<W, N, B> + Clone + Send + Sync + 'static,
        B: Clone + 'static,
        N: Clone + 'static,
        M: Clone + 'static,
        A: Clone + 'static,
        W: Clone + 'static,
        BindFn: Fn(M, Arc<dyn Fn(A) -> N + Send + Sync>) -> N + 'static,
    {
        // Create a function that takes an owned A and returns the inner monad of the WriterT
        let f_wrapped = Arc::new(move |a: A| f(&a).run);
        WriterT::new(bind_fn(self.run.clone(), f_wrapped))
    }

    /// Combines this WriterT with another using a binary function.
    ///
    /// # Parameters
    ///
    /// * `other` - Another WriterT to combine with
    /// * `f` - Function to combine the results
    /// * `combine_fn` - Function that knows how to combine values in the base monad
    ///
    /// # Returns
    ///
    /// A new WriterT with the combined results
    pub fn combine_with<B, C, F, CombineFn>(
        &self, other: &WriterT<W, M, B>, f: F, combine_fn: CombineFn,
    ) -> WriterT<W, M, C>
    where
        B: Clone + 'static,
        C: Clone + 'static,
        F: Fn(A, B) -> C + 'static,
        M: Clone + 'static,
        A: Clone + 'static,
        W: Semigroup + Clone + 'static,
        CombineFn: for<'a> Fn(M, M, &'a dyn Fn((W, A), (W, B)) -> (W, C)) -> M + 'static,
    {
        // Create the combine function
        let combine_fn_impl = |w1a: (W, A), w2b: (W, B)| -> (W, C) {
            let (w1, a) = w1a;
            let (w2, b) = w2b;
            (w1.combine(&w2), f(a, b))
        };

        // Pass the closure by reference to the combine_fn
        WriterT::new(combine_fn(
            self.run.clone(),
            other.run.clone(),
            &combine_fn_impl,
        ))
    }

    /// Lifts a function that produces a log and a value into a WriterT
    ///
    /// # Parameters
    ///
    /// * `f` - Function that takes an input and returns a log and value
    /// * `pure` - Function to lift the log and value into the base monad
    ///
    /// # Returns
    ///
    /// A function that takes an input and returns a WriterT
    pub fn lift_writer<I, B, F, P>(f: F, pure: P) -> impl Fn(I) -> WriterT<W, M, B>
    where
        F: Fn(I) -> (W, B) + 'static,
        B: Clone + 'static,
        I: 'static,
        M: 'static,
        W: Clone + 'static,
        P: Fn(W, B) -> M + 'static,
    {
        move |input: I| {
            let (w, b) = f(input);
            WriterT::new(pure(w, b))
        }
    }

    /// Maps a function over the values inside this WriterT.
    ///
    /// This is the Functor operation for WriterT.
    ///
    /// # Parameters
    ///
    /// * `f` - Function to apply to the values
    ///
    /// # Returns
    ///
    /// A new WriterT with the function applied to its values
    ///
    /// # Examples
    #[inline]
    pub fn fmap<F, B>(&self, f: F) -> WriterT<W, M, B>
    where
        F: Fn(A) -> B + Clone + Send + Sync + 'static,
        B: Clone + 'static,
        W: Clone + 'static,
        A: Clone + 'static,
        M: HKT<Source = (W, A), Output<(W, B)> = M> + Functor + Clone + 'static,
    {
        WriterT::new(M::fmap(&self.run, |pair_ref| {
            let (w, a) = pair_ref;
            (w.clone(), f(a.clone()))
        }))
    }

    /// Applies a function from another WriterT to the values in this WriterT.
    ///
    /// This is the Applicative operation for WriterT.
    ///
    /// # Parameters
    ///
    /// * `f` - WriterT containing functions to apply
    ///
    /// # Returns
    ///
    /// A new WriterT with the functions applied
    #[inline]
    pub fn apply_with_monad<Func, B, ApFn>(
        &self, f: &WriterT<W, M, Func>, ap_fn: ApFn,
    ) -> WriterT<W, M, B>
    where
        Func: Fn(A) -> B + Clone + 'static,
        B: Clone + 'static,
        W: Semigroup + Clone + 'static,
        A: Clone + 'static,
        M: Clone + 'static,
        ApFn: Fn(M, M, fn((W, A), (W, Func)) -> (W, B)) -> M + 'static,
    {
        let apply_fn = |(w1, a): (W, A), (w2, func): (W, Func)| {
            // Combine the logs and apply the function to the value
            (w1.combine(&w2), func(a))
        };

        // Apply the function using the provided ap_fn
        WriterT::new(ap_fn(self.run.clone(), f.run.clone(), apply_fn))
    }

    /// Binds this WriterT with a function that produces another WriterT.
    ///
    /// This is the Monad operation for WriterT.
    ///
    /// # Parameters
    ///
    /// * `f` - Function that takes a value and returns a new WriterT
    ///
    /// # Returns
    ///
    /// A new WriterT representing the sequenced computation
    #[inline]
    pub fn bind_with_monad<B, F, G>(&self, f: F, bind_fn: G) -> WriterT<W, M, B>
    where
        F: Fn(&A) -> WriterT<W, M, B> + 'static,
        B: Clone + 'static,
        M: Clone + 'static,
        A: Clone + 'static,
        W: Semigroup + Clone + 'static,
        G: FnOnce(M, F) -> M + 'static,
    {
        WriterT::new(bind_fn(self.run.clone(), f))
    }

    /// Joins a nested WriterT.
    ///
    /// This is part of the Monad operations.
    ///
    /// # Returns
    ///
    /// The flattened WriterT
    #[inline]
    pub fn join_with<B, JoinFn>(&self, join_fn: JoinFn) -> WriterT<W, M, B>
    where
        W: Semigroup + Clone + 'static,
        JoinFn: Fn(M) -> M + 'static,
        A: Clone + 'static,
        B: Clone + 'static,
        M: Clone + 'static,
    {
        WriterT::new(join_fn(self.run.clone()))
    }

    /// Sequences two WriterT operations, discarding the value of the first.
    ///
    /// # Parameters
    ///
    /// * `other` - The second WriterT to run after this one
    /// * `then_fn` - Function that knows how to sequence operations in the base monad
    ///
    /// # Returns
    ///
    /// A new WriterT with the log from both Writers and the value from the second
    pub fn then_with<B, ThenFn>(
        &self, other: &WriterT<W, M, B>, then_fn: ThenFn,
    ) -> WriterT<W, M, B>
    where
        W: Semigroup + Clone + 'static,
        ThenFn: Fn(M, M, fn((W, A), (W, B)) -> (W, B)) -> M + 'static,
        A: Clone + 'static,
        B: Clone + 'static,
        M: Clone + 'static,
    {
        let combine_fn = |(w1, _): (W, A), (w2, b): (W, B)| (w1.combine(&w2), b);

        WriterT::new(then_fn(self.run.clone(), other.run.clone(), combine_fn))
    }

    /// Creates a WriterT with an additional log entry and the same value.
    ///
    /// # Parameters
    ///
    /// * `log` - The log to add
    /// * `map_fn` - Function that knows how to map over the base monad
    ///
    /// # Returns
    ///
    /// A WriterT with the additional log entry
    pub fn log_with<MapFn>(&self, log: W, map_fn: MapFn) -> Self
    where
        W: Semigroup + Clone + Send + Sync + 'static,
        MapFn: Fn(M, Arc<dyn Fn((W, A)) -> (W, A) + Send + Sync>) -> M + 'static,
        A: Clone + 'static,
        M: Clone,
    {
        let log_clone = log.clone();
        let log_fn = Arc::new(move |(w, a): (W, A)| (w.combine(&log_clone), a));

        WriterT::new(map_fn(self.run.clone(), log_fn))
    }

    /// Creates a `WriterT` that contains a pure value with an empty log.
    ///
    /// This is the Pure operation for WriterT.
    ///
    /// # Parameters
    ///
    /// * `value` - The value to wrap
    /// * `pure_fn` - Function to lift the value into the base monad
    ///
    /// # Returns
    ///
    /// A new `WriterT` instance with the value and an empty log
    #[inline]
    pub fn pure<T, P>(value: T, pure_fn: P) -> WriterT<W, M, T>
    where
        W: Monoid + Clone + 'static,
        T: Clone + 'static,
        P: Fn(W, T) -> M + 'static,
    {
        WriterT::tell_with::<P, fn(W, T) -> M>(W::empty(), value, pure_fn)
    }

    /// Creates a WriterT that applies a modification to the log
    ///
    /// # Parameters
    ///
    /// * `f` - Function to modify the log
    /// * `map_fn` - Function that knows how to map over the base monad
    ///
    /// # Returns
    ///
    /// A WriterT with the modified log
    #[inline]
    pub fn censor_with<F, MapFn>(&self, f: F, map_fn: MapFn) -> Self
    where
        F: Fn(&W) -> W + Clone + Send + Sync + 'static,
        MapFn: Fn(M, Arc<dyn Fn(W) -> W + Send + Sync>) -> M + 'static,
        W: Clone + 'static,
        A: Clone + 'static,
        M: Clone + 'static,
    {
        let log_modifier = Arc::new(move |w: W| f(&w));
        WriterT::new(map_fn(self.run.clone(), log_modifier))
    }

    /// Creates a WriterT that includes the log in the value
    ///
    /// # Parameters
    ///
    /// * `map_fn` - Function that knows how to map over the base monad
    ///
    /// # Returns
    ///
    /// A WriterT that includes the log in the value
    #[inline]
    pub fn listen_with<MapFn>(&self, map_fn: MapFn) -> WriterT<W, M, (A, W)>
    where
        MapFn: Fn(M) -> M + 'static,
        M: Clone + 'static,
        W: Clone + 'static,
        A: Clone + 'static,
    {
        WriterT::new(map_fn(self.run.clone()))
    }

    /// Creates a WriterT where the value includes a function to modify the log
    ///
    /// # Parameters
    ///
    /// * `map_fn` - Function that knows how to map over the base monad
    ///
    /// # Returns
    ///
    /// A WriterT with the log modified by a function from the value
    #[inline]
    pub fn pass_with<MapFn, B>(&self, map_fn: MapFn) -> WriterT<W, M, B>
    where
        A: Clone + 'static,
        B: Clone + 'static,
        MapFn: Fn(M) -> M + 'static,
        M: Clone + 'static,
        W: Clone + 'static,
    {
        WriterT::new(map_fn(self.run.clone()))
    }

    /// This method provides a specialized bind implementation for WriterT over Option.
    /// It's an example of how to implement binding for a specific base monad.
    #[inline]
    pub fn bind_option<F, B>(&self, f: F) -> WriterT<W, Option<(W, B)>, B>
    where
        W: Semigroup + Clone + 'static,
        A: Clone + 'static,
        B: Clone + 'static,
        F: Fn(&A) -> WriterT<W, Option<(W, B)>, B> + 'static,
        M: Clone + Into<Option<(W, A)>>,
    {
        let bind_fn = |m: Option<(W, A)>, f: &F| -> Option<(W, B)> {
            m.and_then(|(log1, val1)| {
                let new_writer = f(&val1);
                new_writer.run.map(|(log2, val2)| (log1.combine(&log2), val2))
            })
        };

        WriterT::new(bind_fn(self.run.clone().into(), &f))
    }

    /// This method provides a specialized bind implementation for WriterT over Result.
    /// It's an example of how to implement binding for a specific base monad.
    #[inline]
    pub fn bind_result<F, B, E>(&self, f: F) -> WriterT<W, Result<(W, B), E>, B>
    where
        W: Semigroup + Clone + 'static,
        A: Clone + 'static,
        B: Clone + 'static,
        E: Clone + 'static,
        F: Fn(&A) -> WriterT<W, Result<(W, B), E>, B> + 'static,
        M: Clone + Into<Result<(W, A), E>>,
    {
        let bind_fn = |m: Result<(W, A), E>, f: &F| -> Result<(W, B), E> {
            m.and_then(|(log1, val1)| {
                let new_writer = f(&val1);
                new_writer.run.map(|(log2, val2)| (log1.combine(&log2), val2))
            })
        };

        WriterT::new(bind_fn(self.run.clone().into(), &f))
    }

    /// This method provides a specialized bind implementation for WriterT over Vec.
    /// It's an example of how to implement binding for a specific base monad.
    #[inline]
    pub fn bind_vec<F, B>(&self, f: F) -> WriterT<W, Vec<(W, B)>, B>
    where
        W: Semigroup + Clone + 'static,
        A: Clone + 'static,
        B: Clone + 'static,
        F: Fn(&A) -> WriterT<W, Vec<(W, B)>, B> + 'static,
        M: Clone + Into<Vec<(W, A)>>,
    {
        let bind_fn = |m: Vec<(W, A)>, f: &F| -> Vec<(W, B)> {
            m.into_iter()
                .flat_map(|(log1, val1)| {
                    let new_writer = f(&val1);
                    new_writer
                        .run
                        .into_iter()
                        .map(move |(log2, val2)| (log1.clone().combine(&log2), val2))
                })
                .collect()
        };

        WriterT::new(bind_fn(self.run.clone().into(), &f))
    }
}

// Implementation of MonadTransformer for WriterT
impl<W, M, A> MonadTransformer for WriterT<W, M, A>
where
    W: 'static + Clone,
    M: 'static + Clone + Monad,
    A: 'static + Clone,
{
    type BaseMonad = M;

    /// Lifts a value from the base monad into the WriterT transformer.
    ///
    /// # Parameters
    ///
    /// * `m` - A value in the base monad
    ///
    /// # Returns
    ///
    /// A `WriterT` containing the lifted value
    #[inline]
    fn lift(m: Self::BaseMonad) -> Self {
        WriterT {
            run: m,
            phantom: PhantomData,
        }
    }
}
