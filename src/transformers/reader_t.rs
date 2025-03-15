//! # Reader Transformer
//! 
//! This module provides the `ReaderT` monad transformer, which adds the ability to read
//! from an environment to any base monad.
//! 
//! The `ReaderT` transformer represents computations that can read from a shared environment
//! while also supporting the effects of the base monad.
//! 
//! ## Usage
//! 
//! ```rust
//! use rustica::transformers::ReaderT;
//! use rustica::prelude::*;
//! 
//! // Create a ReaderT over Vec for a configuration environment
//! let reader_t: ReaderT<i32, Vec<i32>, i32> = ReaderT::new(|config: i32| vec![config, config * 2, config * 3]);
//! 
//! // Run with a specific environment value
//! let result = reader_t.run_reader(10);
//! assert_eq!(result, vec![10, 20, 30]);
//! ```

use super::MonadTransformer;
use crate::traits::monad::Monad;
use std::marker::PhantomData;
use std::sync::Arc;

/// The `ReaderT` monad transformer adds environment reading capabilities to any base monad.
/// 
/// `ReaderT<E, M, A>` represents a computation that can read from an environment of type `E`,
/// and produces a value of type `A` within the context of monad `M`.
/// 
/// # Type Parameters
/// 
/// * `E` - The environment type
/// * `M` - The base monad type constructor
/// * `A` - The result type
/// 
/// # Examples
/// 
/// ```rust
/// use rustica::transformers::ReaderT;
/// use rustica::prelude::*;
/// 
/// // Create a reader transformer over Vec
/// let reader_t: ReaderT<String, Vec<usize>, usize> = ReaderT::new(|config: String| {
///     vec![config.len(), config.chars().count()]
/// });
/// 
/// // Run with a specific environment
/// let result = reader_t.run_reader("hello".to_string());
/// assert_eq!(result, vec![5, 5]);
/// ```
pub struct ReaderT<E, M, A> {
    /// Internal function that runs with an environment to produce a monadic value
    run_reader_fn: Arc<dyn Fn(E) -> M + Send + Sync>,
    /// Phantom data to track the value type
    _phantom: PhantomData<A>,
}

impl<E, M, A> Clone for ReaderT<E, M, A> 
where 
    E: 'static,
    M: 'static,
{
    fn clone(&self) -> Self {
        ReaderT {
            run_reader_fn: self.run_reader_fn.clone(),
            _phantom: PhantomData,
        }
    }
}

impl<E, M, A> ReaderT<E, M, A> 
where 
    E: 'static,
    M: 'static,
{
    /// Creates a new `ReaderT` transformer.
    /// 
    /// # Parameters
    /// 
    /// * `f` - A function that takes an environment and returns a monadic value
    /// 
    /// # Returns
    /// 
    /// A new `ReaderT` instance
    #[inline]
    pub fn new<F>(f: F) -> Self 
    where 
        F: Fn(E) -> M + 'static + Send + Sync,
    {
        ReaderT {
            run_reader_fn: Arc::new(f),
            _phantom: PhantomData,
        }
    }
    
    /// Runs the reader transformer with a specific environment.
    /// 
    /// # Parameters
    /// 
    /// * `env` - The environment to run with
    /// 
    /// # Returns
    /// 
    /// The resulting monadic value
    #[inline]
    pub fn run_reader(&self, env: E) -> M 
    where 
        E: Clone,
    {
        (self.run_reader_fn)(env)
    }
    
    /// Creates a `ReaderT` that returns the environment itself, wrapped in the base monad.
    /// 
    /// # Type Parameters
    /// 
    /// * `M` - The base monad type constructor
    /// 
    /// # Returns
    /// 
    /// A `ReaderT` that returns the environment
    #[inline]
    pub fn ask<P>(pure: P) -> ReaderT<E, M, E> 
    where 
        P: Fn(E) -> M + Send + Sync + 'static,
    {
        ReaderT::new(pure)
    }
    
    /// Creates a `ReaderT` by applying a function to the environment.
    /// 
    /// # Parameters
    /// 
    /// * `f` - Function to apply to the environment
    /// * `pure` - Function to lift a value into the base monad
    /// 
    /// # Returns
    /// 
    /// A `ReaderT` that applies a function to the environment
    #[inline]
    pub fn asks<B, F, P>(f: F, pure: P) -> ReaderT<E, M, B> 
    where 
        F: Fn(E) -> B + Send + Sync + 'static,
        P: Fn(B) -> M + Send + Sync + 'static,
    {
        ReaderT::new(move |e| pure(f(e)))
    }
    
    /// Modifies the environment before running a reader transformer.
    /// 
    /// # Parameters
    /// 
    /// * `f` - Function to modify the environment
    /// 
    /// # Returns
    /// 
    /// A `ReaderT` that runs with a modified environment
    #[inline]
    pub fn local<F>(&self, f: F) -> Self 
    where 
        F: Fn(E) -> E + Send + Sync + 'static,
    {
        let inner_fn = self.run_reader_fn.clone();
        ReaderT::new(move |e| inner_fn(f(e)))
    }
}

/// Extended methods for ReaderT with monadic operations.
/// These methods require knowledge of how to work with the underlying monad type.
impl<E, M, A> ReaderT<E, M, A>
where
    E: Clone + Send + Sync + 'static,
    M: Monad<Source = A> + Clone + 'static,
{
    /// Maps a function over the values inside this ReaderT.
    /// 
    /// This is a specialized implementation that works with monads that have a map function.
    /// 
    /// # Parameters
    /// 
    /// * `f` - Function to apply to the values
    /// * `map_fn` - Function that knows how to map over the base monad
    /// 
    /// # Returns
    /// 
    /// A new ReaderT with the function applied to its values
    #[inline]
    pub fn fmap_with<B, F, MapFn>(&self, f: F, map_fn: MapFn) -> ReaderT<E, M, B>
    where
        F: Fn(A) -> B + Clone + Send + Sync + 'static,
        MapFn: Fn(M, F) -> M + Send + Sync + 'static,
        A: 'static,
        B: 'static,
        M: 'static,
    {
        let inner_fn = self.run_reader_fn.clone();
        let f_clone = f.clone();
        
        ReaderT::new(move |e| {
            let m = inner_fn(e);
            map_fn(m, f_clone.clone())
        })
    }
    
    /// Binds this ReaderT with a function that produces another ReaderT.
    /// 
    /// This is the monadic bind operation, which allows sequencing operations that depend
    /// on the result of previous operations.
    /// 
    /// # Parameters
    /// 
    /// * `f` - Function that takes a value and returns a new ReaderT
    /// * `bind_fn` - Function that knows how to perform bind on the base monad
    /// 
    /// # Returns
    /// 
    /// A new ReaderT representing the sequenced computation
    #[inline]
    pub fn bind_with<B, N, F, BindFn>(&self, f: F, bind_fn: BindFn) -> ReaderT<E, N, B>
    where
        F: Fn(A) -> ReaderT<E, N, B> + Clone + Send + Sync + 'static,
        BindFn: Fn(M, Arc<dyn Fn(A) -> N + Send + Sync>) -> N + Send + Sync + 'static,
        A: Clone + 'static,
        B: 'static,
        M: 'static,
        N: 'static,
    {
        let inner_fn = self.run_reader_fn.clone();
        let f_clone = f.clone();
        
        ReaderT::new(move |e: E| {
            let m = inner_fn(e.clone());
            let e_for_closure = e.clone();
            let f_for_closure = f_clone.clone();
            
            let bind_closure = Arc::new(move |a: A| {
                let reader_b = f_for_closure(a);
                reader_b.run_reader(e_for_closure.clone())
            });
            
            bind_fn(m, bind_closure)
        })
    }
    
    /// Applies a function from another ReaderT to the values in this ReaderT.
    /// 
    /// This implements the applicative functor pattern.
    /// 
    /// # Parameters
    /// 
    /// * `f` - ReaderT containing functions to apply
    /// * `ap_fn` - Function that knows how to perform function application in the base monad
    /// 
    /// # Returns
    /// 
    /// A new ReaderT with the functions applied
    #[inline]
    pub fn apply_with<B, F, ApFn>(&self, f: &ReaderT<E, M, F>, ap_fn: ApFn) -> ReaderT<E, M, B>
    where
        F: Fn(A) -> B + Clone + Send + Sync + 'static,
        ApFn: Fn(M, M) -> M + Clone + Send + Sync + 'static,
        A: Clone + 'static,
        B: 'static,
        M: 'static,
    {
        let self_fn = self.run_reader_fn.clone();
        let f_fn = f.run_reader_fn.clone();
        let ap_fn_clone = ap_fn.clone();
        
        ReaderT::new(move |e: E| {
            let ma = self_fn(e.clone());
            let mf = f_fn(e.clone());
            ap_fn_clone(ma, mf)
        })
    }
    
    /// Combines this ReaderT with another using a binary function.
    /// 
    /// This is useful for combining the results of two reader operations that depend
    /// on the same environment.
    /// 
    /// # Parameters
    /// 
    /// * `other` - Another ReaderT to combine with
    /// * `f` - Function to combine the results
    /// * `combine_fn` - Function that knows how to combine values in the base monad
    /// 
    /// # Returns
    /// 
    /// A new ReaderT with the combined results
    #[inline]
    pub fn combine_with<B, C, F, CombineFn>(
        &self,
        other: &ReaderT<E, M, B>,
        f: F,
        combine_fn: CombineFn
    ) -> ReaderT<E, M, C>
    where
        F: Fn(A, B) -> C + Clone + Send + Sync + 'static,
        CombineFn: Fn(M, M, F) -> M + Clone + Send + Sync + 'static,
        A: Clone + 'static,
        B: Clone + 'static,
        C: 'static,
        M: 'static,
    {
        let self_fn = self.run_reader_fn.clone();
        let other_fn = other.run_reader_fn.clone();
        let f_clone = f.clone();
        let combine_fn_clone = combine_fn.clone();
        
        ReaderT::new(move |e: E| {
            let ma = self_fn(e.clone());
            let mb = other_fn(e.clone());
            combine_fn_clone(ma, mb, f_clone.clone())
        })
    }
    
    /// Creates a ReaderT that returns a pure value, independent of the environment.
    /// 
    /// # Parameters
    /// 
    /// * `value` - The value to return
    /// * `pure_fn` - Function that lifts a value into the base monad
    /// 
    /// # Returns
    /// 
    /// A ReaderT that always returns the given value
    #[inline]
    pub fn pure<B, PureFn>(value: B, pure_fn: PureFn) -> ReaderT<E, M, B>
    where
        B: Clone + Send + Sync + 'static,
        PureFn: Fn(B) -> M + Send + Sync + 'static,
    {
        let cloned_value = value.clone();
        ReaderT::new(move |_| pure_fn(cloned_value.clone()))
    }

    /// Unwraps this ReaderT to get the base monad value by providing an environment.
    /// 
    /// This method allows for safely unwrapping a ReaderT by providing the
    /// environment needed to run the computation.
    /// 
    /// # Parameters
    /// 
    /// * `env` - The environment to use for unwrapping
    /// 
    /// # Returns
    /// 
    /// The base monad value
    #[inline]
    pub fn unwrap_with(self, env: E) -> M {
        self.run_reader(env)
    }

    #[inline]
    pub fn lift<B>(m: M) -> ReaderT<E, M, B>
    where
        M: Clone + Send + Sync + 'static,
        B: 'static,
    {
        ReaderT::new(move |_: E| m.clone())
    }
}

// Implementation of MonadTransformer for ReaderT
impl<E, M, A> MonadTransformer for ReaderT<E, M, A> 
where 
    E: Clone + 'static,
    M: Monad<Source = A> + Send + Sync + Clone + 'static,
    A: Clone + 'static,
{
    type BaseMonad = M;
    
    #[inline]
    fn lift(base: Self::BaseMonad) -> Self {
        let base_clone = base.clone();
        ReaderT::new(move |_| base_clone.clone())
    }
    
    /// It does nothing. Returns panic.
    /// 
    /// This method is a placeholder and should not be used in production code.
    /// It always panics when called, serving as a reminder to implement proper
    /// functionality or to use `unwrap_with(env)` instead.
    /// 
    /// # Panics
    /// 
    /// This method always panics with a message indicating that an environment
    /// is required to unwrap a ReaderT.
    #[inline]
    fn unwrap(self) -> Self::BaseMonad {
        // Since we need an environment to run the reader, we can't generally
        // unwrap a ReaderT without providing an environment. This is a limitation
        // of the ReaderT transformer.
        panic!("ReaderT::unwrap() requires an environment. Use unwrap_with(env) instead.")
    }
}