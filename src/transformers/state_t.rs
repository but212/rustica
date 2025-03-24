//! The State monad transformer, adding stateful computations to any monad.
//!
//! `StateT` allows combining state operations with effects provided by the base monad.
//! For example, it can be combined with `Option` to create stateful computations that
//! may fail, or with `Result` to create stateful computations that may produce errors.
//!
//! # Examples
//!
//! ```rust
//! use rustica::transformers::StateT;
//! use rustica::prelude::*;
//!
//! // Create a StateT over Option that increments the state and returns it
//! let state_t: StateT<i32, Option<(i32, i32)>, i32> =
//!     StateT::new(|s: i32| Some((s + 1, s)));
//!
//! // Run with an initial state
//! let result = state_t.run_state(10);
//! assert_eq!(result, Some((11, 10)));
//! ```
//!
//! ## State Manipulation and Composition
//!
//! ```rust
//! use rustica::transformers::StateT;
//! use rustica::prelude::*;
//!
//! // Define a more complex state type
//! #[derive(Debug, Clone, PartialEq)]
//! struct Counter {
//!     value: i32,
//!     increments: i32,
//! }
//!
//! // Create a state that increments the counter value
//! let increment: StateT<Counter, Option<(Counter, i32)>, i32> = StateT::new(|mut s: Counter| {
//!     s.value += 1;
//!     s.increments += 1;
//!     Some((s.clone(), s.value))
//! });
//!
//! // Create a StateT that doubles the counter value and returns the previous value
//! let double: StateT<Counter, Option<(Counter, i32)>, i32> = StateT::new(|mut s: Counter| {
//!     let prev = s.value;
//!     s.value *= 2;
//!     s.increments += 1;
//!     Some((s.clone(), prev))
//! });
//!
//! // Compose state operations
//! let inc_and_double = increment.bind_with(
//!     move |_| double.clone(),
//!     |m, f| m.and_then(|(s, _)| f((s, 0)))
//! );
//!
//! // Run with an initial state
//! let result = inc_and_double.run_state(Counter { value: 5, increments: 0 });
//!
//! // After incrementing, value = 6, then we double to 12
//! // The final result is ((Counter{value: 12, increments: 2}, 6))
//! // where 6 is the value after increment (returned by double)
//! assert_eq!(result.map(|(s, v)| (s.value, s.increments, v)), Some((12, 2, 6)));
//! ```

use std::marker::PhantomData;
use std::sync::Arc;

use crate::traits::monad::Monad;
use crate::transformers::MonadTransformer;

/// Type alias for a function that transforms a state-value pair to another state-value pair
pub type StateValueMapper<S, A, B> = Box<dyn Fn((S, A)) -> (S, B) + Send + Sync>;

/// Type alias for a function that combines two state-value pairs into a new state-value pair
pub type StateCombiner<S, A, B, C> = Box<dyn Fn((S, A), (S, B)) -> (S, C) + Send + Sync>;

/// A monad transformer that adds state capabilities to a base monad.
///
/// The `StateT` type takes three type parameters:
/// - `S`: The state type
/// - `M`: The base monad type, which wraps a tuple of state and value
/// - `A`: The value type
///
/// # Examples
///
/// ```rust
/// use rustica::transformers::StateT;
/// use rustica::prelude::*;
///
/// // Create a state transformer over Result that counts characters
/// let count_chars: StateT<usize, Result<(usize, usize), &str>, usize> = StateT::new(|state: usize| {
///     Ok((state + 1, state))
/// });
///
/// // Run with a specific initial state
/// let result = count_chars.run_state(5);
/// assert_eq!(result, Ok((6, 5)));
/// ```
pub struct StateT<S, M, A> {
    run_fn: Arc<dyn Fn(S) -> M + Send + Sync>,
    _phantom: PhantomData<A>,
}

impl<S, M, A> Clone for StateT<S, M, A>
where
    S: 'static,
    M: 'static,
{
    fn clone(&self) -> Self {
        StateT {
            run_fn: Arc::clone(&self.run_fn),
            _phantom: PhantomData,
        }
    }
}

impl<S, M, A> StateT<S, M, A>
where
    S: 'static,
    M: 'static,
    A: 'static,
{
    /// Creates a new `StateT` transformer.
    ///
    /// # Parameters
    ///
    /// * `f` - A function that takes a state and returns a monadic value containing a tuple of the new state and result
    ///
    /// # Returns
    ///
    /// A new `StateT` instance
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::transformers::StateT;
    /// use rustica::prelude::*;
    ///
    /// // Create a StateT that modifies a numeric state and returns a derived value
    /// let state_t: StateT<i32, Option<(i32, String)>, String> = StateT::new(|state: i32| {
    ///     if state <= 0 {
    ///         None
    ///     } else {
    ///         Some((state - 1, format!("Value: {}", state)))
    ///     }
    /// });
    ///
    /// assert_eq!(state_t.run_state(5), Some((4, "Value: 5".to_string())));
    /// assert_eq!(state_t.run_state(0), None);
    /// ```
    pub fn new<F>(f: F) -> Self
    where
        F: Fn(S) -> M + Send + Sync + 'static,
    {
        StateT {
            run_fn: Arc::new(f),
            _phantom: PhantomData,
        }
    }

    /// Runs the state transformer with a specific initial state.
    ///
    /// # Parameters
    ///
    /// * `state` - The initial state to run with
    ///
    /// # Returns
    ///
    /// The resulting monadic value containing the new state and result
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::transformers::StateT;
    /// use rustica::prelude::*;
    /// use std::collections::HashMap;
    ///
    /// // Create a state that counts word frequencies
    /// let count_word: StateT<HashMap<String, i32>, Option<(HashMap<String, i32>, i32)>, i32> =
    ///     StateT::new(|mut state: HashMap<String, i32>| {
    ///         let word = "hello".to_string();
    ///         let count = state.entry(word).or_insert(0);
    ///         *count += 1;
    ///         let result = *count;
    ///         Some((state, result))
    ///     });
    ///
    /// // Run with an empty HashMap
    /// let mut map = HashMap::new();
    /// let result1 = count_word.run_state(map);
    ///
    /// // Extract the state and result
    /// let (new_state, count) = result1.unwrap();
    /// assert_eq!(count, 1);
    ///
    /// // Run again with the updated state
    /// let result2 = count_word.run_state(new_state);
    /// assert_eq!(result2.map(|(_, c)| c), Some(2));
    /// ```
    pub fn run_state(&self, state: S) -> M {
        (self.run_fn)(state)
    }

    /// Creates a `StateT` that returns the current state without modifying it.
    ///
    /// # Parameters
    ///
    /// * `pure` - A function that lifts a value into the base monad
    ///
    /// # Returns
    ///
    /// A new `StateT` that returns the current state
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::transformers::StateT;
    /// use rustica::prelude::*;
    ///
    /// // Create a StateT that gets the current state
    /// let get_state = StateT::<i32, Option<(i32, i32)>, i32>::get(Some);
    ///
    /// // Run with a specific state
    /// let result = get_state.run_state(42);
    /// assert_eq!(result, Some((42, 42)));
    /// ```
    pub fn get<P>(pure: P) -> StateT<S, M, S>
    where
        P: Fn((S, S)) -> M + Send + Sync + 'static,
        S: Clone + Send + Sync,
    {
        StateT::new(move |s: S| pure((s.clone(), s)))
    }

    /// Creates a `StateT` that replaces the current state and returns the old state.
    ///
    /// # Parameters
    ///
    /// * `new_state` - The new state to set
    /// * `pure` - Function to lift a value into the base monad
    ///
    /// # Returns
    ///
    /// A `StateT` that updates the state
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::transformers::StateT;
    /// use rustica::prelude::*;
    ///
    /// // Create a StateT that sets a new state and returns the old one
    /// let put_state = StateT::<i32, Result<(i32, i32), &str>, i32>::put(100, |t| Ok(t));
    ///
    /// // Run with a specific state
    /// let result = put_state.run_state(42);
    /// assert_eq!(result, Ok((100, 42)));
    /// ```
    pub fn put<P>(new_state: S, pure: P) -> StateT<S, M, S>
    where
        P: Fn((S, S)) -> M + Send + Sync + 'static,
        S: Clone + Send + Sync,
    {
        StateT::new(move |s: S| pure((new_state.clone(), s)))
    }

    /// Creates a `StateT` that modifies the current state with a function.
    ///
    /// # Parameters
    ///
    /// * `f` - Function to modify the state
    /// * `pure` - Function to lift a value into the base monad
    ///
    /// # Returns
    ///
    /// A `StateT` that modifies the state
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::transformers::StateT;
    /// use rustica::prelude::*;
    ///
    /// // Create a StateT that doubles the current state
    /// let modify_state = StateT::<i32, Option<(i32, ())>, ()>::modify(|s| s * 2, |t| Some(t));
    ///
    /// // Run with a specific state
    /// let result = modify_state.run_state(21);
    /// assert_eq!(result, Some((42, ())));
    /// ```
    pub fn modify<F, P>(f: F, pure: P) -> StateT<S, M, ()>
    where
        F: Fn(S) -> S + Send + Sync + 'static,
        P: Fn((S, ())) -> M + Send + Sync + 'static,
    {
        StateT::new(move |s: S| pure((f(s), ())))
    }

    /// Maps a function over the values inside this StateT.
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
    /// A new StateT with the function applied to its values
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::transformers::StateT;
    /// use rustica::prelude::*;
    ///
    /// // Create a state transformer over Option
    /// let state_t: StateT<i32, Option<(i32, i32)>, i32> = StateT::new(|s: i32| {
    ///     Some((s + 1, s * 2))
    /// });
    ///
    /// // Map over the value using fmap_with
    /// let doubled_state = state_t.fmap_with(
    ///     |n: i32| n + 10,
    ///     |m: Option<(i32, i32)>, f: Box<dyn Fn((i32, i32)) -> (i32, i32) + Send + Sync>| m.map(f)
    /// );
    ///
    /// assert_eq!(doubled_state.run_state(5), Some((6, 20)));
    /// ```
    pub fn fmap_with<F, B, MapFn>(&self, f: F, map_fn: MapFn) -> StateT<S, M, B>
    where
        F: Fn(A) -> B + Send + Sync + Clone + 'static,
        MapFn: Fn(M, StateValueMapper<S, A, B>) -> M + Send + Sync + 'static,
        S: Clone + Send + Sync + 'static,
        B: 'static,
    {
        let run_fn = Arc::clone(&self.run_fn);

        StateT::new(move |s: S| {
            let f_clone = f.clone();
            let mapper: StateValueMapper<S, A, B> = Box::new(move |(state, a)| (state, f_clone(a)));

            map_fn((run_fn)(s), mapper)
        })
    }

    /// Binds this StateT with a function that produces another StateT.
    ///
    /// This is the monadic bind operation, which allows sequencing operations that depend
    /// on the result of previous operations.
    ///
    /// # Parameters
    ///
    /// * `f` - Function that takes a value and returns a new StateT
    /// * `bind_fn` - Function that knows how to perform bind on the base monad
    ///
    /// # Returns
    ///
    /// A new StateT representing the sequenced computation
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::transformers::StateT;
    /// use rustica::prelude::*;
    ///
    /// // Create a state that increments and returns the new value
    /// let increment: StateT<i32, Option<(i32, i32)>, i32> =
    ///     StateT::new(|s: i32| Some((s + 1, s + 1)));
    ///
    /// // Create a function that takes the output and produces another state transformer
    /// let validate = |n: i32| {
    ///     StateT::new(move |s: i32| {
    ///         if n > 10 {
    ///             Some((s, n * 2))
    ///         } else {
    ///             Some((s, n))
    ///         }
    ///     })
    /// };
    ///
    /// // Compose using bind_with
    /// let inc_and_validate: StateT<i32, Option<(i32, i32)>, i32> = increment.bind_with(
    ///     validate,
    ///     |m: Option<(i32, i32)>, f| m.and_then(|(s, a)| f((s, a)))
    /// );
    ///
    /// assert_eq!(inc_and_validate.run_state(5), Some((6, 6))); // <= 10, returns as-is
    /// assert_eq!(inc_and_validate.run_state(10), Some((11, 22))); // > 10, doubles
    /// ```
    pub fn bind_with<F, B, BindFn, N>(&self, f: F, bind_fn: BindFn) -> StateT<S, N, B>
    where
        F: Fn(A) -> StateT<S, N, B> + Send + Sync + Clone + 'static,
        BindFn: Fn(M, Box<dyn Fn((S, A)) -> N + Send + Sync>) -> N + Send + Sync + 'static,
        S: Clone + Send + Sync + 'static,
        N: 'static,
        B: 'static,
    {
        let run_fn = Arc::clone(&self.run_fn);

        StateT::new(move |s: S| {
            let f_clone = f.clone();
            let binder: Box<dyn Fn((S, A)) -> N + Send + Sync> = Box::new(move |(state, a)| {
                let next_state_t = f_clone(a);
                next_state_t.run_state(state)
            });

            bind_fn((run_fn)(s), binder)
        })
    }

    /// Combines this StateT with another using a binary function.
    ///
    /// This is useful for combining the results of two state operations that have the same state type.
    ///
    /// # Parameters
    ///
    /// * `other` - Another StateT to combine with
    /// * `f` - Function to combine the results
    /// * `combine_fn` - Function that knows how to combine values in the base monad
    ///
    /// # Returns
    ///
    /// A new StateT with the combined results
    pub fn combine_with<B, C, F, CombineFn>(
        &self,
        other: &StateT<S, M, B>,
        f: F,
        combine_fn: CombineFn,
    ) -> StateT<S, M, C>
    where
        F: Fn(A, B) -> C + Send + Sync + Clone + 'static,
        CombineFn: Fn(M, M, StateCombiner<S, A, B, C>) -> M + Send + Sync + 'static,
        S: Clone + Send + Sync + 'static,
        B: 'static,
        C: 'static,
    {
        let self_run_fn = Arc::clone(&self.run_fn);
        let other_run_fn = Arc::clone(&other.run_fn);

        StateT::new(move |s: S| {
            let f_clone = f.clone();
            let combiner: StateCombiner<S, A, B, C> = Box::new(move |(_, a), (state, b)| {
                let f_clone = f_clone.clone();
                (state, f_clone(a, b))
            });

            combine_fn((self_run_fn)(s.clone()), (other_run_fn)(s), combiner)
        })
    }
}

impl<S, M, A> MonadTransformer for StateT<S, M, A>
where
    S: Clone + Send + Sync + 'static,
    M: Monad<Source = (S, A)> + Send + Sync + Clone + 'static,
    A: Clone + 'static,
{
    type BaseMonad = M;

    #[inline]
    fn lift(base: M) -> Self {
        StateT::new(move |_: S| base.clone())
    }
}
