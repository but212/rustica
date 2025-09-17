//! The State monad transformer, adding stateful computations to any monad.
//!
//! `StateT` allows combining state operations with effects provided by the base monad.
//! For example, it can be combined with `Option` to create stateful computations that
//! may fail, or with `Result` to create stateful computations that may produce errors.
//!
//! ## Performance Characteristics
//!
//! ### Time Complexity
//! - **Construction (`new`)**: O(1) - Just wraps the function in an Arc
//! - **State Execution (`run_state`)**: O(f) where f is the complexity of the state function
//! - **Bind Operations**: O(f + g) where f and g are the complexities of the chained functions
//! - **Map Operations**: O(f) where f is the complexity of the mapping function
//!
//! ### Memory Usage
//! - **Structure Size**: O(1) - Arc pointer + PhantomData (zero-sized)
//! - **State Storage**: O(S) where S is the size of the state type
//! - **Function Storage**: O(1) - Arc provides shared ownership with minimal overhead
//! - **Composition Overhead**: O(n) where n is the depth of nested StateT operations
//!
//! ### Concurrency
//! - **Thread Safety**: StateT is Send + Sync when the wrapped function is Send + Sync
//! - **Cloning**: O(1) - Arc cloning is constant time (reference counting)
//! - **State Isolation**: Each execution maintains separate state, preventing race conditions
//!
//! ### Performance Notes
//! - StateT adds minimal overhead over the base monad when used correctly
//! - Arc usage enables efficient cloning but may add slight indirection cost
//! - State passing is explicit, allowing for predictable memory usage patterns
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

use std::sync::Arc;

use crate::traits::monad::Monad;
use crate::transformers::MonadTransformer;
use crate::utils::error_utils::AppError;

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
pub enum StateT<S, M, A> {
    Pure(A),
    LiftM(M),
    Effect(Arc<dyn Fn(S) -> M + Send + Sync>),
}

impl<S, M, A> Clone for StateT<S, M, A>
where
    S: 'static,
    M: Clone + 'static,
    A: Clone + 'static,
{
    fn clone(&self) -> Self {
        match self {
            StateT::Pure(a) => StateT::Pure(a.clone()),
            StateT::LiftM(m) => StateT::LiftM(m.clone()),
            StateT::Effect(f) => StateT::Effect(Arc::clone(f)),
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
        StateT::Effect(Arc::new(f))
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
    pub fn run_state(&self, state: S) -> M
    where
        M: Clone,
        A: Clone,
    {
        match self {
            StateT::Pure(_) => panic!("Cannot run Pure StateT without a base monad"),
            StateT::LiftM(m) => m.clone(),
            StateT::Effect(f) => f(state),
        }
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
        M: Clone + 'static,
        A: Clone + 'static,
        B: 'static,
    {
        match self {
            StateT::Pure(a) => {
                let b = f(a.clone());
                StateT::Pure(b)
            },
            StateT::LiftM(m) => StateT::LiftM(map_fn(m.clone(), {
                let f_clone = f.clone();
                let mapper: StateValueMapper<S, A, B> =
                    Box::new(move |(state, a)| (state, f_clone(a)));
                mapper
            })),
            StateT::Effect(run_fn) => {
                let run_fn = Arc::clone(run_fn);
                StateT::new(move |s: S| {
                    let f_clone = f.clone();
                    let mapper: StateValueMapper<S, A, B> =
                        Box::new(move |(state, a)| (state, f_clone(a)));

                    map_fn(run_fn(s), mapper)
                })
            },
        }
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
        M: Clone + Send + Sync + 'static,
        A: Clone + 'static,
        N: Clone + 'static,
        B: Clone + 'static,
    {
        match self {
            StateT::Pure(a) => f(a.clone()),
            StateT::LiftM(m) => {
                let m_clone = m.clone();
                let f_clone = f.clone();

                StateT::new(move |_: S| {
                    let f_for_closure = f_clone.clone();
                    let binder: Box<dyn Fn((S, A)) -> N + Send + Sync> =
                        Box::new(move |(state, a)| {
                            let next_state_t = f_for_closure(a);
                            next_state_t.run_state(state)
                        });

                    bind_fn(m_clone.clone(), binder)
                })
            },
            StateT::Effect(run_fn) => {
                let run_fn = Arc::clone(run_fn);
                let f_clone = f.clone();

                StateT::new(move |s: S| {
                    let f_for_closure = f_clone.clone();
                    let binder: Box<dyn Fn((S, A)) -> N + Send + Sync> =
                        Box::new(move |(state, a)| {
                            let next_state_t = f_for_closure(a);
                            next_state_t.run_state(state)
                        });

                    bind_fn(run_fn(s), binder)
                })
            },
        }
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
        &self, other: &StateT<S, M, B>, f: F, combine_fn: CombineFn,
    ) -> StateT<S, M, C>
    where
        F: Fn(A, B) -> C + Send + Sync + Clone + 'static,
        CombineFn: Fn(M, M, StateCombiner<S, A, B, C>) -> M + Send + Sync + 'static,
        S: Clone + Send + Sync + 'static,
        M: Clone + 'static,
        A: Clone + 'static,
        B: Clone + 'static,
        C: 'static,
    {
        match (self, other) {
            (StateT::Pure(a), StateT::Pure(b)) => {
                let c = f(a.clone(), b.clone());
                StateT::Pure(c)
            },
            (StateT::LiftM(m1), StateT::LiftM(m2)) => {
                let combiner: StateCombiner<S, A, B, C> = Box::new(move |(s1, a), (_, b)| {
                    let f_clone = f.clone();
                    (s1, f_clone(a, b))
                });
                StateT::LiftM(combine_fn(m1.clone(), m2.clone(), combiner))
            },
            (StateT::Effect(self_run_fn), StateT::Effect(other_run_fn)) => {
                let self_run_fn = Arc::clone(self_run_fn);
                let other_run_fn = Arc::clone(other_run_fn);

                StateT::new(move |s: S| {
                    let f_clone = f.clone();
                    let combiner: StateCombiner<S, A, B, C> =
                        Box::new(move |(_, a), (state, b)| {
                            let f_clone = f_clone.clone();
                            (state, f_clone(a, b))
                        });

                    combine_fn(self_run_fn(s.clone()), other_run_fn(s), combiner)
                })
            },
            _ => panic!("Cannot combine StateT variants of different types"),
        }
    }

    /// Creates a new `StateT` transformer with a pure value.
    ///
    /// This method lifts a pure value into the `StateT` monad without changing
    /// the current state. It's the analog of `State::pure`.
    ///
    /// # Parameters
    ///
    /// * `a` - The value to lift into the StateT
    /// * `pure_fn` - A function that lifts a tuple into the base monad
    ///
    /// # Returns
    ///
    /// A new `StateT` containing the value and preserving the state
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::transformers::StateT;
    ///
    /// // Create a StateT with a pure value
    /// let state_t = StateT::<i32, Option<(i32, String)>, String>::pure("hello".to_string(), Some);
    ///
    /// // Running with any state just returns the value and preserves the state
    /// assert_eq!(state_t.run_state(42), Some((42, "hello".to_string())));
    /// ```
    pub fn pure<P>(a: A, pure_fn: P) -> Self
    where
        P: Fn((S, A)) -> M + Send + Sync + 'static,
        A: Clone + Send + Sync,
    {
        StateT::new(move |s| pure_fn((s, a.clone())))
    }

    /// Runs the state computation and returns only the final state, discarding the value.
    ///
    /// # Parameters
    ///
    /// * `s` - The initial state
    /// * `extract_state_fn` - Function that knows how to extract the state from the monadic result
    ///
    /// # Returns
    ///
    /// The final state after running the computation
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::transformers::StateT;
    ///
    /// // Create a state that increments the state
    /// let state_t = StateT::<i32, Option<(i32, String)>, String>::new(|s| {
    ///     Some((s + 1, format!("Value: {}", s)))
    /// });
    ///
    /// // Run and extract only the state
    /// let result = state_t.exec_state(42, |opt| opt.map(|(s, _)| s));
    /// assert_eq!(result, Some(43));
    /// ```
    pub fn exec_state<F, B>(&self, s: S, extract_state_fn: F) -> B
    where
        F: FnOnce(M) -> B,
        M: Clone,
        A: Clone,
    {
        extract_state_fn(self.run_state(s))
    }

    /// Applies a function inside a StateT to a value inside another StateT.
    /// Applies a function inside a StateT to a value inside another StateT.
    ///
    /// This is the applicative apply operation for StateT, allowing you to
    /// apply a function in a stateful context to a value in a stateful context.
    ///
    /// # Parameters
    ///
    /// * `other` - A StateT containing the value to apply the function to
    /// * `apply_fn` - A function that knows how to apply functions in the base monad
    ///
    /// # Returns
    ///
    /// A new StateT containing the result of applying the function to the value
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::transformers::StateT;
    ///
    /// // Define a function that adds state to its argument
    /// let fn_state: StateT<i32, Option<(i32, i32)>, i32> = StateT::new(|s: i32| {
    ///     Some((s + 1, 10))
    /// });
    ///
    /// // Define a state holding a value
    /// let value_state: StateT<i32, Option<(i32, i32)>, i32> = StateT::new(|s: i32| {
    ///     Some((s * 2, 5))
    /// });
    ///
    /// // Apply the function to the value
    /// let result: StateT<i32, Option<(i32, i32)>, i32> = fn_state.apply(value_state, |f_result, v_result| {
    ///     match (f_result, v_result) {
    ///         (Some((s1, f)), Some((s2, v))) => {
    ///             Some((s2, f + v)) // Using the second state, add the values
    ///         },
    ///         _ => None
    ///     }
    /// });
    ///
    /// // Run with state 10
    /// // fn_state: returns (11, 10)
    /// // value_state: returns (20, 5)
    /// // apply: returns (20, 10 + 5) = (20, 15)
    /// assert_eq!(result.run_state(10), Some((20, 15)));
    /// ```
    pub fn apply<B, C, ApplyFn>(&self, other: StateT<S, M, B>, apply_fn: ApplyFn) -> StateT<S, M, C>
    where
        A: Clone + Send + Sync + 'static,
        B: Clone + Send + Sync + 'static,
        C: Clone + Send + Sync + 'static,
        S: Clone + Send + Sync + 'static,
        M: Clone + Send + Sync + 'static,
        ApplyFn: Fn(M, M) -> M + Send + Sync + 'static,
    {
        match (self, &other) {
            (StateT::Pure(f), StateT::Pure(v)) => {
                let f_clone = f.clone();
                let v_clone = v.clone();
                StateT::new(move |s: S| {
                    let f_state = StateT::Pure(f_clone.clone());
                    let v_state = StateT::Pure(v_clone.clone());
                    let f_result = f_state.run_state(s.clone());
                    let v_result = v_state.run_state(s);
                    apply_fn(f_result, v_result)
                })
            },
            (StateT::LiftM(m1), StateT::LiftM(m2)) => {
                StateT::LiftM(apply_fn(m1.clone(), m2.clone()))
            },
            (StateT::Effect(self_run), StateT::Effect(other_run)) => {
                let self_run = Arc::clone(self_run);
                let other_run = Arc::clone(other_run);

                StateT::new(move |s: S| apply_fn(self_run(s.clone()), other_run(s)))
            },
            _ => {
                let self_run = match self {
                    StateT::Pure(_) | StateT::LiftM(_) => {
                        let self_clone = self.clone();
                        Arc::new(move |s: S| self_clone.run_state(s))
                            as Arc<dyn Fn(S) -> M + Send + Sync>
                    },
                    StateT::Effect(run) => Arc::clone(run),
                };

                let other_run = match &other {
                    StateT::Pure(_) | StateT::LiftM(_) => {
                        let other_clone = other.clone();
                        Arc::new(move |s: S| other_clone.run_state(s))
                            as Arc<dyn Fn(S) -> M + Send + Sync>
                    },
                    StateT::Effect(run) => Arc::clone(run),
                };

                StateT::new(move |s: S| apply_fn(self_run(s.clone()), other_run(s)))
            },
        }
    }

    /// Joins a nested StateT structure, flattening it to a single level.
    ///
    /// This is useful when working with operations that return StateT instances
    /// inside StateT, allowing you to flatten the nested structure.
    ///
    /// # Parameters
    ///
    /// * `join_fn` - Function that knows how to join/flatten the base monad
    ///
    /// # Returns
    ///
    /// A flattened StateT instance
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::transformers::StateT;
    ///
    /// // Create a nested StateT (StateT inside StateT)
    /// let nested: StateT<i32, Option<(i32, StateT<i32, Option<(i32, i32)>, i32>)>, StateT<i32, Option<(i32, i32)>, i32>> =
    ///     StateT::new(|s: i32| {
    ///         let inner = StateT::new(move |inner_s: i32| {
    ///             Some((inner_s * 2, inner_s + s))
    ///         });
    ///         Some((s + 1, inner))
    ///     });
    ///
    /// // Flatten the structure
    /// let flattened = nested.join(|m| {
    ///     m.and_then(|(outer_s, inner_state_t)| {
    ///         inner_state_t.run_state(outer_s)
    ///     })
    /// });
    ///
    /// // Run the flattened computation
    /// // With initial state 10:
    /// // 1. outer: (11, inner_state_t)
    /// // 2. inner_state_t with state 11: (22, 21)
    /// assert_eq!(flattened.run_state(10), Some((22, 21)));
    /// ```
    pub fn join<JoinFn, OuterM>(&self, join_fn: JoinFn) -> StateT<S, OuterM, A>
    where
        A: Clone + Send + Sync + 'static,
        M: Clone + 'static,
        JoinFn: Fn(M) -> OuterM + Send + Sync + 'static,
        OuterM: 'static,
    {
        match self {
            StateT::Pure(inner_state_t) => StateT::Pure(inner_state_t.clone()),
            StateT::LiftM(m) => StateT::LiftM(join_fn(m.clone())),
            StateT::Effect(run_fn) => {
                let run_fn = Arc::clone(run_fn);
                StateT::new(move |s: S| join_fn(run_fn(s)))
            },
        }
    }
}

impl<S, M, A> MonadTransformer for StateT<S, M, A>
where
    S: Clone + Send + Sync + 'static,
    M: Monad<Source = (S, A)> + Send + Sync + Clone + 'static,
    A: Clone + Send + Sync + 'static,
{
    type BaseMonad = M;

    #[inline]
    fn lift(base: M) -> Self {
        StateT::new(move |_: S| base.clone())
    }
}

impl<S, E, A> StateT<S, Result<(S, A), E>, A>
where
    S: Clone + 'static,
    E: 'static,
    A: Send + Sync + 'static,
{
    /// Runs the state transformer and converts errors to AppError for standardized error handling.
    ///
    /// This method executes the state transformer with the given initial state and converts
    /// any errors to the standardized AppError type, providing consistent error handling
    /// across the library.
    ///
    /// # Parameters
    ///
    /// * `state` - Initial state
    ///
    /// # Returns
    ///
    /// Result containing either the state-value pair or an AppError
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::transformers::StateT;
    /// use rustica::utils::error_utils::AppError;
    ///
    /// // Create a StateT that may fail with division
    /// let safe_div: StateT<i32, Result<(i32, i32), String>, i32> = StateT::new(|s: i32| {
    ///     if s == 0 {
    ///         Err("Division by zero".to_string())
    ///     } else {
    ///         Ok((s, 100 / s))
    ///     }
    /// });
    ///
    /// // Convert regular errors to AppError
    /// let result = safe_div.try_run_state(4);
    /// assert!(result.is_ok());
    /// assert_eq!(result.unwrap(), (4, 25)); // 100/4 = 25
    ///
    /// // With error
    /// let result = safe_div.try_run_state(0);
    /// assert!(result.is_err());
    /// assert_eq!(result.unwrap_err().message(), &"Division by zero");
    /// ```
    pub fn try_run_state(&self, state: S) -> Result<(S, A), AppError<E>>
    where
        A: Clone,
        E: Clone,
    {
        match self {
            StateT::Pure(_) => panic!("Cannot run Pure StateT without proper context"),
            StateT::LiftM(result) => match result.as_ref() {
                Ok((s, a)) => Ok((s.clone(), a.clone())),
                Err(e) => Err(AppError::new(e.clone())),
            },
            StateT::Effect(run_fn) => run_fn(state).map_err(AppError::new),
        }
    }

    /// Runs the state transformer with context information for better error reporting.
    ///
    /// This method is similar to `try_run_state` but allows for adding context to the error,
    /// which can provide more information about what was happening when the error occurred.
    ///
    /// # Parameters
    ///
    /// * `state` - Initial state
    /// * `context` - Context information to include with errors
    ///
    /// # Returns
    ///
    /// Result containing either the state-value pair or an AppError with context
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::transformers::StateT;
    /// use rustica::utils::error_utils::AppError;
    ///
    /// // Create a StateT that may fail with division
    /// let safe_div: StateT<i32, Result<(i32, i32), String>, i32> = StateT::new(|s: i32| {
    ///     if s == 0 {
    ///         Err("Division by zero".to_string())
    ///     } else {
    ///         Ok((s, 100 / s))
    ///     }
    /// });
    ///
    /// // Run with context
    /// let result = safe_div.try_run_state_with_context(4, "processing user input");
    /// assert!(result.is_ok());
    /// assert_eq!(result.unwrap(), (4, 25)); // 100/4 = 25
    ///
    /// // With error and context
    /// let result = safe_div.try_run_state_with_context(0, "processing user input");
    /// assert!(result.is_err());
    /// let error = result.unwrap_err();
    /// assert_eq!(error.message(), &"Division by zero");
    /// assert_eq!(error.context(), Some(&"processing user input"));
    /// ```
    pub fn try_run_state_with_context<C>(
        &self, state: S, context: C,
    ) -> Result<(S, A), AppError<E, C>>
    where
        C: Clone + 'static,
        A: Clone,
        E: Clone,
    {
        match self {
            StateT::Pure(_) => panic!("Cannot run Pure StateT without proper context"),
            StateT::LiftM(result) => match result.as_ref() {
                Ok((s, a)) => Ok((s.clone(), a.clone())),
                Err(e) => Err(AppError::with_context(e.clone(), context)),
            },
            StateT::Effect(run_fn) => run_fn(state).map_err(|e| AppError::with_context(e, context)),
        }
    }

    /// Maps a function over the error contained in this StateT.
    ///
    /// This method transforms the error type of the StateT, allowing for conversion
    /// between different error types while preserving the structure of the StateT.
    ///
    /// # Parameters
    ///
    /// * `f` - Function to apply to the error
    ///
    /// # Returns
    ///
    /// A new StateT with the mapped error
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::transformers::StateT;
    ///
    /// // Create a StateT with a string error
    /// let state_t: StateT<i32, Result<(i32, i32), String>, i32> = StateT::new(|s: i32| {
    ///     if s == 0 {
    ///         Err("Division by zero".to_string())
    ///     } else {
    ///         Ok((s, 100 / s))
    ///     }
    /// });
    ///
    /// // Map the error to a different type
    /// let mapped = state_t.map_error(|e: String| e.len() as i32);
    ///
    /// // Now the error is an i32 (the length of the original error string)
    /// let result = mapped.run_state(0);
    /// assert_eq!(result, Err(16)); // "Division by zero" has length 16
    /// ```
    pub fn map_error<F, E2>(&self, f: F) -> StateT<S, Result<(S, A), E2>, A>
    where
        F: Fn(E) -> E2 + Send + Sync + 'static,
        E2: 'static,
        A: Clone,
        E: Clone,
    {
        match self {
            StateT::Pure(a) => StateT::Pure(a.clone()),
            StateT::LiftM(result) => {
                let mapped_result = match result.as_ref() {
                    Ok((s, a)) => Ok((s.clone(), a.clone())),
                    Err(e) => Err(f(e.clone())),
                };
                StateT::LiftM(mapped_result)
            },
            StateT::Effect(run_fn) => {
                let run_fn = Arc::clone(run_fn);
                StateT::new(move |s: S| run_fn(s).map_err(&f))
            },
        }
    }

    /// Runs the state transformer and returns only the value as a Result with AppError.
    ///
    /// This method is similar to `try_run_state` but discards the final state and
    /// only returns the computed value.
    ///
    /// # Parameters
    ///
    /// * `state` - Initial state
    ///
    /// # Returns
    ///
    /// Result containing either the computed value or an AppError
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::transformers::StateT;
    /// use rustica::utils::error_utils::AppError;
    ///
    /// let safe_div: StateT<i32, Result<(i32, i32), String>, i32> = StateT::new(|s: i32| {
    ///     if s == 0 {
    ///         Err("Division by zero".to_string())
    ///     } else {
    ///         Ok((s, 100 / s))
    ///     }
    /// });
    ///
    /// let result = safe_div.try_eval_state(4);
    /// assert_eq!(result, Ok(25)); // 100/4 = 25
    ///
    /// let result = safe_div.try_eval_state(0);
    /// assert!(result.is_err());
    /// assert_eq!(result.unwrap_err().message(), &"Division by zero");
    /// ```
    pub fn try_eval_state(&self, state: S) -> Result<A, AppError<E>>
    where
        A: Clone,
        E: Clone,
    {
        self.try_run_state(state).map(|(_, a)| a)
    }

    /// Runs the state transformer with context and returns only the value as a Result with AppError.
    ///
    /// This method is similar to `try_run_state_with_context` but discards the final state
    /// and only returns the computed value.
    ///
    /// # Parameters
    ///
    /// * `state` - Initial state
    /// * `context` - Context information to include with errors
    ///
    /// # Returns
    ///
    /// Result containing either the computed value or an AppError with context
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::transformers::StateT;
    /// use rustica::utils::error_utils::AppError;
    ///
    /// let safe_div: StateT<i32, Result<(i32, i32), String>, i32> = StateT::new(|s: i32| {
    ///     if s == 0 {
    ///         Err("Division by zero".to_string())
    ///     } else {
    ///         Ok((s, 100 / s))
    ///     }
    /// });
    ///
    /// let result = safe_div.try_eval_state_with_context(4, "processing user input");
    /// assert_eq!(result, Ok(25)); // 100/4 = 25
    ///
    /// let result = safe_div.try_eval_state_with_context(0, "processing user input");
    /// assert!(result.is_err());
    /// let error = result.unwrap_err();
    /// assert_eq!(error.message(), &"Division by zero");
    /// assert_eq!(error.context(), Some(&"processing user input"));
    /// ```
    pub fn try_eval_state_with_context<C>(&self, state: S, context: C) -> Result<A, AppError<E, C>>
    where
        C: Clone + 'static,
        A: Clone,
        E: Clone,
    {
        self.try_run_state_with_context(state, context)
            .map(|(_, a)| a)
    }

    /// Runs the state transformer and returns only the final state as a Result with AppError.
    ///
    /// This method is similar to `try_run_state` but discards the computed value and
    /// only returns the final state.
    ///
    /// # Parameters
    ///
    /// * `state` - Initial state
    ///
    /// # Returns
    ///
    /// Result containing either the final state or an AppError
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::transformers::StateT;
    /// use rustica::utils::error_utils::AppError;
    ///
    /// let safe_div: StateT<i32, Result<(i32, i32), String>, i32> = StateT::new(|s: i32| {
    ///     if s == 0 {
    ///         Err("Division by zero".to_string())
    ///     } else {
    ///         Ok((s + 1, 100 / s))
    ///     }
    /// });
    ///
    /// let result = safe_div.try_exec_state(4);
    /// assert_eq!(result, Ok(5)); // initial state 4 + 1 = 5
    ///
    /// let result = safe_div.try_exec_state(0);
    /// assert!(result.is_err());
    /// assert_eq!(result.unwrap_err().message(), &"Division by zero");
    /// ```
    pub fn try_exec_state(&self, state: S) -> Result<S, AppError<E>>
    where
        A: Clone,
        E: Clone,
    {
        self.try_run_state(state).map(|(s, _)| s)
    }
}

use crate::datatypes::id::Id;
use crate::traits::identity::Identity;

impl<S, A> StateT<S, Id<(S, A)>, A>
where
    S: Clone + Send + Sync + 'static,
    A: Clone + Send + Sync + 'static,
{
    /// Converts this `StateT<S, Id<(S, A)>, A>` into a `State<S, A>`.
    ///
    /// This method allows you to convert a state transformer with the identity monad as its base
    /// back into a regular `State` monad. This is useful when you want to drop the transformer
    /// context and work with the simpler state monad.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::transformers::StateT;
    /// use rustica::datatypes::id::Id;
    /// use rustica::datatypes::state::State;
    ///
    /// // Create a StateT with Id as the monad
    /// let state_t: StateT<i32, Id<(i32, i32)>, i32> = StateT::new(|s: i32| {
    ///     Id::new((s * 2, s + 1))
    /// });
    ///
    /// // Convert to State
    /// let state: State<i32, i32> = state_t.to_state();
    ///
    /// // The behavior should be identical
    /// assert_eq!(state.run_state(21), (22, 42));
    /// ```
    pub fn to_state(self) -> crate::datatypes::state::State<S, A> {
        crate::datatypes::state::State::new(move |s: S| {
            let result = self.run_state(s.clone());
            let (new_state, value) = result.value().clone();
            (value, new_state)
        })
    }

    /// Converts a `State<S, A>` into a `StateT<S, Id<(S, A)>, A>`.
    ///
    /// This method allows you to lift a regular state monad into the transformer context
    /// with the identity monad as the base. This is useful for composing stateful computations
    /// with other monad transformers.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::state::State;
    /// use rustica::datatypes::id::Id;
    /// use rustica::traits::identity::Identity;
    /// use rustica::transformers::StateT;
    ///
    /// // Create a State
    /// let state = State::new(|s: i32| (s * 2, s + 1));
    ///
    /// // Convert to StateT
    /// let state_t: StateT<i32, Id<(i32, i32)>, i32> = StateT::from_state(state);
    ///
    /// // The behavior should be identical
    /// assert_eq!(state_t.run_state(21).value(), &(22, 42));
    /// ```
    pub fn from_state(state: crate::datatypes::state::State<S, A>) -> Self {
        StateT::new(move |s: S| {
            let (a, s2) = state.run_state(s);
            Id::new((s2, a))
        })
    }
}
