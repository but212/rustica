//! # State Monad
//!
//! The State monad represents computations that can read and modify state in a purely functional way.
//! It encapsulates a function that takes a state and returns a value along with a new state.
//!
//! ## Functional Programming Context
//!
//! In functional programming, the State monad provides a principled way to work with stateful computations
//! while maintaining referential transparency. It is a foundational abstraction for handling state in
//! pure functional programming languages and libraries.
//!
//! The State monad can be understood as:
//!
//! - **A Functional Alternative to Mutable Variables**: Instead of modifying variables in place, the State monad
//!   models state transitions as pure functions that produce new states.
//! - **Sequential State Transformer**: State enables chaining operations where each step depends on and potentially
//!   modifies the state from previous steps.
//! - **Encapsulation of Effects**: State is part of the broader category of effect systems in functional programming
//!   that make side effects explicit in the type system.
//!
//! Similar constructs in other functional languages include:
//!
//! - **Haskell**: `Control.Monad.State` and `StateT` transformer
//! - **Scala**: `cats.data.State` and `scalaz.State`
//! - **PureScript**: `Control.Monad.State`
//! - **Kotlin**: `arrow.mtl.State` from Arrow library
//!
//! ## Core Concepts
//!
//! - **Stateful Computation**: State allows you to model computations that depend on and may modify some state.
//! - **Pure Functional State**: Unlike imperative programming where state is modified as a side effect,
//!   the State monad makes state transformations explicit and composable.
//! - **Sequential Operations**: State operations can be chained together, with each operation
//!   receiving the state produced by the previous operation.
//!
//! ## Performance Characteristics
//!
//! ### Time Complexity
//!
//! - **Construction (new/pure)**: O(1) - Constant time to create a State instance
//! - **run_state**: O(n) - Where n is the complexity of the wrapped function
//! - **eval_state/exec_state**: O(n) - Same as run_state but returning only part of the result
//! - **fmap**: O(n) - Where n is the complexity of the wrapped function plus the mapping function
//! - **bind**: O(m + n) - Where m is the complexity of the first computation and n is the complexity of the second
//!
//! ### Memory Usage
//!
//! - **Structure**: Minimal - Stores only a function pointer and does not allocate memory itself
//! - **Laziness**: State operations are lazy - they only execute when `run_state`, `eval_state`, or `exec_state` is called
//! - **Composition**: Each composition creates a new function wrapper but defers execution
//! - **Cloning**: O(1) for the State monad itself, as it uses Arc for internal sharing
//!
//! ## Use Cases
//!
//! State is particularly useful in scenarios such as:
//!
//! - **Stateful Algorithms**: Implementing algorithms that need to track and update state
//! - **Parsing**: Building parsers that consume input and maintain parsing state
//! - **Game Logic**: Managing game state transitions without mutable variables
//! - **Simulations**: Modeling step-by-step simulations with changing state
//!
//! ## Type Class Implementations
//!
//! The State monad implements several important functional programming type classes:
//!
//! - **Functor**: State implements the Functor type class through its `fmap` method, which allows
//!   transforming the values inside the State context while preserving the state transitions.
//!   - Implementation: `fmap :: (A -> B) -> State<S, A> -> State<S, B>`
//!
//! - **Applicative**: State implements the Applicative type class through its `pure` and `apply` methods:
//!   - `pure`: Creates a State that returns the provided value without modifying the state
//!     - Implementation: `pure :: A -> State<S, A>`
//!   - `apply`: Applies a function inside a State to a value inside another State
//!     - Implementation: `apply :: State<S, (A -> B)> -> State<S, A> -> State<S, B>`
//!
//! - **Monad**: State implements the Monad type class through its `bind` method, enabling sequential
//!   composition of stateful computations where each computation can depend on the result of the previous.
//!   - Implementation: `bind :: State<S, A> -> (A -> State<S, B>) -> State<S, B>`
//!
//! - **MonadState**: State implements the MonadState type class through the utility functions:
//!   - `get`: Retrieves the current state without modification
//!   - `put`: Replaces the current state and returns unit
//!   - `modify`: Updates the state using a provided function
//!
//! ## Type Class Laws
//!
//! The `State` type implements the following type class laws. See the documentation for
//! the specific functions (`fmap`, `bind`) for examples demonstrating these laws.
//!
//! ### Functor Laws
//!
//! The `State` type satisfies the functor laws:
//!
//! 1. **Identity Law**: `fmap(id) = id`
//!    - Mapping the identity function over a `State` returns a `State` that produces the same result when run.
//!
//! 2. **Composition Law**: `fmap(f . g) = fmap(f) . fmap(g)`
//!    - Mapping a composed function is the same as mapping each function in sequence.
//!
//! ### Monad Laws
//!
//! The `State` type satisfies the monad laws:
//!
//! 1. **Left Identity**: `return a >>= f = f a`
//!    - Binding a function to a pure value is the same as applying the function directly.
//!
//! 2. **Right Identity**: `m >>= return = m`
//!    - Binding the pure function to a monad returns the original monad.
//!
//! 3. **Associativity**: `(m >>= f) >>= g = m >>= (\x -> f x >>= g)`
//!    - Sequential binds can be nested in either direction with the same result.
//!
//! ## Examples
//!
//! ### Basic Usage
//!
//! ```rust
//! use rustica::datatypes::state::State;
//!
//! // A simple counter that returns the current state and increments it
//! let counter = State::new(|s: i32| (s, s + 1));
//!
//! // Run the state computation with initial state 0
//! assert_eq!(counter.run_state(0), (0, 1));
//!
//! // Run it again with a different initial state
//! assert_eq!(counter.run_state(10), (10, 11));
//! ```
//!
//! ### Chaining State Operations
//!
//! ```rust
//! use rustica::datatypes::state::State;
//! use rustica::datatypes::state::{get, put, modify};
//!
//! // Define a sequence of state operations
//! let computation = get::<i32>()                     // Get the current state
//!     .bind(|x| modify(move |s: i32| s + x)          // Modify state by adding its current value
//!         .bind(|_| get::<i32>()                     // Get the new state
//!             .bind(|y| put(y * 2)                   // Double the state
//!                 .bind(move |_| State::pure(y)))));      // Return the previous state value
//!
//! // Run the computation with initial state 2
//! // 1. get() returns (2, 2)
//! // 2. modify(|s| s + x) changes state to 4 (2 + 2)
//! // 3. get() returns (4, 4)
//! // 4. put(y * 2) changes state to 8 (4 * 2)
//! // 5. State::pure(y) returns the value 4 with state 8
//! assert_eq!(computation.run_state(2), (4, 8));
//! ```
//!
//! ### Implementing a Stack with State
//!
//! ```rust
//! use rustica::datatypes::state::State;
//!
//! // Define stack operations
//! fn push<T: Send + Sync + Clone + 'static>(x: T) -> State<Vec<T>, ()> {
//!     State::new(move |mut stack: Vec<T>| {
//!         stack.push(x.clone());
//!         ((), stack)
//!     })
//! }
//!
//! fn pop<T: Send + Sync + Clone + 'static>() -> State<Vec<T>, Option<T>> {
//!     State::new(|mut stack: Vec<T>| {
//!         let item = stack.pop();
//!         (item, stack)
//!     })
//! }
//!
//! // Use the stack operations in a sequence
//! let stack_ops = push(1)
//!     .bind(|_| push(2))
//!     .bind(|_| push(3))
//!     .bind(|_| pop::<i32>())
//!     .bind(|x| pop::<i32>().bind(move |y| State::pure((x, y))));
//!
//! // Run the stack operations with an empty stack
//! // After pushing 1, 2, 3 and popping twice, we get the values 3 and 2
//! // The final stack contains just [1]
//! assert_eq!(stack_ops.run_state(Vec::new()), ((Some(3), Some(2)), vec![1]));
//! ```
//!
use crate::datatypes::id::Id;
use crate::traits::hkt::HKT;
use crate::traits::identity::Identity;
use crate::transformers::StateT;
use crate::utils::error_utils::AppError;
#[cfg(feature = "full")]
use quickcheck::{Arbitrary, Gen};

/// A monad that represents stateful computations.
///
/// The State monad provides a way to handle state in a purely functional way.
/// It encapsulates a function that takes a state and returns a tuple
/// containing a value and a new state.
///
/// # Performance Characteristics
///
/// ## Time Complexity
///
/// * **Construction**: O(1) - Creating a State instance is a constant-time operation
/// * **run_state**: O(n) - Where n is the complexity of the wrapped function
/// * **fmap/bind**: O(1) for the operation itself, but the resulting State will have O(m+n) execution time
///   where m is the complexity of the original function and n is the complexity of the mapped/bound function
///
/// ## Memory Usage
///
/// * **Structure**: Minimal - Uses a function pointer wrapped in Arc for thread safety
/// * **Cloning**: O(1) - Internally uses Arc for efficient cloning with shared ownership
/// * **Composition**: Each composition (fmap/bind) creates a new wrapper function but defers execution
///
/// # Functional Programming Context
///
/// The `new` constructor is the primary way to create custom State computations.
/// While utility functions like `get`, `put`, and `modify` cover common use cases,
/// `new` allows you to define arbitrary state transformations with full control
/// over both the returned value and the state transition.
///
/// # Implementation Details
///
/// The State monad is implemented as a wrapper around a function `S -> (A, S)` where:
/// - `S` is the type of the state
/// - `A` is the type of the value being computed
/// - The function takes a state and returns both a value and a new state
///
/// # Type Class Laws
///
/// State satisfies the following laws:
///
/// ## Functor Laws
///
/// 1. **Identity**: `fmap(id, state) = state`
/// 2. **Composition**: `fmap(f . g, state) = fmap(f, fmap(g, state))`
///
/// ## Monad Laws
///
/// 1. **Left Identity**: `pure(a).bind(f) = f(a)`
/// 2. **Right Identity**: `state.bind(pure) = state`
/// 3. **Associativity**: `state.bind(f).bind(g) = state.bind(x => f(x).bind(g))`
///
/// # Thread Safety
///
/// The State monad is thread-safe and can be safely shared across threads when the state
/// and value types implement `Send + Sync`. The implementation uses Arc internally to enable
/// safe sharing.
///
/// # Type Parameters
///
/// * `S`: The type of the state
/// * `A`: The type of the value being computed
///
/// # Examples
///
/// ```rust
/// use rustica::datatypes::state::State;
///
/// // A simple state computation that doubles the state and returns the original
/// let counter = State::new(|s: i32| (s, s * 2));
/// assert_eq!(counter.run_state(5), (5, 10));
///
/// // Chain multiple state operations
/// let double_counter = counter.bind(|x| {
///     State::new(move |s| (x + s, s + 1))
/// });
/// assert_eq!(double_counter.run_state(0), (0, 1));
///
/// // Using State for a more complex computation
/// let computation = State::new(|s: i32| (s * 2, s))
///     .bind(|x| State::new(move |s| (x + s, s + 1)))
///     .bind(|x| State::new(move |s| (format!("Result: {}", x), s * 2)));
///
/// // When run with initial state 3:
/// // 1. First computation returns (6, 3)
/// // 2. Second computation returns (6 + 3, 3 + 1) = (9, 4)
/// // 3. Third computation returns ("Result: 9", 4 * 2) = ("Result: 9", 8)
/// assert_eq!(computation.run_state(3), ("Result: 9".to_string(), 8));
///
/// // Verifying functor identity law
/// let state = State::new(|s: i32| (s + 1, s * 2));
/// let identity = |x| x;
/// let mapped = state.clone().fmap(identity);
/// assert_eq!(state.run_state(5), mapped.run_state(5));
/// ```
#[repr(transparent)]
pub struct State<S, A> {
    /// The state transformation function
    inner: StateT<S, Id<(A, S)>, A>,
}

impl<S: Clone + Send + Sync + 'static, A: Clone + Send + Sync + 'static> Clone for State<S, A> {
    #[inline]
    fn clone(&self) -> Self {
        State {
            inner: self.inner.clone(),
        }
    }
}

impl<S, A> State<S, A>
where
    S: Clone + Send + Sync + 'static,
    A: Clone + Send + Sync + 'static,
{
    /// Creates a new State monad.
    ///
    /// This constructor creates a new State monad that wraps the provided state
    /// transformation function. The function takes a state and returns a tuple
    /// containing a value and a new state.
    ///
    /// # Performance Characteristics
    ///
    /// ## Time Complexity
    ///
    /// * **Construction**: O(1) - Creating the State instance is a constant-time operation
    /// * **Execution**: O(n) - Where n is the complexity of the wrapped function when run_state is called
    ///
    /// ## Memory Usage
    ///
    /// * **Structure**: Minimal - Stores only the function pointer wrapped in Arc
    /// * **Thread Safety**: Safe to share across threads when the state and value types implement `Send + Sync`
    /// * **Composition**: Zero overhead until executed - State monad is lazily evaluated
    ///
    /// # State Monad Context
    ///
    /// The `new` constructor is the primary way to create custom State computations.
    /// While utility functions like `get`, `put`, and `modify` cover common use cases,
    /// `new` allows you to define arbitrary state transformations with full control
    /// over both the returned value and the state transition.
    ///
    /// # Arguments
    ///
    /// * `run` - Function that takes a state and returns a tuple of value and new state
    ///
    /// # Type Parameters
    ///
    /// * `S`: The type of the state
    /// * `A`: The type of the value being computed
    /// * `F`: The type of the function
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::state::State;
    ///
    /// // Create a state computation that returns the state as the value and increments the state
    /// let counter = State::new(|s: i32| (s, s + 1));
    /// assert_eq!(counter.run_state(5), (5, 6));
    /// ```
    #[inline]
    pub fn new<F>(f: F) -> Self
    where
        F: Fn(S) -> (A, S) + Send + Sync + 'static,
    {
        State {
            inner: StateT::new(move |s: S| Id::new(f(s))),
        }
    }

    /// Runs the state computation with an initial state.
    ///
    /// This is the primary method for executing a State computation. It applies the
    /// state transformation function to the provided initial state and returns both
    /// the computed value and the final state.
    ///
    /// # Performance Characteristics
    ///
    /// ## Time Complexity
    ///
    /// * **Execution**: O(n) - Where n is the complexity of the wrapped function
    /// * **For Composed States**: O(m + n + ...) - Sum of complexities of all composed functions
    ///
    /// ## Memory Usage
    ///
    /// * **Stack Usage**: Proportional to the depth of nested function calls in composed State monads
    /// * **Heap Usage**: Depends on the state and value types and what transformations occur
    ///
    /// # State Monad Context
    ///
    /// The `run_state` operation is the entry point for state computations, allowing
    /// you to provide an initial state and retrieve both the result and the final state.
    /// In the context of the State monad laws, `run_state` is what makes the abstract
    /// computation concrete and observable.
    ///
    /// # Arguments
    ///
    /// * `s` - The initial state
    ///
    /// # Returns
    ///
    /// A tuple containing the computed value and the final state.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::state::State;
    ///
    /// // A simple state computation that doubles the state and returns the original
    /// let counter = State::new(|s: i32| (s, s * 2));
    ///
    /// // Run with initial state 5
    /// assert_eq!(counter.run_state(5), (5, 10));
    ///
    /// // Run with a different initial state
    /// assert_eq!(counter.run_state(21), (21, 42));
    /// ```
    #[inline]
    pub fn run_state(&self, s: S) -> (A, S) {
        // Direct mapping from Id monad's value
        self.inner.run_state(s).value().clone()
    }

    /// Runs the state computation and returns only the final value.
    ///
    /// This method is similar to `run_state`, but it discards the final state and
    /// only returns the computed value. This is useful when you're only interested
    /// in the result of the computation, not the state changes.
    ///
    /// # State Monad Context
    ///
    /// The `eval_state` operation is commonly used when the state is just a means to
    /// an end, and the final value is what matters for the computation.
    ///
    /// # Arguments
    ///
    /// * `s` - The initial state
    ///
    /// # Returns
    ///
    /// The computed value, discarding the final state.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::state::State;
    /// use rustica::datatypes::state::{get, put, modify};
    ///
    /// // A state computation that returns the state multiplied by 2
    /// let counter = State::new(|s: i32| (s * 2, s + 1));
    ///
    /// // Only get the value, not the state
    /// assert_eq!(counter.eval_state(5), 10);
    ///
    /// // Useful for computations where the state is just a means to calculate a result
    /// let fibonacci = get::<(u32, u32)>()
    ///     .bind(|(a, b)| {
    ///         put((b, a + b))
    ///             .bind(move |_| State::pure(a))
    ///     });
    ///
    /// // Calculate the first 10 Fibonacci numbers
    /// let mut results = Vec::new();
    /// let mut state = (0, 1); // Initial state (F_0, F_1)
    ///
    /// for _ in 0..10 {
    ///     let value = fibonacci.eval_state(state.clone());
    ///     results.push(value);
    ///     state = fibonacci.exec_state(state); // Update state for next iteration
    /// }
    ///
    /// assert_eq!(results, vec![0, 1, 1, 2, 3, 5, 8, 13, 21, 34]);
    /// ```
    #[inline]
    pub fn eval_state(&self, s: S) -> A {
        self.run_state(s).0
    }

    /// Runs the state computation and returns only the final state.
    ///
    /// This method is similar to `run_state`, but it discards the computed value and
    /// only returns the final state. This is useful when you're only interested in
    /// the state changes, not the computed value.
    ///
    /// # State Monad Context
    ///
    /// The `exec_state` operation is commonly used for side-effecting computations where
    /// the primary goal is to modify the state.
    ///
    /// # Arguments
    ///
    /// * `s` - The initial state
    ///
    /// # Returns
    ///
    /// The final state, discarding the computed value.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::state::State;
    /// use rustica::datatypes::state::{get, put, modify};
    ///
    /// // Define a series of state operations
    /// let add_5 = modify(|s: i32| s + 5);
    /// let multiply_by_2 = modify(|s: i32| s * 2);
    /// let subtract_3 = modify(|s: i32| s - 3);
    ///
    /// // Chain operations together
    /// let apply_operations = vec![add_5, multiply_by_2, subtract_3]
    ///     .into_iter()
    ///     .fold(State::pure(()), |acc, op| acc.bind(move |_| op.clone()));
    ///
    /// // Starting with 0: 0 -> 5 -> 10 -> 7
    /// assert_eq!(apply_operations.exec_state(0), 7);
    /// ```
    #[inline]
    pub fn exec_state(&self, s: S) -> S {
        self.run_state(s).1
    }

    /// Maps a function over the value produced by a state computation.
    ///
    /// This method implements the `fmap` operation from the Functor typeclass in
    /// functional programming. It transforms the value produced by a State computation
    /// without affecting the state transitions.
    ///
    /// # Performance Characteristics
    ///
    /// ## Time Complexity
    ///
    /// * **Construction**: O(1) - Creating the mapped State is a constant-time operation
    /// * **Execution**: O(m + n) - Where m is the complexity of the original state computation
    ///   and n is the complexity of the mapping function
    /// * **Multiple fmaps**: O(1) per fmap construction, but execution combines all transformations
    ///
    /// ## Memory Usage
    ///
    /// * **Lazy Evaluation**: No computation happens until `run_state` is called
    /// * **Composition**: Each `fmap` creates a new function wrapper but defers execution
    /// * **Closure Capture**: The mapping function may capture variables from its environment,
    ///   potentially increasing memory usage
    ///
    /// # Functional Programming Context
    ///
    /// The `fmap` operation (often written as `<$>` or `map` in functional languages)
    /// is the defining operation of the Functor typeclass. It allows you to transform
    /// the values within a context without changing the structure of that context.
    /// For the State monad, this means:
    ///
    /// 1. Running the state computation to get a value and a new state
    /// 2. Applying the function to the value
    /// 3. Returning the transformed value with the same new state
    ///
    ///
    /// # Type Parameters
    ///
    /// * `B`: The type of the value after transformation
    /// * `F`: The type of the function
    ///
    /// # Arguments
    ///
    /// * `f` - Function to apply to the value
    ///
    /// # Returns
    ///
    /// A new State computation that produces the transformed value.
    ///
    /// # Functor Laws
    ///
    /// 1. **Identity Law**: `fmap(id) = id`
    ///    ```rust
    ///    # use rustica::datatypes::state::State;
    ///    let state = State::new(|s: i32| (s * 2, s + 1));
    ///    let id = |x| x;
    ///    assert_eq!(state.clone().fmap(id).run_state(5), state.run_state(5));
    ///    ```
    ///
    /// 2. **Composition Law**: `fmap(f . g) = fmap(f) . fmap(g)`
    ///    ```rust
    ///    # use rustica::datatypes::state::State;
    ///    let state = State::new(|s: i32| (s, s + 1));
    ///    let f = |x: i32| x * 3;
    ///    let g = |x: i32| x + 2;
    ///    
    ///    // fmap(f . g) - composing functions and mapping once
    ///    let composed = state.clone().fmap(move |x| f(g(x)));
    ///    
    ///    // fmap(f) . fmap(g) - mapping twice with individual functions
    ///    let chained = state.clone().fmap(g).fmap(f);
    ///    
    ///    assert_eq!(composed.run_state(10), chained.run_state(10));
    ///    ```
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::state::State;
    ///
    /// // Create a state computation that returns the state and increments it
    /// let counter = State::new(|s: i32| (s, s + 1));
    ///
    /// // Map a function over the value
    /// let doubled = counter.clone().fmap(|x| x * 2);
    /// assert_eq!(doubled.run_state(5), (10, 6));
    /// ```
    #[inline]
    pub fn fmap<B, F>(self, f: F) -> State<S, B>
    where
        B: Clone + Send + Sync + 'static,
        F: Fn(A) -> B + Send + Sync + 'static,
    {
        State::new(move |s| {
            let (a, s) = self.run_state(s);
            (f(a), s)
        })
    }

    /// Chains two state computations together.
    ///
    /// This method implements the `bind` operation (also known as `flatMap` or `>>=`)
    /// from the Monad typeclass in functional programming. It allows you to sequence
    /// state computations where the second computation depends on the value produced
    /// by the first.
    ///
    /// # Functional Programming Context
    ///
    /// The `bind` operation is the defining operation of the Monad typeclass. It enables
    /// sequential composition of computations where each step can depend on the results
    /// of previous steps. For the State monad, this means:
    ///
    /// 1. Running the first computation to get a value and an intermediate state
    /// 2. Using that value to determine which second computation to run
    /// 3. Running the second computation with the intermediate state
    /// 4. Returning the final value and state
    ///
    /// The `bind` operation satisfies important laws:
    /// - Left identity: `pure(a).bind(f) = f(a)`
    /// - Right identity: `m.bind(pure) = m`
    /// - Associativity: `m.bind(f).bind(g) = m.bind(x => f(x).bind(g))`
    ///
    /// # Type Parameters
    ///
    /// * `B`: The type of the value produced by the second computation
    /// * `F`: The type of the function that produces the second computation
    ///
    /// # Arguments
    ///
    /// * `f` - Function that takes the value from the first computation and returns a new State computation
    ///
    /// # Returns
    ///
    /// A new State computation representing the sequential composition of the two computations.
    ///
    /// # Monad Laws
    ///
    /// 1. **Left Identity**: `pure(a).bind(f) = f(a)`
    ///    ```rust
    ///    # use rustica::datatypes::state::State;
    ///    let value = 10;
    ///    let f = |x: i32| State::new(move |s: i32| (x * 2, s + 1));
    ///    
    ///    let left_side = State::pure(value).bind(f.clone());
    ///    let right_side = f(value);
    ///    
    ///    assert_eq!(left_side.run_state(5), right_side.run_state(5));
    ///    ```
    ///
    /// 2. **Right Identity**: `m.bind(pure) = m`
    ///    ```rust
    ///    # use rustica::datatypes::state::State;
    ///    let m = State::new(|s: i32| (s * 3, s + 2));
    ///    let right_side = m.clone().bind(State::pure);
    ///    
    ///    assert_eq!(m.run_state(5), right_side.run_state(5));
    ///    ```
    ///
    /// 3. **Associativity**: `m.bind(f).bind(g) = m.bind(x => f(x).bind(g))`
    ///    ```rust
    ///    # use rustica::datatypes::state::State;
    ///    let m = State::new(|s: i32| (s, s + 1));
    ///    let f = |x: i32| State::new(move |s: i32| (x * 2, s + 5));
    ///    let g = |x: i32| State::new(move |s: i32| (x + 10, s * 2));
    ///    
    ///    let left_side = m.clone().bind(f.clone()).bind(g.clone());
    ///    let right_side = m.clone().bind(move |x| f(x).bind(g.clone()));
    ///    
    ///    assert_eq!(left_side.run_state(3), right_side.run_state(3));
    ///    ```
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::state::State;
    /// use rustica::datatypes::state::{get, put, modify};
    ///
    /// // Create a simple state computation
    /// let counter = State::new(|s: i32| (s, s + 1));
    ///
    /// // Chain with another computation that depends on the value
    /// let computation = counter.bind(|x| {
    ///     if x % 2 == 0 {
    ///         // If value is even, double the state
    ///         State::new(move |s| (format!("Even: {}", x), s * 2))
    ///     } else {
    ///         // If value is odd, add 10 to the state
    ///         State::new(move |s| (format!("Odd: {}", x), s + 10))
    ///     }
    /// });
    ///
    /// // With initial state 4:
    /// // 1. counter returns (4, 5)
    /// // 2. Since 4 is even, the second computation returns ("Even: 4", 5 * 2) = ("Even: 4", 10)
    /// assert_eq!(computation.run_state(4), ("Even: 4".to_string(), 10));
    ///
    /// // With initial state 5:
    /// // 1. counter returns (5, 6)
    /// // 2. Since 5 is odd, the second computation returns ("Odd: 5", 6 + 10) = ("Odd: 5", 16)
    /// assert_eq!(computation.run_state(5), ("Odd: 5".to_string(), 16));
    /// ```
    #[inline]
    pub fn bind<B, F>(self, f: F) -> State<S, B>
    where
        B: Clone + Send + Sync + 'static,
        F: Fn(A) -> State<S, B> + Send + Sync + 'static,
    {
        State::new(move |s| {
            let (a, s) = self.run_state(s);
            f(a).run_state(s)
        })
    }

    /// Lifts a value into the State monad.
    ///
    /// This method creates a State computation that returns the provided value
    /// and leaves the state unchanged. This is the `pure` operation from the
    /// Applicative typeclass in functional programming.
    ///
    /// # Functional Programming Context
    ///
    /// In functional programming, `pure` (also known as `return` in some languages)
    /// is a fundamental operation for the Applicative and Monad typeclasses. It
    /// represents the minimal context that can wrap a value. For the State monad,
    /// this means creating a computation that:
    ///
    /// 1. Returns the provided value
    /// 2. Performs no state modifications
    ///
    /// The `pure` operation satisfies important laws:
    /// - Identity: `pure(id) <*> v = v`
    /// - Homomorphism: `pure(f) <*> pure(x) = pure(f(x))`
    /// - Interchange: `u <*> pure(y) = pure(f => f(y)) <*> u`
    ///
    /// # Arguments
    ///
    /// * `a` - The value to lift into the State monad
    ///
    /// # Returns
    ///
    /// A State computation that returns the provided value and leaves the state unchanged.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::state::State;
    ///
    /// // Create a State computation that always returns 42
    /// let computation = State::pure(42);
    /// assert_eq!(computation.run_state(10), (42, 10));
    /// assert_eq!(computation.run_state(99), (42, 99));
    ///
    /// // pure preserves the state regardless of its type
    /// let string_computation = State::pure("hello");
    /// assert_eq!(string_computation.run_state(true), ("hello", true));
    ///
    /// // Use pure as part of a more complex computation
    /// let complex = State::new(|s: i32| (s * 2, s))
    ///     .bind(|_| State::pure("Calculation complete"));
    /// ```
    #[inline]
    pub fn pure(a: A) -> Self {
        State::new(move |s| (a.clone(), s))
    }

    /// Applies a state computation containing a function to another state computation.
    ///
    /// This method implements the `apply` operation from the Applicative typeclass in
    /// functional programming. It allows you to apply a function wrapped in a State context
    /// to a value wrapped in a State context, resulting in a new State computation.
    ///
    /// # Functional Programming Context
    ///
    /// The `apply` operation (often written as `<*>` in functional languages) is a key
    /// component of the Applicative typeclass. It enables function application within
    /// computational contexts. For the State monad, this means:
    ///
    /// 1. Running the first computation to get a function and an intermediate state
    /// 2. Running the second computation with that intermediate state to get a value
    /// 3. Applying the function to the value
    /// 4. Returning the result with the final state
    ///
    /// # Type Parameters
    ///
    /// * `B`: The type of the value that results from applying the function
    /// * `F`: The type of the function contained in `self`
    ///
    /// # Arguments
    ///
    /// * `other` - A State computation containing the value to apply the function to
    ///
    /// # Returns
    ///
    /// A new State computation containing the result of applying the function to the value.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::state::State;
    ///
    /// // Create a State computation containing a function
    /// let add_one = State::pure(|x: i32| x + 1);
    ///
    /// // Create a State computation containing a value
    /// let value = State::pure(41);
    ///
    /// // Apply the function to the value
    /// let result = add_one.apply(value);
    /// assert_eq!(result.run_state(0), (42, 0));
    ///
    /// // Using apply with state transformations
    /// let add_state = State::new(|state: i32| (move |x: i32| x + state, state + 1));
    /// let value = State::new(|s: i32| (s * 2, s + 2));
    ///
    /// // When run with initial state 5:
    /// // 1. add_state returns (|x| x + 5, 6)
    /// // 2. value runs with state 6 and returns (12, 8)
    /// // 3. The function |x| x + 5 is applied to 12, resulting in 17
    /// // 4. Final result is (17, 8)
    /// let result = add_state.apply(value);
    /// assert_eq!(result.run_state(5), (17, 8));
    /// ```
    pub fn apply<B, C>(self, other: State<S, B>) -> State<S, C>
    where
        B: Clone + Send + Sync + 'static,
        C: Clone + Send + Sync + 'static,
        A: Fn(B) -> C + Clone + Send + Sync + 'static,
    {
        State::new(move |s| {
            let (f, s1) = self.run_state(s);
            let (a, s2) = other.run_state(s1);
            (f(a), s2)
        })
    }

    /// Executes the state computation with a pure value.
    ///
    /// This method runs the state computation and returns only the final state,
    /// discarding the computed value. It is the State equivalent of `StateT::exec_pure`.
    ///
    /// # Parameters
    ///
    /// * `s` - The initial state
    ///
    /// # Returns
    ///
    /// The final state after running the computation
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::state::State;
    ///
    /// // Create a state that modifies the state but returns a value
    /// let state = State::new(|s: i32| (s * 2, s + 1));
    ///
    /// // Run and extract only the state
    /// let result = state.exec_pure(42);
    /// assert_eq!(result, 43); // Only the state (42 + 1) is returned
    /// ```
    pub fn exec_pure(&self, s: S) -> S {
        self.exec_state(s)
    }
}

impl<S, A> HKT for State<S, A> {
    type Source = A;
    type Output<T> = State<S, T>;
}

/// Returns the current state.
///
/// This function creates a State computation that returns the current state as its value
/// and leaves the state unchanged.
///
/// # State Monad Context
///
/// The `get` operation is a fundamental building block for State computations. It allows
/// you to access the current state without modifying it, which can then be used to make
/// decisions or compute new values.
///
/// # Type Parameters
///
/// * `S`: The type of the state
///
/// # Returns
///
/// A State computation that returns the current state as its value.
///
/// # Examples
///
/// ```rust
/// use rustica::datatypes::state::{State, get, put, modify};
///
/// // Get the current state and return it as the value
/// let computation = get::<i32>();
/// assert_eq!(computation.run_state(42), (42, 42));
///
/// // Use get to access the state for a calculation
/// let double_state = get::<i32>().bind(|s| State::pure(s * 2));
/// assert_eq!(double_state.run_state(21), (42, 21));
/// ```
#[inline]
pub fn get<S>() -> State<S, S>
where
    S: Clone + Send + Sync + 'static,
{
    State::new(|s: S| (s.clone(), s))
}

/// Sets the state to a new value.
///
/// This function creates a State computation that updates the state to a new value
/// and returns unit `()` as its value.
///
/// # State Monad Context
///
/// The `put` operation is a fundamental building block for State computations. It allows
/// you to replace the current state with a new one, enabling state transitions in a
/// purely functional way.
///
/// # Arguments
///
/// * `s`: The new state
///
/// # Type Parameters
///
/// * `S`: The type of the state
///
/// # Returns
///
/// A State computation that updates the state and returns unit `()`.
///
/// # Examples
///
/// ```rust
/// use rustica::datatypes::state::{State, get, put, modify};
///
/// // Set the state to 42
/// let computation = put(42);
/// assert_eq!(computation.run_state(0), ((), 42));
///
/// // Replace the state entirely
/// let computation = put("new state");
/// assert_eq!(computation.run_state("old state"), ((), "new state"));
/// ```
#[inline]
pub fn put<S>(s: S) -> State<S, ()>
where
    S: Clone + Send + Sync + 'static,
{
    State::new(move |_| ((), s.clone()))
}

/// Modifies the state using a function.
///
/// This function creates a State computation that transforms the current state
/// using the provided function and returns unit `()` as its value.
///
/// # State Monad Context
///
/// The `modify` operation combines `get` and `put` into a single operation,
/// allowing you to transform the state based on its current value. This is
/// particularly useful for incremental state updates.
///
/// # Arguments
///
/// * `f`: A function that transforms the state
///
/// # Type Parameters
///
/// * `S`: The type of the state
/// * `F`: The type of the function
///
/// # Returns
///
/// A State computation that modifies the state using the provided function.
///
/// # Examples
///
/// ```rust
/// use rustica::datatypes::state::{State, get, put, modify};
///
/// // Increment the state by 1
/// let increment = modify(|x: i32| x + 1);
/// assert_eq!(increment.run_state(41), ((), 42));
/// ```
#[inline]
pub fn modify<S, F>(f: F) -> State<S, ()>
where
    S: Clone + Send + Sync + 'static,
    F: Fn(S) -> S + Send + Sync + 'static,
{
    State::new(move |s| ((), f(s)))
}

impl<
    S: Clone + Default + Send + Sync + 'static,
    A: Clone + Send + Sync + 'static,
    Err: Clone + Send + Sync + 'static,
> State<S, Result<A, Err>>
{
    /// Runs the state computation and converts the result to a Result with AppError.
    ///
    /// This method runs the state computation and returns a tuple containing the result
    /// wrapped in a Result with AppError and the final state.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::state::State;
    /// use rustica::utils::error_utils::AppError;
    ///
    /// // Create a state computation that might fail
    /// let state = State::new(|s: i32| {
    ///     if s > 0 {
    ///         (Ok(s * 2), s + 1)
    ///     } else {
    ///         (Err("Value must be positive"), s)
    ///     }
    /// });
    ///
    /// let (result, final_state) = state.try_run_state(5);
    /// assert_eq!(result, Ok(10));
    /// assert_eq!(final_state, 6);
    ///
    /// let (result, final_state) = state.try_run_state(-1);
    /// assert!(result.is_err());
    /// assert_eq!(result.unwrap_err().message(), &"Value must be positive");
    /// assert_eq!(final_state, -1);
    /// ```
    pub fn try_run_state(&self, s: S) -> (Result<A, AppError<Err>>, S) {
        let (result, final_state) = self.run_state(s);
        let transformed_result = match result {
            Ok(value) => Ok(value),
            Err(error) => Err(AppError::new(error)),
        };
        (transformed_result, final_state)
    }

    /// Runs the state computation with context and returns a Result with AppError.
    ///
    /// This method is similar to `try_run_state` but allows for adding context to the error.
    ///
    /// # Arguments
    ///
    /// * `s` - The initial state
    /// * `context` - Context to add to the error if the computation fails
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::state::State;
    ///
    /// // Create a state computation that might fail
    /// let state = State::new(|s: i32| {
    ///     if s > 0 {
    ///         (Ok(s * 2), s + 1)
    ///     } else {
    ///         (Err("Value must be positive"), s)
    ///     }
    /// });
    ///
    /// let (result, final_state) = state.try_run_state_with_context(5, "processing user input");
    /// assert_eq!(result, Ok(10));
    /// assert_eq!(final_state, 6);
    ///
    /// let (result, final_state) = state.try_run_state_with_context(-1, "processing user input");
    /// assert!(result.is_err());
    /// let error = result.unwrap_err();
    /// assert_eq!(error.message(), &"Value must be positive");
    /// assert_eq!(error.context(), Some(&"processing user input"));
    /// assert_eq!(final_state, -1);
    /// ```
    pub fn try_run_state_with_context<C: Clone + Send + Sync + 'static>(
        &self, s: S, context: C,
    ) -> (Result<A, AppError<Err, C>>, S) {
        let (result, final_state) = self.run_state(s);
        let transformed_result = match result {
            Ok(value) => Ok(value),
            Err(error) => Err(AppError::with_context(error, context)),
        };
        (transformed_result, final_state)
    }

    /// Runs the state computation and returns only the value as a Result with AppError.
    ///
    /// This method is similar to `eval_state` but converts errors to AppError.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::state::State;
    ///
    /// // Create a state computation that might fail
    /// let state = State::new(|s: i32| {
    ///     if s > 0 {
    ///         (Ok(s * 2), s + 1)
    ///     } else {
    ///         (Err("Value must be positive"), s)
    ///     }
    /// });
    ///
    /// let result = state.try_eval_state(5);
    /// assert_eq!(result, Ok(10));
    ///
    /// let result = state.try_eval_state(-1);
    /// assert!(result.is_err());
    /// assert_eq!(result.unwrap_err().message(), &"Value must be positive");
    /// ```
    pub fn try_eval_state(&self, s: S) -> Result<A, AppError<Err>> {
        let (result, _) = self.try_run_state(s);
        result
    }

    /// Runs the state computation with context and returns only the value as a Result with AppError.
    ///
    /// This method is similar to `try_eval_state` but allows for adding context to the error.
    ///
    /// # Arguments
    ///
    /// * `s` - The initial state
    /// * `context` - Context to add to the error if the computation fails
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::state::State;
    ///
    /// // Create a state computation that might fail
    /// let state = State::new(|s: i32| {
    ///     if s > 0 {
    ///         (Ok(s * 2), s + 1)
    ///     } else {
    ///         (Err("Value must be positive"), s)
    ///     }
    /// });
    ///
    /// let result = state.try_eval_state_with_context(5, "processing user input");
    /// assert_eq!(result, Ok(10));
    ///
    /// let result = state.try_eval_state_with_context(-1, "processing user input");
    /// assert!(result.is_err());
    /// let error = result.unwrap_err();
    /// assert_eq!(error.message(), &"Value must be positive");
    /// assert_eq!(error.context(), Some(&"processing user input"));
    /// ```
    pub fn try_eval_state_with_context<C: Clone + Send + Sync + 'static>(
        &self, s: S, context: C,
    ) -> Result<A, AppError<Err, C>> {
        let (result, _) = self.try_run_state_with_context(s, context);
        result
    }

    /// Runs the state computation and returns only the final state.
    ///
    /// This method is similar to `exec_state` but returns a Result in case of error.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::state::State;
    ///
    /// // Create a state computation that might fail
    /// let state = State::new(|s: i32| {
    ///     if s > 0 {
    ///         (Ok(s * 2), s + 1)
    ///     } else {
    ///         (Err("Value must be positive"), s)
    ///     }
    /// });
    ///
    /// let final_state = state.try_exec_state(5);
    /// assert_eq!(final_state, Ok(6));
    ///
    /// let final_state = state.try_exec_state(-1);
    /// assert!(final_state.is_err());
    /// assert_eq!(final_state.unwrap_err().message(), &"Value must be positive");
    /// ```
    pub fn try_exec_state(&self, s: S) -> Result<S, AppError<Err>> {
        let (result, final_state) = self.try_run_state(s);
        match result {
            Ok(_) => Ok(final_state),
            Err(error) => Err(error),
        }
    }

    /// Runs the state computation with context and returns only the final state.
    ///
    /// This method is similar to `try_exec_state` but allows for adding context to the error.
    ///
    /// # Arguments
    ///
    /// * `s` - The initial state
    /// * `context` - Context to add to the error if the computation fails
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::state::State;
    ///
    /// // Create a state computation that might fail
    /// let state = State::new(|s: i32| {
    ///     if s > 0 {
    ///         (Ok(s * 2), s + 1)
    ///     } else {
    ///         (Err("Value must be positive"), s)
    ///     }
    /// });
    ///
    /// let final_state = state.try_exec_state_with_context(5, "processing user input");
    /// assert_eq!(final_state, Ok(6));
    ///
    /// let final_state = state.try_exec_state_with_context(-1, "processing user input");
    /// assert!(final_state.is_err());
    /// let error = final_state.unwrap_err();
    /// assert_eq!(error.message(), &"Value must be positive");
    /// assert_eq!(error.context(), Some(&"processing user input"));
    /// ```
    pub fn try_exec_state_with_context<C: Clone + Send + Sync + 'static>(
        &self, s: S, context: C,
    ) -> Result<S, AppError<Err, C>> {
        let (result, final_state) = self.try_run_state_with_context(s, context);
        match result {
            Ok(_) => Ok(final_state),
            Err(error) => Err(error),
        }
    }
}

/// Allows conversion from a `StateT<S, Id<(A, S)>, A>` to a `State<S, A>`.
///
/// This implementation enables seamless conversion from the transformer type to the base type,
/// following the same pattern as `Reader` and `ReaderT`. Typically, this is only valid when the
/// base monad is `Id` and the output is a tuple `(A, S)`.
///
/// # Examples
///
/// ```rust
/// use rustica::datatypes::state::State;
/// use rustica::transformers::state_t::StateT;
/// use rustica::datatypes::id::Id;
///
/// // Create a StateT that increments the state
/// let state_t: StateT<i32, Id<(i32, i32)>, i32> = StateT::new(|s| Id::new((s + 1, s + 1)));
///
/// // Convert to State
/// let state: State<i32, i32> = State::from(state_t);
/// assert_eq!(state.run_state(1), (2, 2));
/// ```
impl<S, A> From<StateT<S, Id<(A, S)>, A>> for State<S, A>
where
    S: Clone + Send + Sync + 'static,
    A: Clone + Send + Sync + 'static,
{
    fn from(state_t: StateT<S, Id<(A, S)>, A>) -> Self {
        State { inner: state_t }
    }
}

#[cfg(feature = "full")]
impl<S, A> Arbitrary for State<S, A>
where
    S: Arbitrary + Send + Sync + 'static,
    A: Arbitrary + Send + Sync + 'static,
{
    fn arbitrary(g: &mut Gen) -> Self {
        let value = A::arbitrary(g);
        State::new(move |s: S| (value.clone(), s))
    }
}
