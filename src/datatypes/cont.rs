//! # Continuation Monad
//!
//! The Continuation monad represents computations with explicit control flow, allowing
//! operations to be suspended and resumed. It provides a way to manipulate control flow
//! in a purely functional manner.
//!
//! ## Core Concepts
//!
//! - **Continuation-Passing Style**: Functions receive an explicit continuation that represents "what to do next"
//! - **Explicit Control Flow**: Allows implementing advanced control flow patterns like exceptions, backtracking, or coroutines
//! - **Composable Computations**: Continuations can be composed and transformed using monadic operations
//!
//! ## Functional Programming Context
//!
//! In functional programming, continuations provide a way to represent and manipulate control flow
//! as first-class values. The Continuation monad encapsulates this pattern, making it composable
//! with other functional abstractions.
//!
//! The Continuation monad is particularly powerful because it can be used to implement other monads,
//! making it sometimes called the "mother of all monads."
//!
//! ## Use Cases
//!
//! The Continuation monad is useful for:
//!
//! - **Custom Control Flow**: Implementing non-standard control flow patterns
//! - **Exception Handling**: Creating custom error handling mechanisms
//! - **Asynchronous Programming**: Representing callbacks and asynchronous operations
//! - **Backtracking Algorithms**: Implementing algorithms that need to explore multiple paths
//! - **Coroutines**: Building cooperative multitasking systems
//!
//! ## Examples
//!
//! ### Basic Usage
//!
//! ```rust
//! use std::sync::Arc;
//! use rustica::datatypes::cont::Cont;
//!
//! // Create a simple continuation
//! let cont = Cont::pure(42);
//!
//! // Run the continuation with a handler
//! let result = cont.clone().run(|x| x * 2);
//! assert_eq!(result, 84);
//!
//! // Chain continuations
//! let cont2 = cont.bind(Arc::new(|x| Cont::pure(x + 1)));
//! let result2 = cont2.run(|x| x * 2);
//! assert_eq!(result2, 86);
//! ```
//!
//! ### Control Flow Example
//!
//! ```rust
//! use std::sync::Arc;
//! use rustica::datatypes::cont::Cont;
//!
//! // A function that uses continuations to implement early return
//! fn safe_divide(a: i32, b: i32) -> Cont<i32, i32> {
//!     if b == 0 {
//!         // Early return with a default value
//!         Cont::new(|_| -1)
//!     } else {
//!         // Continue with the division
//!         Cont::pure(a / b)
//!     }
//! }
//!
//! // Run with different inputs
//! let result1 = safe_divide(10, 2).run(|x| x);
//! let result2 = safe_divide(10, 0).run(|x| x);
//!
//! assert_eq!(result1, 5);
//! assert_eq!(result2, -1);
//! ```
use std::sync::Arc;

/// The Continuation monad, which represents computations with explicit control flow.
/// 
/// The `Cont` type allows you to work with computations that can be suspended and resumed,
/// making it useful for implementing complex control flow patterns, asynchronous operations,
/// or custom error handling mechanisms.
/// 
/// # Type Parameters
/// 
/// * `R` - The final result type of the computation
/// * `A` - The intermediate value type
/// 
/// # Examples
/// 
/// ```
/// use std::sync::Arc;
/// use rustica::datatypes::cont::Cont;
/// 
/// // Create a simple continuation
/// let cont = Cont::pure(42);
/// 
/// // Run the continuation with a handler
/// let result = cont.clone().run(|x| x * 2);
/// assert_eq!(result, 84);
/// 
/// // Chain continuations
/// let cont2 = cont.bind(Arc::new(|x| Cont::pure(x + 1)));
/// let result2 = cont2.run(|x| x * 2);
/// assert_eq!(result2, 86);
/// ```
#[derive(Clone)]
pub struct Cont<R: 'static, A: 'static> {
    /// The function that represents the continuation.
    /// 
    /// This function takes a continuation (a function from `A` to `R`) and returns an `R`.
    run_cont: Arc<dyn Fn(Arc<dyn Fn(A) -> R>) -> R + 'static>,
}

impl<R: 'static, A: 'static> Cont<R, A> {
    /// Creates a new continuation from a function.
    /// 
    /// This method allows you to create a continuation directly from a function that
    /// takes a continuation and returns the final result.
    /// 
    /// # Arguments
    /// 
    /// * `f` - A function that takes a continuation and returns the final result
    /// 
    /// # Type Parameters
    /// 
    /// * `F` - The type of the function
    /// 
    /// # Examples
    /// 
    /// ```
    /// use std::sync::Arc;
    /// use rustica::datatypes::cont::Cont;
    /// 
    /// // Create a continuation that adds 1 to the input and passes it to the continuation
    /// let cont = Cont::<i32, i32>::new(|k| (*k)(42 + 1));
    /// let result = cont.run(|x| x * 2);
    /// assert_eq!(result, 86);
    /// ```
    pub fn new<F>(f: F) -> Self
    where
        F: Fn(Arc<dyn Fn(A) -> R>) -> R + 'static,
    {
        Cont {
            run_cont: Arc::new(f),
        }
    }

    /// Runs this continuation with the given function.
    /// 
    /// This method executes the continuation by providing a function that processes
    /// the final value produced by the continuation.
    /// 
    /// # Arguments
    /// 
    /// * `f` - A function that processes the final value
    /// 
    /// # Returns
    /// 
    /// The result of running the continuation
    /// 
    /// # Examples
    /// 
    /// ```
    /// use std::sync::Arc;
    /// use rustica::datatypes::cont::Cont;
    /// 
    /// let cont = Cont::pure(42);
    /// 
    /// // Run the continuation, doubling the result
    /// let result = cont.clone().run(|x| x * 2);
    /// assert_eq!(result, 84);
    /// 
    /// // Run the continuation, keeping the original value
    /// let result_int = cont.run(|x| x);
    /// assert_eq!(result_int, 42);
    /// ```
    pub fn run<F>(self, f: F) -> R
    where
        F: Fn(A) -> R + 'static,
    {
        (self.run_cont)(Arc::new(f))
    }

    /// Creates a continuation that returns a pure value.
    /// 
    /// This method lifts a value into the continuation monad context,
    /// creating a continuation that simply passes the value to its continuation.
    /// 
    /// # Arguments
    /// 
    /// * `value` - The value to wrap in a continuation
    /// 
    /// # Returns
    /// 
    /// A new continuation that will pass the value to its continuation
    /// 
    /// # Examples
    /// 
    /// ```
    /// use std::sync::Arc;
    /// use rustica::datatypes::cont::Cont;
    /// 
    /// let cont = Cont::pure(42);
    /// let result = cont.run(|x| x);
    /// assert_eq!(result, 42);
    /// ```
    pub fn pure(value: A) -> Self
    where
        A: Clone + 'static,
        R: 'static,
    {
        Cont::new(move |k| k(value.clone()))
    }

    /// Maps a function over the result of this continuation.
    /// 
    /// This method transforms the value produced by this continuation using the provided function.
    /// It's similar to the `map` operation on other container types.
    /// 
    /// # Arguments
    /// 
    /// * `f` - A function that transforms `A` into `B`
    /// 
    /// # Type Parameters
    /// 
    /// * `B` - The type of the transformed value
    /// 
    /// # Returns
    /// 
    /// A new continuation that produces the transformed value
    /// 
    /// # Examples
    /// 
    /// ```
    /// use std::sync::Arc;
    /// use rustica::datatypes::cont::Cont;
    /// 
    /// let cont = Cont::pure(42);
    /// let mapped = cont.fmap(|x| x.to_string());
    /// let result = mapped.run(|x| x);
    /// assert_eq!(result, "42");
    /// ```
    pub fn fmap<B, F>(self, f: F) -> Cont<R, B>
    where
        F: Fn(A) -> B + Clone + 'static,
        B: 'static,
    {
        Cont::new(move |k| {
            let f = f.clone();
            (self.run_cont)(Arc::new(move |x| k(f(x))))
        })
    }

    /// Chains this continuation with another continuation.
    /// 
    /// This method allows you to sequence continuations, where the result of this
    /// continuation is used to produce a new continuation.
    /// 
    /// # Arguments
    /// 
    /// * `f` - A function that takes the result of this continuation and returns a new continuation
    /// 
    /// # Type Parameters
    /// 
    /// * `B` - The type of value produced by the new continuation
    /// 
    /// # Returns
    /// 
    /// A new continuation representing the sequenced computation
    /// 
    /// # Examples
    /// 
    /// ```
    /// use std::sync::Arc;
    /// use rustica::datatypes::cont::Cont;
    /// 
    /// let cont = Cont::pure(42);
    /// let cont2 = cont.bind(Arc::new(|x| Cont::pure(x + 1)));
    /// let result = cont2.run(|x| x);
    /// assert_eq!(result, 43);
    /// ```
    pub fn bind<B>(self, f: Arc<dyn Fn(A) -> Cont<R, B> + Send + Sync>) -> Cont<R, B>
    where
        B: 'static,
    {
        Cont::new(move |k| {
            let k = k.clone();
            let f = f.clone();
            let run_cont = self.run_cont.clone();
            (run_cont)(Arc::new(move |x| {
                let k = k.clone();
                f(x).run(move |y| (*k)(y))
            }))
        })
    }

    /// Applies a function wrapped in a continuation to a value.
    /// 
    /// This method implements the applicative functor pattern, allowing you to apply
    /// a function that is itself wrapped in a continuation to a value in this continuation.
    /// 
    /// # Arguments
    /// 
    /// * `cf` - A continuation containing a function to apply
    /// 
    /// # Type Parameters
    /// 
    /// * `B` - The type of the result after applying the function
    /// 
    /// # Returns
    /// 
    /// A new continuation with the result of applying the function
    /// 
    /// # Examples
    /// 
    /// ```
    /// use std::sync::Arc;
    /// use rustica::datatypes::cont::Cont;
    /// 
    /// let value_cont = Cont::pure(42);
    /// let function_cont = Cont::pure(Arc::new(|x: i32| x * 2) as Arc<dyn Fn(i32) -> i32 + Send + Sync>);
    /// let result_cont = value_cont.apply(function_cont);
    /// let result = result_cont.run(|x| x);
    /// assert_eq!(result, 84);
    /// ```
    pub fn apply<B>(self, cf: Cont<R, Arc<dyn Fn(A) -> B + Send + Sync>>) -> Cont<R, B>
    where
        B: 'static,
    {
        Cont::new(move |k| {
            let k = k.clone();
            let run_cont = cf.run_cont.clone();
            let self_run_cont = self.run_cont.clone();
            (run_cont)(Arc::new(move |f| {
                let k = k.clone();
                let f = f.clone();
                (self_run_cont)(Arc::new(move |x| (*k)((*f)(x))))
            }))
        })
    }
}
