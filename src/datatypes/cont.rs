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
//! let cont = Cont::return_cont(42);
//!
//! // Run the continuation with a handler
//! let result = cont.clone().run(|x| x * 2);
//! assert_eq!(result, 84);
//!
//! // Chain continuations
//! let cont2 = cont.bind(Arc::new(|x| Cont::return_cont(x + 1)));
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
//!         Cont::return_cont(a / b)
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
use std::marker::PhantomData;
use std::sync::Arc;

/// Type alias for a continuation function
pub type ContFn<R, A> = Arc<dyn Fn(Arc<dyn Fn(A) -> R + Send + Sync>) -> R + Send + Sync + 'static>;

/// The `Cont` monad represents computations in continuation-passing style.
///
/// It captures a computation that takes a continuation (a function) and
/// returns a value of type `R`.
///
/// # Type Parameters
///
/// * `R` - The type of the final result
/// * `A` - The type of the intermediate value
///
/// # Examples
///
/// ```
/// use rustica::datatypes::cont::Cont;
///
/// // Create two continuations
/// let cont1 = Cont::return_cont(5);
/// let cont2 = Cont::return_cont(-1);
///
/// // Run the continuations with an identity continuation
/// let result1 = cont1.run(|x| x);
/// let result2 = cont2.run(|x| x);
///
/// assert_eq!(result1, 5);
/// assert_eq!(result2, -1);
/// ```
#[derive(Clone)]
pub struct Cont<R, A> 
where
    R: 'static,
    A: 'static,
{
    /// The function that represents the continuation.
    ///
    /// This function takes a continuation (a function from `A` to `R`) and returns an `R`.
    run_cont: ContFn<R, A>,
    phantom: PhantomData<(R, A)>,
}

impl<R, A> Cont<R, A> 
where
    R: 'static,
    A: 'static + Send + Sync,
{
    /// Creates a new continuation from a function.
    ///
    /// This method allows you to create a continuation directly from a function that
    /// takes a continuation and returns the final result.
    ///
    /// # Parameters
    ///
    /// * `f` - A function that takes a continuation and returns a result
    ///
    /// # Returns
    ///
    /// A new continuation
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::datatypes::cont::Cont;
    /// use std::sync::Arc;
    ///
    /// let cont = Cont::new(|k| {
    ///     let result = 42;
    ///     k(result)
    /// });
    ///
    /// let result = cont.run(|x| x);
    /// assert_eq!(result, 42);
    /// ```
    #[inline]
    pub fn new<F>(f: F) -> Self
    where
        F: Fn(Arc<dyn Fn(A) -> R + Send + Sync>) -> R + Send + Sync + 'static,
    {
        Cont {
            run_cont: Arc::new(f),
            phantom: PhantomData,
        }
    }

    /// Runs this continuation with the given continuation function.
    ///
    /// This method executes the continuation by providing a function that processes
    /// the final value produced by the continuation.
    ///
    /// # Parameters
    ///
    /// * `k` - The continuation function to use
    ///
    /// # Returns
    ///
    /// The result of running the continuation
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::datatypes::cont::Cont;
    ///
    /// let cont = Cont::return_cont(42);
    /// let result = cont.run(|x| x);
    /// assert_eq!(result, 42);
    ///
    /// // Run the continuation, keeping the original value
    /// let result_int = cont.run(|x| x);
    /// assert_eq!(result_int, 42);
    /// ```
    #[inline]
    pub fn run<F>(&self, f: F) -> R
    where
        F: Fn(A) -> R + Send + Sync + 'static,
    {
        (self.run_cont)(Arc::new(f))
    }

    /// Creates a continuation that returns the given value.
    ///
    /// This method lifts a value into the continuation monad context,
    /// creating a continuation that simply passes the value to its continuation.
    ///
    /// # Parameters
    ///
    /// * `a` - The value to return
    ///
    /// # Returns
    ///
    /// A new continuation that will pass the value to its continuation
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::datatypes::cont::Cont;
    ///
    /// let cont = Cont::return_cont(42);
    /// let result = cont.run(|x| x);
    /// assert_eq!(result, 42);
    /// ```
    #[inline]
    pub fn return_cont(a: A) -> Self
    where
        A: Clone,
    {
        Cont::new(move |k| k(a.clone()))
    }

    /// Maps a function over the continuation's result value.
    ///
    /// This is the implementation of `fmap` for `Cont`, which allows you to transform
    /// the result of a continuation with a function.
    ///
    /// # Type Parameters
    ///
    /// * `B` - The new result type
    /// * `F` - The function type
    ///
    /// # Parameters
    ///
    /// * `f` - A function from `A` to `B`
    ///
    /// # Returns
    ///
    /// A new `Cont` with the transformation applied
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::datatypes::cont::Cont;
    ///
    /// let c = Cont::return_cont(5);
    /// let c2 = c.fmap(|x| x * 2);
    ///
    /// let result = c2.run(|x| x);
    /// assert_eq!(result, 10);
    /// ```
    #[inline]
    pub fn fmap<B, F>(self, f: F) -> Cont<R, B>
    where
        F: Fn(A) -> B + Clone + Send + Sync + 'static,
        B: 'static + Send + Sync,
    {
        Cont::new(move |k| {
            let f_clone = f.clone();
            (self.run_cont)(Arc::new(move |a| {
                k(f_clone(a))
            }))
        })
    }

    /// Binds this continuation to a function that returns another continuation.
    ///
    /// This is the monadic bind for `Cont`, which allows you to sequence continuations.
    ///
    /// # Type Parameters
    ///
    /// * `B` - The type of the result in the new continuation
    ///
    /// # Parameters
    ///
    /// * `f` - A function from `A` to `Cont<R, B>`
    ///
    /// # Returns
    ///
    /// A new continuation that sequences the operations
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::datatypes::cont::Cont;
    /// use std::sync::Arc;
    ///
    /// let c = Cont::return_cont(5);
    /// let c2 = c.bind(Arc::new(|x| Cont::return_cont(x * 2)));
    ///
    /// let result = c2.run(|x| x);
    /// assert_eq!(result, 10);
    /// ```
    #[inline]
    pub fn bind<B>(self, f: Arc<dyn Fn(A) -> Cont<R, B> + Send + Sync>) -> Cont<R, B>
    where
        B: 'static + Send + Sync,
    {
        Cont::new(move |k| {
            let f = f.clone(); // Clone here to avoid moving f in the inner closure
            let k_clone = k.clone(); // Clone k to avoid moving it
            (self.run_cont)(Arc::new(move |a| {
                let f = f.clone(); // Clone again for the inner closure
                let k = k_clone.clone(); // Clone k again for the inner closure
                let cont = f(a);
                cont.run(move |b| k(b))
            }))
        })
    }

    /// Applies a function inside a continuation to a value inside this continuation.
    ///
    /// This implements the `apply` operation from `Applicative`, allowing you
    /// to combine two continuations where one contains a function and the other
    /// contains a value.
    ///
    /// # Type Parameters
    ///
    /// * `B` - The result type after applying the function
    ///
    /// # Parameters
    ///
    /// * `cf` - A continuation containing a function from `A` to `B`
    ///
    /// # Returns
    ///
    /// A new continuation with the function applied to the value
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::datatypes::cont::Cont;
    /// use std::sync::Arc;
    ///
    /// let func_cont = Cont::return_cont(Arc::new(|x: i32| x * 2) as Arc<dyn Fn(i32) -> i32 + Send + Sync>);
    /// let value_cont = Cont::return_cont(5);
    ///
    /// let applied = value_cont.apply(func_cont);
    /// let result = applied.run(|x| x);
    ///
    /// assert_eq!(result, 10);
    /// ```
    #[inline]
    pub fn apply<B>(self, cf: Cont<R, Arc<dyn Fn(A) -> B + Send + Sync>>) -> Cont<R, B>
    where
        B: 'static + Send + Sync,
    {
        Cont::new(move |k| {
            let self_run_cont = self.run_cont.clone();
            (cf.run_cont)(Arc::new(move |f| {
                let f = f.clone();
                let k = k.clone();
                (self_run_cont)(Arc::new(move |a| {
                    let f = f.clone();
                    k((*f)(a))
                }))
            }))
        })
    }

    /// Calls a function on the result of this continuation.
    ///
    /// # Parameters
    ///
    /// * `f` - A function that transforms `A` into `B`
    ///
    /// # Returns
    ///
    /// The result of applying the function to the result of this continuation
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::datatypes::cont::Cont;
    ///
    /// let cont = Cont::return_cont(5);
    /// let result = cont.call_cc(|k| {
    ///     k(10); // Skip the rest of the computation
    ///     k(20); // This will not be executed
    /// });
    /// assert_eq!(result, 10);
    /// ```
    #[inline]
    pub fn call_cc<B, F>(self, f: F) -> Cont<R, B>
    where
        F: FnOnce(Arc<dyn Fn(B) -> Cont<R, A> + Send + Sync>) -> Cont<R, B> + Send + Sync + Clone + 'static,
        B: 'static + Send + Sync + Clone,
    {
        Cont::new(move |k| {
            let k_clone = k.clone();
            
            let escape = Arc::new(move |b: B| -> Cont<R, A> {
                let b = b.clone();
                let k = k_clone.clone();
                Cont::new(move |_| k(b.clone()))
            });
            
            let f_clone = f.clone();
            let result = f_clone(escape);
            let k_final = k.clone();
            result.run(move |b| k_final(b))
        })
    }
}
