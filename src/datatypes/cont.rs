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
//! let cont2 = cont.bind(|x| Cont::return_cont(x + 1));
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
use crate::traits::identity::Identity;
use crate::transformers::cont_t::ContT;
use std::sync::Arc;

use crate::datatypes::id::Id;

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
#[repr(transparent)]
pub struct Cont<R, A> {
    /// The state transformation function
    pub inner: ContT<R, Id<R>, A>,
}

impl<R: Clone + Send + Sync + 'static, A: Clone + Send + Sync + 'static> Clone for Cont<R, A> {
    #[inline]
    fn clone(&self) -> Self {
        Cont {
            inner: self.inner.clone(),
        }
    }
}

impl<R, A> Cont<R, A>
where
    R: Clone + Send + Sync + 'static,
    A: Clone + Send + Sync + 'static,
{
    /// Creates a new continuation from a function.
    ///
    /// This constructor takes a function that accepts a continuation and produces a result.
    /// The function parameter represents the computation to be performed, which will
    /// eventually call the provided continuation to produce the final result.
    ///
    /// # Arguments
    ///
    /// * `f` - A function that takes a continuation and returns a result wrapped in `Id`
    ///
    /// # Returns
    ///
    /// A new `Cont<R, A>` instance
    ///
    /// # Examples
    ///
    /// ```rust
    /// use std::sync::Arc;
    /// use rustica::datatypes::cont::Cont;
    ///
    /// // Create a continuation that doubles its input and adds 1
    /// let cont = Cont::new(|k: Arc<dyn Fn(i32) -> i32 + Send + Sync>| {
    ///     let x = 5;
    ///     let doubled = x * 2;
    ///     k(doubled + 1)
    /// });
    ///
    /// // Run the continuation with the identity function
    /// let result = cont.run(|x| x);
    /// assert_eq!(result, 11);
    /// ```
    #[inline]
    pub fn new<F>(f: F) -> Self
    where
        F: Fn(Arc<dyn Fn(A) -> R + Send + Sync>) -> R + Send + Sync + 'static,
    {
        Self::new_inner(move |k: Arc<dyn Fn(A) -> Id<R> + Send + Sync>| {
            let k_arc =
                Arc::new(move |a: A| (k)(a).value().clone()) as Arc<dyn Fn(A) -> R + Send + Sync>;
            Id::new(f(k_arc))
        })
    }

    /// Creates a new continuation with an inner ContT implementation.
    ///
    /// This is an internal constructor that takes a function working with `Id`-wrapped values.
    /// It's used as the foundation for other constructors that provide a more convenient interface.
    ///
    /// # Arguments
    ///
    /// * `f` - A function that takes a continuation returning `Id<R>` and produces an `Id<R>`
    ///
    /// # Returns
    ///
    /// A new `Cont<R, A>` instance wrapping the provided function
    #[inline]
    fn new_inner<F>(f: F) -> Self
    where
        F: Fn(Arc<dyn Fn(A) -> Id<R> + Send + Sync>) -> Id<R> + Send + Sync + 'static,
    {
        Cont {
            inner: ContT::new(f),
        }
    }

    /// Runs this continuation with the given continuation function.
    ///
    /// This method applies the provided continuation function to the result of this computation,
    /// effectively executing the continuation and producing the final result.
    ///
    /// # Arguments
    ///
    /// * `k` - A function that takes a value of type `A` and returns a value of type `R`
    ///
    /// # Returns
    ///
    /// The final result of type `R` after applying the continuation
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::datatypes::cont::Cont;
    ///
    /// let cont = Cont::return_cont(42);
    /// let result = cont.run(|x| x * 2);
    /// assert_eq!(result, 84);
    /// ```
    #[inline]
    pub fn run<FN>(&self, k: FN) -> R
    where
        FN: Fn(A) -> R + Send + Sync + 'static,
    {
        self.inner.run(move |a: A| Id::new(k(a))).value().clone()
    }

    /// Creates a continuation that immediately returns the given value.
    ///
    /// This is a convenience method that creates a continuation which, when run,
    /// simply passes the provided value to the continuation function.
    ///
    /// # Arguments
    ///
    /// * `a` - The value to be returned by the continuation
    ///
    /// # Returns
    ///
    /// A new `Cont<R, A>` instance that will return the provided value
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::datatypes::cont::Cont;
    ///
    /// let cont = Cont::return_cont(42);
    /// let result = cont.run(|x| x * 2);
    /// assert_eq!(result, 84);
    /// ```
    #[inline]
    pub fn return_cont(a: A) -> Self {
        Cont {
            inner: ContT::pure(a),
        }
    }

    /// Maps a function over the value inside this continuation.
    ///
    /// This is the `fmap` operation for the `Functor` type class, allowing
    /// transformation of the value inside the `Cont` context without
    /// changing the continuation structure.
    ///
    /// # Arguments
    ///
    /// * `f` - A function that transforms `A` into `B`
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::cont::Cont;
    ///
    /// let computation = Cont::return_cont(42);
    ///
    /// // Map a function over the continuation
    /// let doubled = computation.fmap(|x| x * 2);
    /// assert_eq!(doubled.run(|x| x), 84);
    ///
    /// // Chain multiple transformations
    /// let result = Cont::return_cont(42)
    ///     .fmap(|x| x + 10)
    ///     .fmap(|x| x.to_string());
    /// assert_eq!(result.run(|x| x), "52");
    /// ```
    #[inline]
    pub fn fmap<B, F>(self, f: F) -> Cont<R, B>
    where
        F: Fn(A) -> B + Send + Sync + 'static,
        B: Clone + Send + Sync + 'static,
    {
        Cont {
            inner: self.inner.fmap(f),
        }
    }

    /// Monadic bind operation for the continuation monad.
    ///
    /// Allows sequencing of continuation computations by applying a function to the result
    /// of this continuation and returning a new continuation.
    ///
    /// # Arguments
    ///
    /// * `f` - A function that transforms a value of type `A` into a new continuation of type `Cont<R, B>`
    ///
    /// # Returns
    ///
    /// A new continuation of type `Cont<R, B>`
    ///
    /// # Examples
    ///
    /// ```rust
    /// use std::sync::Arc;
    /// use rustica::datatypes::cont::Cont;
    ///
    /// let cont1 = Cont::return_cont(5);
    /// let cont2 = cont1.bind(|x| Cont::return_cont(x * 2));
    /// let result = cont2.run(|x| x);
    /// assert_eq!(result, 10);
    /// ```
    #[inline]
    pub fn bind<B, F>(self, f: F) -> Cont<R, B>
    where
        F: Fn(A) -> Cont<R, B> + Send + Sync + 'static,
        B: Clone + Send + Sync + 'static,
    {
        Cont {
            inner: self.inner.bind(move |a| f(a).inner),
        }
    }

    /// Applies a function contained in a continuation to the value in this continuation.
    ///
    /// This is the applicative functor's apply operation for the continuation monad.
    ///
    /// # Arguments
    ///
    /// * `cf` - A continuation containing a function that transforms a value of type `A` into a value of type `B`
    ///
    /// # Returns
    ///
    /// A new continuation of type `Cont<R, B>`
    ///
    /// # Examples
    ///
    /// ```rust
    /// use std::sync::Arc;
    /// use rustica::datatypes::cont::Cont;
    ///
    /// let cont_val = Cont::return_cont(5);
    /// let cont_fn = Cont::return_cont(Arc::new(|x| x * 2) as Arc<dyn Fn(i32) -> i32 + Send + Sync>);
    /// let result = cont_val.apply(cont_fn).run(|x| x);
    /// assert_eq!(result, 10);
    /// ```
    #[inline]
    pub fn apply<B>(self, cf: Cont<R, Arc<dyn Fn(A) -> B + Send + Sync>>) -> Cont<R, B>
    where
        B: Clone + Send + Sync + 'static,
    {
        Cont {
            inner: self.inner.apply(cf.inner),
        }
    }

    /// Call with current continuation.
    ///
    /// Captures the current continuation and passes it to the given function.
    /// This allows for complex control flow patterns like early returns and exception handling.
    ///
    /// # Arguments
    ///
    /// * `f` - A function that takes a continuation escape function and returns a continuation
    ///
    /// # Returns
    ///
    /// A new continuation of type `Cont<R, B>`
    ///
    /// # Examples
    ///
    /// ```rust
    /// use std::sync::Arc;
    /// use rustica::datatypes::cont::Cont;
    ///
    /// // Use call_cc to implement early return
    /// let computation = Cont::return_cont(5).call_cc(|exit| {
    ///     // If condition is met, exit early with a different value
    ///     if 5 > 3 {
    ///         exit(10)
    ///     } else {
    ///         Cont::return_cont(5)
    ///     }
    /// });
    ///
    /// assert_eq!(computation.run(|x| x), 10);
    /// ```
    #[inline]
    pub fn call_cc<B, F>(self, f: F) -> Cont<R, B>
    where
        F: FnOnce(Box<dyn Fn(B) -> Cont<R, A> + Send + Sync>) -> Cont<R, B>
            + Send
            + Sync
            + Copy
            + 'static,
        B: Clone + Send + Sync + 'static,
    {
        Cont {
            inner: ContT::call_cc(move |k| f(Box::new(move |b| Cont { inner: k(b) })).inner),
        }
    }

    /// Lifts a value into the continuation monad context.
    ///
    /// This is an alias for `return_cont` that aligns with the `Pure` trait.
    ///
    /// # Arguments
    ///
    /// * `a` - The value to lift into the continuation context
    ///
    /// # Returns
    ///
    /// A new `Cont<R, A>` containing the provided value
    #[inline]
    pub fn pure(a: A) -> Self {
        Self::return_cont(a)
    }
}

/// Allows conversion from a `ContT<R, Id<R>, A>` to a `Cont<R, A>`.
///
/// This implementation enables seamless conversion from the transformer type to the base type,
/// following the same pattern as `Reader` and `ReaderT`. Typically, this is only valid when the
/// base monad is `Id`.
///
/// # Examples
///
/// ```rust
/// use rustica::datatypes::cont::Cont;
/// use rustica::transformers::cont_t::ContT;
/// use rustica::datatypes::id::Id;
///
/// // Create a ContT that applies the continuation to the value 42
/// let cont_t: ContT<i32, Id<i32>, i32> = ContT::new(|k| k(42));
///
/// // Convert to Cont
/// let cont: Cont<i32, i32> = Cont::from(cont_t);
/// let result = cont.run(|x| x + 1);
/// assert_eq!(result, 43);
/// ```
impl<R, A> From<crate::transformers::cont_t::ContT<R, crate::datatypes::id::Id<R>, A>>
    for Cont<R, A>
where
    R: Clone + Send + Sync + 'static,
    A: Clone + Send + Sync + 'static,
{
    fn from(cont_t: crate::transformers::cont_t::ContT<R, crate::datatypes::id::Id<R>, A>) -> Self {
        Cont { inner: cont_t }
    }
}
