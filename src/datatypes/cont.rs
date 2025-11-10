//! # Continuation Monad
//!
//! The Continuation monad represents computations with explicit control flow, allowing
//! operations to be suspended and resumed. It provides a way to manipulate control flow
//! in a purely functional manner.
//!
//! ## Quick Start
//!
//! Control program flow with continuations:
//!
//! ```rust
//! use rustica::datatypes::cont::Cont;
//!
//! // Create a simple continuation that passes a value to its continuation
//! let cont_value = Cont::return_cont(42);
//!
//! // Transform the value with fmap
//! let doubled = cont_value.fmap(|x| x * 2);
//!
//! // Run the continuation with an identity function
//! let result = doubled.run(|x| x);
//! assert_eq!(result, 84);
//!
//! // Chain continuations with bind
//! let chained = Cont::return_cont(10)
//!     .bind(|x| Cont::return_cont(x + 5))
//!     .bind(|x| Cont::return_cont(x * 2));
//!
//! let final_result = chained.run(|x| x);
//! assert_eq!(final_result, 30); // ((10 + 5) * 2)
//!
//! // Use continuations for early exit patterns
//! let early_exit = Cont::new(|k| {
//!     // Simulate some computation that might want to exit early
//!     let value = 100;
//!     if value > 50 {
//!         k(value) // Continue normally
//!     } else {
//!         0 // Early exit with different value
//!     }
//! });
//!
//! let exit_result = early_exit.run(|x| x + 1);
//! assert_eq!(exit_result, 101);
//! ```
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
//! making it sometimes called the "mother of all monads." In category theory terms, the Continuation
//! monad is related to the concept of a Yoneda embedding, which provides a representation of objects
//! in terms of their relationships with other objects.
//!
//! Similar structures in other languages include:
//!
//! - Haskell's `Cont` monad in Control.Monad.Cont
//! - Scala's `Cont` in cats library
//! - JavaScript's CPS transformations in libraries like fantasy-land
//! - Scheme and Racket's first-class continuations via `call/cc`
//!
//! ## Functional Programming Methods
//!
//! `Cont<R, A>` provides inherent methods that follow functional programming patterns:
//!
//! - **Functor-like**: `fmap` transforms values inside the continuation
//! - **Applicative-like**: `apply` applies functions wrapped in continuations to values in continuations
//! - **Monad-like**: `bind` sequences continuation operations
//!
//! **Note**: These are inherent methods, not trait implementations. `Cont` does not implement
//! the `Functor`, `Applicative`, or `Monad` traits, but provides equivalent functionality
//! through its own methods optimized for continuation-passing style.
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
//! ## Functional Programming Laws
//!
//! The inherent methods of `Cont<R, A>` satisfy the functional programming laws:
//!
//! ### Functor Laws
//! - Identity: `fmap id == id`
//! - Composition: `fmap (f . g) == fmap f . fmap g`
//!
//! ### Applicative Laws
//! - Identity: `pure id <*> v = v`
//! - Homomorphism: `pure f <*> pure x = pure (f x)`
//! - Interchange: `u <*> pure y = pure ($ y) <*> u`
//! - Composition: `pure (.) <*> u <*> v <*> w = u <*> (v <*> w)`
//!
//! ### Monad Laws
//! - Left Identity: `return a >>= f = f a`
//! - Right Identity: `m >>= return = m`
//! - Associativity: `(m >>= f) >>= g = m >>= (\x -> f x >>= g)`
//!
//! See individual method documentation (e.g., `fmap`, `apply`, `bind`) for specific examples demonstrating these laws.
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
use crate::transformers::cont_t::ContT;
use quickcheck::{Arbitrary, Gen};
use std::sync::Arc;

use crate::datatypes::id::Id;

/// Type alias for a continuation function
pub type ContFn<R, A> = Arc<dyn Fn(Arc<dyn Fn(A) -> R + Send + Sync>) -> R + Send + Sync + 'static>;

/// Type alias for a function wrapped in Arc with Send + Sync bounds, commonly used in continuation operations
pub type ContFn2<A, B> = Arc<dyn Fn(A) -> B + Send + Sync>;

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
            let k_arc = Arc::new(move |a: A| (k)(a).unwrap()) as Arc<dyn Fn(A) -> R + Send + Sync>;
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
    /// effectively executing the continuation and producing the final result. It is the primary
    /// way to extract a value from a continuation.
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
    /// ```rust
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
        self.inner.run(move |a: A| Id::new(k(a))).unwrap()
    }

    /// Creates a continuation that immediately returns the given value.
    ///
    /// This is a convenience method that creates a continuation which, when run,
    /// simply passes the provided value to the continuation function. It is analogous
    /// to `pure` in applicative style and `return` in monadic style.
    ///
    /// # Functional Programming Laws
    ///
    /// ## Identity Law (Monad)
    ///
    /// ```rust
    /// use rustica::datatypes::cont::Cont;
    /// use rustica::traits::monad::Monad;
    ///
    /// // For any continuation cont, binding with return_cont should return the original continuation
    /// // m >>= return = m
    /// let verify_identity_law = |x: i32| {
    ///     let cont = Cont::return_cont(x);
    ///     let with_return = cont.clone().bind(|val| Cont::return_cont(val));
    ///     
    ///     // Both should yield the same result with any continuation function
    ///     let f = |v: i32| v * 2;
    ///     assert_eq!(cont.run(f), with_return.run(f));
    /// };
    ///
    /// verify_identity_law(42);
    /// ```
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
    /// ```rust
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
    /// This operation allows transformation of the value inside the `Cont` context
    /// without changing the continuation structure.
    ///
    /// # Functional Programming Laws
    ///
    /// ## Functor Identity Law
    ///
    /// ```rust
    /// use rustica::datatypes::cont::Cont;
    ///
    /// // For any continuation cont, mapping the identity function should return an equivalent continuation
    /// // fmap id = id
    /// let verify_identity_law = |x: i32| {
    ///     let cont = Cont::return_cont(x);
    ///     let mapped = cont.clone().fmap(|x| x); // Identity function
    ///     
    ///     // Both should yield the same result when run
    ///     assert_eq!(cont.run(|x| x), mapped.run(|x| x));
    /// };
    ///
    /// verify_identity_law(42);
    /// ```
    ///
    /// ## Functor Composition Law
    ///
    /// ```rust
    /// use rustica::datatypes::cont::Cont;
    ///
    /// // For any continuation cont and functions f and g, mapping their composition
    /// // should be the same as mapping f and then mapping g
    /// // fmap (f . g) = fmap f . fmap g
    /// let verify_composition_law = |x: i32| {
    ///     let f = |x: i32| x * 2;
    ///     let g = |x: i32| x + 3;
    ///     
    ///     let cont = Cont::return_cont(x);
    ///     
    ///     // Map the composition of f and g
    ///     let mapped_composition = cont.clone().fmap(move |x| f(g(x)));
    ///     
    ///     // Map g, then map f
    ///     let mapped_separately = cont.clone().fmap(g).fmap(f);
    ///     
    ///     // Both should yield the same result when run
    ///     assert_eq!(mapped_composition.run(|x| x), mapped_separately.run(|x| x));
    /// };
    ///
    /// verify_composition_law(10); // (10 + 3) * 2 = 26
    /// ```
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
    /// of this continuation and returning a new continuation. This is the core operation that
    /// enables chaining complex control flow patterns in a composable manner.
    ///
    /// # Functional Programming Laws
    ///
    /// ## Left Identity Law
    ///
    /// ```rust
    /// use rustica::datatypes::cont::Cont;
    /// use rustica::traits::monad::Monad;
    ///
    /// // For any function f and value x, return x >>= f should be equivalent to f(x)
    /// // return a >>= f = f a
    /// let verify_left_identity = |x: i32| {
    ///     let f = |n: i32| Cont::return_cont(n * 2);
    ///     
    ///     let left_side = Cont::return_cont(x).bind(f);
    ///     let right_side = f(x);
    ///     
    ///     // Both should yield the same result when run
    ///     assert_eq!(left_side.run(|n| n), right_side.run(|n| n));
    /// };
    ///
    /// verify_left_identity(5); // Both sides should result in 10
    /// ```
    ///
    /// ## Right Identity Law
    ///
    /// ```rust
    /// use rustica::datatypes::cont::Cont;
    /// use rustica::traits::monad::Monad;
    ///
    /// // For any continuation m, m >>= return should be equivalent to m
    /// // m >>= return = m
    /// let verify_right_identity = |x: i32| {
    ///     let cont = Cont::return_cont(x);
    ///     
    ///     let with_bind = cont.clone().bind(|val| Cont::return_cont(val));
    ///     
    ///     // Both should yield the same result when run
    ///     assert_eq!(cont.run(|n| n), with_bind.run(|n| n));
    /// };
    ///
    /// verify_right_identity(5);
    /// ```
    ///
    /// ## Associativity Law
    ///
    /// ```rust
    /// use rustica::datatypes::cont::Cont;
    /// use rustica::traits::monad::Monad;
    ///
    /// // For any continuation m and functions f and g:
    /// // (m >>= f) >>= g = m >>= (\x -> f x >>= g)
    /// let verify_associativity = |x: i32| {
    ///     let m = Cont::return_cont(x);
    ///     let f = |n: i32| Cont::return_cont(n * 2);
    ///     let g = |n: i32| Cont::return_cont(n + 3);
    ///     
    ///     // (m >>= f) >>= g
    ///     let left_side = m.clone().bind(f).bind(g);
    ///     
    ///     // m >>= (\x -> f x >>= g)
    ///     let right_side = m.clone().bind(move |val| {
    ///         let f = f;  // Capture f by value
    ///         let g = g;  // Capture g by value
    ///         f(val).bind(g)
    ///     });
    ///     
    ///     // Both should yield the same result when run
    ///     assert_eq!(left_side.run(|n| n), right_side.run(|n| n));
    /// };
    ///
    /// verify_associativity(5); // Both sides should result in 13 ((5*2)+3)
    /// ```
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
    /// This is the applicative functor's apply operation for the continuation monad. It allows
    /// combining two independent continuations where one contains a function and the other contains
    /// a value to be applied to that function.
    ///
    /// # Functional Programming Laws
    ///
    /// ## Identity Law (Applicative)
    ///
    /// ```rust
    /// use rustica::datatypes::cont::Cont;
    /// use std::sync::Arc;
    ///
    /// // For any applicative v, pure id <*> v = v
    /// let verify_identity_law = |x: i32| {
    ///     let v = Cont::return_cont(x);
    ///     let id_fn = Cont::return_cont(Arc::new(|x| x) as Arc<dyn Fn(i32) -> i32 + Send + Sync>);
    ///     
    ///     let applied = v.clone().apply(id_fn);
    ///     
    ///     // Both should yield the same result when run
    ///     assert_eq!(v.run(|x| x), applied.run(|x| x));
    /// };
    ///
    /// verify_identity_law(5);
    /// ```
    ///
    /// ## Homomorphism Law (Applicative)
    ///
    /// ```rust
    /// use rustica::datatypes::cont::Cont;
    /// use std::sync::Arc;
    ///
    /// // pure f <*> pure x = pure (f x)
    /// let verify_homomorphism_law = |x: i32| {
    ///     let f = |n: i32| n * 2;
    ///     
    ///     let pure_f = Cont::return_cont(Arc::new(f) as Arc<dyn Fn(i32) -> i32 + Send + Sync>);
    ///     let pure_x = Cont::return_cont(x);
    ///     
    ///     let left_side = pure_x.clone().apply(pure_f);
    ///     let right_side = Cont::return_cont(f(x));
    ///     
    ///     assert_eq!(left_side.run(|x| x), right_side.run(|x| x));
    /// };
    ///
    /// verify_homomorphism_law(5); // Both sides should equal 10
    /// ```
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
    pub fn apply<B>(self, cf: Cont<R, ContFn2<A, B>>) -> Cont<R, B>
    where
        B: Clone + Send + Sync + 'static,
    {
        Cont {
            inner: self.inner.apply(cf.inner),
        }
    }

    /// Call with current continuation (call/cc).
    ///
    /// Captures the current continuation and passes it to the given function as an "escape function".
    /// This allows for complex control flow patterns like early returns, exceptions, backtracking,
    /// and other non-linear control flow structures. It's one of the most powerful features of the
    /// Continuation monad.
    ///
    /// # Advanced Functional Concepts
    ///
    /// `call_cc` (call-with-current-continuation) is a powerful control operator that reifies the
    /// current continuation as a first-class value, allowing for advanced control flow patterns.
    /// When invoked, the escape function immediately returns its argument as the result of the
    /// entire `call_cc` expression, effectively "jumping out" of the current context.
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
    /// This is an alias for `return_cont` that provides a convenient interface
    /// for creating pure continuation values.
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

impl<R, A> Arbitrary for Cont<R, A>
where
    R: Clone + Send + Sync + 'static,
    A: Arbitrary + Send + Sync + 'static,
{
    fn arbitrary(g: &mut Gen) -> Self {
        let val = A::arbitrary(g);
        Cont::return_cont(val)
    }
}
