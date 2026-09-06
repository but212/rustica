//! # Asynchronous Monad
//!
//! The `AsyncM` datatype represents a *lazy* asynchronous computation that will eventually produce a value of
//! type `A`.
//! It provides a monadic-style interface for composing asynchronous operations in a functional programming style.
//!
//! **Important**: `AsyncM` is a *cold* computation. If it was created with [`AsyncM::new`], the provided
//! closure is invoked each time you call [`AsyncM::try_get`]. The result is not memoized.
//!
//! ## Quick Start
//!
//! ```rust
//! use rustica::datatypes::async_monad::AsyncM;
//!
//! #[tokio::main]
//! async fn main() {
//!     // Create async computations
//!     let value = AsyncM::pure(42);
//!     let delayed = AsyncM::new(|| async {
//!         tokio::time::sleep(tokio::time::Duration::from_millis(10)).await;
//!         100
//!     });
//!
//!     // Chain computations with bind
//!     let result = value.clone()
//!         .bind(|x| async move { AsyncM::pure(x * 2) })
//!         .bind(|x| async move { AsyncM::pure(x + 10) });
//!
//!     // Run parallel computations
//!     let combined = value.zip(delayed).fmap(|(a, b)| async move { a + b });
//!
//!     // Execute and get results
//!     assert_eq!(result.try_get().await, 94);
//!     assert_eq!(combined.try_get().await, 142);
//! }
//! ```
//!
//! ## Functional Programming Context
//!
//! In functional programming, asynchronous monads are used to:
//!
//! - Represent computations that will complete in the future
//! - Compose and sequence asynchronous operations
//! - Handle asynchronous control flow in a pure functional manner
//! - Abstract away the complexity of async/await patterns
//!
//! Similar constructs in other functional programming languages include:
//!
//! - `IO` in Cats Effect (Scala)
//! - `Task` in Arrow (Kotlin)
//! - `Task` in fp-ts (TypeScript)
//! - `IO` in Haskell libraries like `async`
//!
//! ## Functional Programming Methods
//!
//! The `AsyncM` type provides inherent methods that follow functional programming patterns:
//!
//! - **Functor-like**: `fmap` allows mapping functions over the eventual result
//! - **Applicative-like**: `apply` enables applying functions wrapped in `AsyncM` to values wrapped in `AsyncM`
//! - **Monad-like**: `bind` provides sequencing of asynchronous operations
//!
//! **Note**: These are inherent methods, not trait implementations. `AsyncM` does not implement
//! the `Functor`, `Applicative`, or `Monad` traits, but provides equivalent functionality
//! through its own methods optimized for async operations.
//!
//! **Execution model**: most combinators (`fmap`, `bind`, `zip`, ...) build a new `AsyncM` without running
//! anything immediately. Actual execution happens when you call [`AsyncM::try_get`].
//!
//! Additional examples are provided on individual methods; the quick-start flow above is the
//! canonical end-to-end usage example.
//!
//! ## Type Class Laws
//!
//! For computations whose provided closures are pure (no observable side effects) and do not
//! panic, the `AsyncM` combinators behave according to the standard Functor, Applicative, and
//! Monad laws.
//!
//! Note that combinators like `apply`/`zip` may run computations concurrently, which can affect
//! the *ordering* of side effects if your closures perform them.
//!
//! ### Functor Laws
//! - Identity: `fmap id = id`
//! - Composition: `fmap (f . g) = fmap f . fmap g`
//!
//! ### Applicative Laws
//! - Identity: `pure id <*> v = v`
//! - Homomorphism: `pure f <*> pure x = pure (f x)`
//! - Interchange: `u <*> pure y = pure ($ y) <*> u`
//! - Composition: `pure (.) <*> u <*> v <*> w = u <*> (v <*> w)`
//!
//! ### Monad Laws
//! - Left Identity: `pure a >>= f = f a`
//! - Right Identity: `m >>= pure = m`
//! - Associativity: `(m >>= f) >>= g = m >>= (\x -> f x >>= g)`
//!
//! See individual function documentation (e.g., `fmap`, `apply`, `bind`) for specific examples demonstrating these laws.
//!
//! ## Common Pitfalls and Solutions
//!
//! ### Infinite Recursion
//! ```rust,no_run
//! // DON'T: This creates infinite recursion
//! let bad = AsyncM::new(|| async {
//!     let inner = AsyncM::pure(42);
//!     inner.try_get().await // Avoid calling try_get inside AsyncM::new
//! });
//!
//! // DO: Use bind for chaining
//! use rustica::datatypes::async_monad::AsyncM;
//!
//! let good = AsyncM::pure(42)
//!     .bind(|x| async move { AsyncM::pure(x * 2) });
//! ```
//!
//! ### Shared State Issues
//! ```rust
//! # use std::sync::{Arc, Mutex};
//! # use rustica::datatypes::async_monad::AsyncM;
//! // DON'T: Capturing mutable references
//! let mut counter = 0;
//! // let bad = AsyncM::new(|| async { counter += 1; counter }); // Won't compile
//!
//! // DO: Use Arc<Mutex<T>> for shared mutable state
//! let counter = Arc::new(Mutex::new(0));
//! let good = AsyncM::new({
//!     let counter = counter.clone();
//!     move || {
//!         let value = counter.clone();
//!         async move {
//!             let mut c = value.lock().unwrap();
//!             *c += 1;
//!             *c
//!         }
//!     }
//! });
//! ```

use futures::{Future, FutureExt};
#[cfg(any(test, feature = "quickcheck"))]
use quickcheck::{Arbitrary, Gen};
use std::{panic, pin::Pin, sync::Arc};

/// A type alias for an asynchronous computation that can be sent between threads.
pub type BoxFuture<'a, T> = Pin<Box<dyn Future<Output = T> + Send + 'a>>;

/// Internal representation of AsyncM, optimized for pure values.
#[derive(Clone)]
enum AsyncMInner<A> {
    /// A pure value with zero Arc overhead
    Pure(Arc<A>),
    /// A lazy computation
    Effect(Arc<dyn Fn() -> BoxFuture<'static, A> + Send + Sync + 'static>),
}

/// The asynchronous monad, which represents a computation that will eventually produce a value.
///
/// `AsyncM` provides a way to work with asynchronous operations in a functional style,
/// allowing composition and sequencing of async computations while maintaining
/// referentially-transparent composition when the provided closures are pure (free of observable
/// side effects).
///
/// # Type Parameters
///
/// * `A` - The type of the value that will be produced by the async computation
///
/// # Examples
///
/// ```rust
/// use rustica::datatypes::async_monad::AsyncM;
/// use tokio;
///
/// #[tokio::main]
/// async fn main() {
///     // Create an async computation
///     let computation: AsyncM<i32> = AsyncM::pure(42);
///     
///     // Run the computation and get the result
///     let result = computation.try_get().await;
///     assert_eq!(result, 42);
///     
///     // Transform the result using fmap
///     let transformed = computation.fmap(|x| async move { x * 2 });
///     assert_eq!(transformed.try_get().await, 84);
/// }
///
/// ```
///
/// # Type Class Laws
///
/// For pure, non-panicking computations, `AsyncM` follows the standard Functor, Applicative,
/// and Monad laws. These laws are verified by asynchronous unit tests below. Combinators such
/// as `apply` and `zip` may run effects concurrently, so side-effect ordering is not guaranteed.
///
/// # Advanced Usage
///
/// Use the documented combinators to build fallible, parallel, and resource-aware pipelines.
/// Keep computations cold by constructing them first and executing them with [`try_get`](Self::try_get).
///
/// ```rust
/// # use std::sync::{Arc, Mutex};
/// # use rustica::datatypes::async_monad::AsyncM;
/// #[derive(Clone)]
/// struct Database {
///     connections: Arc<Mutex<Vec<String>>>,
/// }
///
/// impl Database {
///     fn query(&self, sql: &str) -> AsyncM<String> {
///         let connections = self.connections.clone();
///         let sql = sql.to_string();
///         
///         AsyncM::new(move || {
///             let connections = connections.clone();
///             let sql = sql.clone();
///             async move {
///                 let mut conns = connections.lock().unwrap();
///                 conns.push(format!("Executed: {}", sql));
///                 format!("Result for: {}", sql)
///             }
///         })
///     }
/// }
///
/// #[tokio::main]
/// async fn main() {
/// let db = Database {
///     connections: Arc::new(Mutex::new(Vec::new())),
/// };
///
/// // Chain multiple queries
/// let result = db.query("SELECT * FROM users")
///     .bind(move |users| {
///         let db = db.clone();
///         async move {
///             db.query(&format!("SELECT orders FROM orders WHERE user IN ({})", users))
///         }
///     });
///
/// println!("Query result: {}", result.try_get().await);
/// }
/// ```
#[repr(transparent)]
#[derive(Clone)]
pub struct AsyncM<A> {
    inner: AsyncMInner<A>,
}

impl<A: Send + Sync + 'static> AsyncM<A> {
    /// Creates a new async computation from a future-producing function.
    ///
    /// This constructor allows you to create an `AsyncM` from any function that
    /// produces a `Future` when called.
    ///
    /// # Arguments
    ///
    /// * `f` - A function that creates a new future each time it's called
    ///
    /// # Type Parameters
    ///
    /// * `G` - The type of the function that produces futures
    /// * `F` - The type of the future produced by the function
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::async_monad::AsyncM;
    /// use tokio;
    /// use std::time::Duration;
    ///
    /// #[tokio::main]
    /// async fn main() {
    ///     // Create an async computation that produces a value after a delay
    ///     let delayed = AsyncM::new(|| async {
    ///         tokio::time::sleep(Duration::from_millis(10)).await;
    ///         42
    ///     });
    ///     
    ///     assert_eq!(delayed.try_get().await, 42);
    /// }
    /// ```
    #[inline(always)]
    pub fn new<G, F>(f: G) -> Self
    where
        G: Fn() -> F + Send + Sync + 'static,
        F: Future<Output = A> + Send + 'static,
    {
        AsyncM {
            inner: AsyncMInner::Effect(Arc::new(move || f().boxed())),
        }
    }

    /// Creates a pure async computation that just returns the given value.
    ///
    /// This operation lifts a pure value into the `AsyncM` context without any
    /// asynchronous computation, following the pure value lifting pattern.
    ///
    /// # Arguments
    ///
    /// * `value` - The value to wrap in an async computation
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::async_monad::AsyncM;
    /// use tokio;
    ///
    /// #[tokio::main]
    /// async fn main() {
    ///     // Create a pure async value
    ///     let async_int: AsyncM<i32> = AsyncM::pure(42);
    ///     assert_eq!(async_int.try_get().await, 42);
    ///     
    ///     // Works with any type that implements Send
    ///     let async_string: AsyncM<String> = AsyncM::pure("hello".to_string());
    ///     assert_eq!(async_string.try_get().await, "hello");
    /// }
    /// ```
    #[inline(always)]
    pub fn pure(value: A) -> Self
    where
        A: Clone + Send + Sync + 'static,
    {
        AsyncM {
            inner: AsyncMInner::Pure(Arc::new(value)),
        }
    }

    /// Executes this async computation and returns its value.
    ///
    /// This method runs the async computation and waits for it to complete.
    ///
    /// Note that this method does not return a `Result`: it will propagate panics from the underlying
    /// future. To convert panics into a default value, use [`AsyncM::recover_with`].
    ///
    /// If this `AsyncM` was created with [`AsyncM::new`], calling `try_get` multiple times will run the
    /// underlying computation multiple times.
    ///
    /// # Returns
    ///
    /// The computed value of type `A`
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::async_monad::AsyncM;
    /// use tokio;
    ///
    /// #[tokio::main]
    /// async fn main() {
    ///     let computation = AsyncM::pure(42);
    ///     
    ///     // Run the computation and get the result
    ///     let result = computation.try_get().await;
    ///     assert_eq!(result, 42);
    /// }
    /// ```
    #[inline(always)]
    pub async fn try_get(&self) -> A
    where
        A: Clone,
    {
        match &self.inner {
            AsyncMInner::Pure(value) => (**value).clone(),
            AsyncMInner::Effect(run) => run().await,
        }
    }

    /// Maps a function over the result of this async computation.
    ///
    /// This operation allows transformation of the value inside the `AsyncM` context
    /// while preserving the asynchronous computation structure.
    ///
    /// # Arguments
    ///
    /// * `f` - An async function that transforms `A` into `B`
    ///
    /// # Type Parameters
    ///
    /// * `B` - The type of the result after applying the function
    /// * `F` - The type of the function
    /// * `Fut` - The type of the future returned by the function
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::async_monad::AsyncM;
    /// use tokio;
    ///
    /// #[tokio::main]
    /// async fn main() {
    ///     let computation = AsyncM::pure(42);
    ///     
    ///     // Map a function over the async value
    ///     let doubled = computation.clone().fmap(|x| async move { x * 2 });
    ///     assert_eq!(doubled.try_get().await, 84);
    ///     
    ///     // Chain multiple transformations
    ///     let result = computation
    ///         .fmap(|x| async move { x + 10 })
    ///         .fmap(|x| async move { x.to_string() });
    ///     assert_eq!(result.try_get().await, "52");
    /// }
    /// ```
    #[inline(always)]
    pub fn fmap<B, F, Fut>(self, f: F) -> AsyncM<B>
    where
        B: Send + 'static,
        F: Fn(A) -> Fut + Send + Sync + Clone + 'static,
        Fut: Future<Output = B> + Send + 'static,
        A: Clone,
    {
        // Fast path: Pure → Lazy (avoid double wrapping)
        if let AsyncMInner::Pure(value) = self.inner {
            return AsyncM {
                inner: AsyncMInner::Effect(Arc::new(move || {
                    let f = f.clone();
                    let value = Arc::clone(&value);
                    async move { f((*value).clone()).await }.boxed()
                })),
            };
        }

        // General path: Lazy → Lazy
        let inner = self.inner;
        AsyncM {
            inner: AsyncMInner::Effect(Arc::new(move || {
                let f = f.clone();
                let inner = inner.clone();
                async move {
                    let a = if let AsyncMInner::Effect(run) = &inner {
                        run().await
                    } else {
                        unreachable!()
                    };
                    f(a).await
                }
                .boxed()
            })),
        }
    }

    /// Chains this computation with another async computation.
    ///
    /// This is a fundamental sequencing operation that allows
    /// async operations to depend on the results of previous operations.
    ///
    /// # Arguments
    ///
    /// * `f` - An async function that takes the result of this computation and returns a new computation
    ///
    /// # Type Parameters
    ///
    /// * `B` - The type of the result after applying the function
    /// * `F` - The type of the function
    /// * `Fut` - The type of the future returned by the function
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::async_monad::AsyncM;
    /// use tokio;
    ///
    /// #[tokio::main]
    /// async fn main() {
    ///     let computation = AsyncM::pure(42);
    ///     
    ///     // Chain with another async computation
    ///     let result = computation.clone().bind(|x| async move {
    ///         // This function returns a new AsyncM
    ///         AsyncM::pure(x + 10)
    ///     });
    ///     assert_eq!(result.try_get().await, 52);
    ///     
    ///     // Chain multiple bind operations
    ///     let result = computation
    ///         .bind(|x| async move { AsyncM::pure(x + 10) })
    ///         .bind(|x| async move { AsyncM::pure(x * 2) });
    ///     assert_eq!(result.try_get().await, 104);
    /// }
    /// ```
    #[inline(always)]
    pub fn bind<B, F, Fut>(self, f: F) -> AsyncM<B>
    where
        B: Send + Sync + Clone + 'static,
        F: Fn(A) -> Fut + Send + Sync + Clone + 'static,
        Fut: Future<Output = AsyncM<B>> + Send + 'static,
        A: Clone,
    {
        // Fast path: Pure → direct call
        if let AsyncMInner::Pure(value) = self.inner {
            return AsyncM {
                inner: AsyncMInner::Effect(Arc::new(move || {
                    let f = f.clone();
                    let value = Arc::clone(&value);
                    async move {
                        let next = f((*value).clone()).await;
                        // Inline next monad execution
                        match &next.inner {
                            AsyncMInner::Pure(v) => (**v).clone(),
                            AsyncMInner::Effect(run) => run().await,
                        }
                    }
                    .boxed()
                })),
            };
        }

        // General path: Lazy → Lazy
        let inner = self.inner;
        AsyncM {
            inner: AsyncMInner::Effect(Arc::new(move || {
                let f = f.clone();
                let inner = inner.clone();
                async move {
                    let a = if let AsyncMInner::Effect(run) = &inner {
                        run().await
                    } else {
                        unreachable!()
                    };
                    let next = f(a).await;
                    match &next.inner {
                        AsyncMInner::Pure(v) => (**v).clone(),
                        AsyncMInner::Effect(run) => run().await,
                    }
                }
                .boxed()
            })),
        }
    }

    /// Applies a wrapped function to this async computation.
    ///
    /// This operation allows application of a function wrapped in `AsyncM` to a value wrapped in `AsyncM`,
    /// following the applicative pattern.
    ///
    /// # Arguments
    ///
    /// * `mf` - An async computation that produces a function
    ///
    /// # Type Parameters
    ///
    /// * `B` - The type of the result after applying the function
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::async_monad::AsyncM;
    /// use tokio;
    ///
    /// #[tokio::main]
    /// async fn main() {
    ///     let computation = AsyncM::pure(42);
    ///     
    ///     // Create a function wrapped in AsyncM
    ///     let func = AsyncM::pure(|x: i32| x * 2);
    ///     
    ///     // Apply the wrapped function to the wrapped value
    ///     let result = computation.apply(func);
    ///     assert_eq!(result.try_get().await, 84);
    /// }
    /// ```
    #[inline(always)]
    pub fn apply<B, F>(self, mf: AsyncM<F>) -> AsyncM<B>
    where
        B: Send + Sync + Clone + 'static,
        F: Fn(A) -> B + Clone + Send + Sync + 'static,
        A: Clone,
    {
        // Ultra-fast path: Pure + Pure → direct apply
        if let (AsyncMInner::Pure(v), AsyncMInner::Pure(f)) = (&self.inner, &mf.inner) {
            let result = (**f).clone()((**v).clone());
            return AsyncM::pure(result);
        }

        let self_inner = self.inner;
        let mf_inner = mf.inner;

        AsyncM {
            inner: AsyncMInner::Effect(Arc::new(move || {
                let self_inner = self_inner.clone();
                let mf_inner = mf_inner.clone();

                async move {
                    // Optimized concurrent execution
                    let (value, func) = tokio::join!(
                        async {
                            match &self_inner {
                                AsyncMInner::Pure(v) => (**v).clone(),
                                AsyncMInner::Effect(run) => run().await,
                            }
                        },
                        async {
                            match &mf_inner {
                                AsyncMInner::Pure(f) => (**f).clone(),
                                AsyncMInner::Effect(run) => run().await,
                            }
                        }
                    );
                    func(value)
                }
                .boxed()
            })),
        }
    }

    /// Executes an async `Result` and maps errors to a default value.
    ///
    /// This is a lazy operation: the provided function `f` is invoked each time you call
    /// [`AsyncM::try_get`].
    ///
    /// # Arguments
    ///
    /// * `f` - A function that produces a future that returns a Result
    /// * `default_value` - The value to return if the Result is an Err
    ///
    /// # Returns
    ///
    /// An `AsyncM` that yields the `Ok` value, or yields `default_value` if `f()` returns `Err`.
    ///
    /// The error value is discarded.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::async_monad::AsyncM;
    /// use tokio;
    ///
    /// #[tokio::main]
    /// async fn main() {
    ///     // A function that returns a Result in a Future
    ///     async fn divide(a: i32, b: i32) -> Result<i32, &'static str> {
    ///         if b == 0 {
    ///             Err("Cannot divide by zero")
    ///         } else {
    ///             Ok(a / b)
    ///         }
    ///     }
    ///
    ///     // Handle a successful result
    ///     let success = AsyncM::from_result_or_default(|| divide(10, 2), 0);
    ///     assert_eq!(success.try_get().await, 5);
    ///
    ///     // Handle an error with default value
    ///     let failure = AsyncM::from_result_or_default(|| divide(10, 0), 0);
    ///     assert_eq!(failure.try_get().await, 0);
    /// }
    /// ```
    #[inline]
    pub fn from_result_or_default<F, Fut, E>(f: F, default_value: A) -> AsyncM<A>
    where
        F: Fn() -> Fut + Send + Sync + Clone + 'static,
        Fut: Future<Output = Result<A, E>> + Send + 'static,
        E: Send + Sync + 'static,
        A: Clone + Send + Sync + 'static,
    {
        // Store the default value as an Arc to avoid cloning it when constructing the future
        let default_value = Arc::new(default_value);

        AsyncM {
            inner: AsyncMInner::Effect(Arc::new(move || {
                let f = f.clone();
                let default_value = Arc::clone(&default_value);

                async move {
                    match f().await {
                        Ok(value) => value,
                        Err(_) => (*default_value).clone(),
                    }
                }
                .boxed()
            })),
        }
    }

    /// Runs multiple AsyncM operations in parallel and combines their results.
    ///
    /// This function allows you to run two AsyncM operations concurrently and
    /// then combine their results using a provided function.
    ///
    /// # Arguments
    ///
    /// * `other` - Another AsyncM operation to run in parallel
    /// * `f` - A function that combines the results of both operations
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::async_monad::AsyncM;
    /// use tokio;
    /// use std::time::Duration;
    ///
    /// #[tokio::main]
    /// async fn main() {
    ///     // Create two operations that take some time
    ///     let op1 = AsyncM::new(|| async {
    ///         tokio::time::sleep(Duration::from_millis(10)).await;
    ///         42
    ///     });
    ///     
    ///     let op2 = AsyncM::new(|| async {
    ///         tokio::time::sleep(Duration::from_millis(10)).await;
    ///         "hello"
    ///     });
    ///     
    ///     // Run them in parallel and combine results
    ///     let result = op1.zip_with(op2, |a, b| format!("{} {}", b, a));
    ///     assert_eq!(result.try_get().await, "hello 42");
    /// }
    /// ```
    #[inline(always)]
    pub fn zip_with<B, C, F>(self, other: AsyncM<B>, f: F) -> AsyncM<C>
    where
        F: Fn(A, B) -> C + Send + Sync + Clone + 'static,
        B: Send + Sync + Clone + 'static,
        C: Send + Sync + Clone + 'static,
        A: Clone,
    {
        AsyncM {
            inner: AsyncMInner::Effect(Arc::new(move || {
                let self_inner = self.inner.clone();
                let other_inner = other.inner.clone();
                let f = f.clone();

                async move {
                    let (a, b) = tokio::join!(
                        async {
                            match &self_inner {
                                AsyncMInner::Pure(v) => (**v).clone(),
                                AsyncMInner::Effect(run) => run().await,
                            }
                        },
                        async {
                            match &other_inner {
                                AsyncMInner::Pure(v) => (**v).clone(),
                                AsyncMInner::Effect(run) => run().await,
                            }
                        }
                    );
                    f(a, b)
                }
                .boxed()
            })),
        }
    }

    /// Zips this AsyncM with another AsyncM, returning a tuple of their results.
    ///
    /// This is a convenience method for zip_with that simply returns the pair.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::async_monad::AsyncM;
    /// use tokio;
    ///
    /// #[tokio::main]
    /// async fn main() {
    ///     let a = AsyncM::pure(42);
    ///     let b = AsyncM::pure("hello");
    ///     
    ///     let pair = a.zip(b);
    ///     let (num, str) = pair.try_get().await;
    ///     
    ///     assert_eq!(num, 42);
    ///     assert_eq!(str, "hello");
    /// }
    /// ```
    #[inline]
    pub fn zip<B>(self, other: AsyncM<B>) -> AsyncM<(A, B)>
    where
        B: Send + Sync + Clone + 'static,
        A: Clone,
    {
        self.zip_with(other, |a, b| (a, b))
    }

    /// Recovers from panics in the computation with a default value.
    ///
    /// This method attempts to run the async computation and, if it panics,
    /// returns the provided default value instead.
    ///
    /// This only handles unwind panics (via `catch_unwind`). It does not turn `Result::Err` into
    /// a default value; use [`AsyncM::from_result_or_default`] for that.
    ///
    /// # Arguments
    ///
    /// * `default` - The default value to return if the computation panics
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::async_monad::AsyncM;
    /// use tokio;
    ///
    /// #[tokio::main]
    /// async fn main() {
    ///     // A computation that will panic
    ///     let faulty = AsyncM::new(|| async {
    ///         panic!("This will fail!");
    ///         #[allow(unreachable_code)]
    ///         42
    ///     });
    ///     
    ///     // Recover from the panic with a default value
    ///     let result = faulty.recover_with(0).try_get().await;
    ///     assert_eq!(result, 0);
    ///     
    ///     // A working computation
    ///     let working = AsyncM::pure(42);
    ///     let result = working.recover_with(0).try_get().await;
    ///     assert_eq!(result, 42);
    /// }
    /// ```
    #[inline]
    pub fn recover_with(self, default: A) -> AsyncM<A>
    where
        A: Send + Sync + Clone,
    {
        AsyncM {
            inner: AsyncMInner::Effect(Arc::new(move || {
                let inner = self.inner.clone();
                let default = default.clone();

                async move {
                    // Use std::panic::catch_unwind to handle panics
                    let result = panic::AssertUnwindSafe(async {
                        match &inner {
                            AsyncMInner::Pure(value) => (**value).clone(),
                            AsyncMInner::Effect(run) => run().await,
                        }
                    })
                    .catch_unwind()
                    .await;

                    match result {
                        Ok(value) => value,
                        Err(_) => default,
                    }
                }
                .boxed()
            })),
        }
    }
}

#[cfg(any(test, feature = "quickcheck"))]
impl<A: Arbitrary + Clone + 'static + Send + Sync> Arbitrary for AsyncM<A> {
    fn arbitrary(g: &mut Gen) -> Self {
        let value = A::arbitrary(g);
        AsyncM::pure(value)
    }
}

#[cfg(test)]
mod tests {
    use super::AsyncM;

    #[tokio::test]
    async fn test_core_monadic_ops() {
        let base = AsyncM::pure(21);
        let res_ref = base
            .fmap(|x| async move { x * 2 })
            .bind(|x| async move { AsyncM::pure(x.to_string()) })
            .try_get()
            .await;
        assert_eq!(res_ref, "42");

        let res_applied = AsyncM::new(|| async { 21 })
            .fmap(|x| async move { x * 2 })
            .bind(|x| async move { AsyncM::pure(x + 10) })
            .apply(AsyncM::pure(|x: i32| x.to_string()))
            .try_get()
            .await;
        assert_eq!(res_applied, "52");
    }

    #[tokio::test]
    async fn test_async_monad_laws_for_pure_computations() {
        let value = AsyncM::pure(10);
        let identity = value.clone().fmap(|x| async move { x });
        assert_eq!(value.clone().try_get().await, identity.try_get().await);

        let f = |x: i32| async move { x * 2 };
        let g = |x: i32| async move { x + 1 };
        let composed = value.clone().fmap(|x| async move { (x + 1) * 2 });
        let chained = value.clone().fmap(g).fmap(f);
        assert_eq!(composed.try_get().await, chained.try_get().await);

        let id_fn = AsyncM::pure(|x: i32| x);
        assert_eq!(
            value.clone().apply(id_fn).try_get().await,
            value.try_get().await
        );

        let bind = |x: i32| async move { AsyncM::pure(x + 1) };
        let left = AsyncM::pure(10).bind(bind);
        let right = bind(10).await;
        assert_eq!(left.try_get().await, right.try_get().await);

        let right_identity = AsyncM::pure(10).bind(|x| async move { AsyncM::pure(x) });
        assert_eq!(right_identity.try_get().await, 10);
    }

    #[tokio::test]
    async fn test_async_data_pipeline() {
        async fn async_inc(x: i32) -> i32 {
            x + 1
        }

        let pipeline = AsyncM::pure(10)
            .bind(|x| async move {
                let val = async_inc(x).await;
                if val > 0 {
                    AsyncM::pure(val * 2)
                } else {
                    AsyncM::pure(0)
                }
            })
            .bind(|x| async move { AsyncM::pure(x.to_string()) });

        assert_eq!(pipeline.try_get().await, "22");
    }

    #[tokio::test]
    async fn test_applicative_combination() {
        let a = AsyncM::pure(10);
        let b = AsyncM::new(|| async { "hello" });
        let combined = a
            .zip(b)
            .fmap(|(x, y)| async move { format!("{} {}", y, x) });
        assert_eq!(combined.try_get().await, "hello 10");

        let panicking: AsyncM<i32> = AsyncM::new(|| async { panic!("fail") });
        let recovered = AsyncM::pure(1)
            .zip_with(panicking, |x, y| x + y)
            .recover_with(0);
        assert_eq!(recovered.try_get().await, 0);
    }

    #[tokio::test]
    async fn test_resilience_and_helpers() {
        let ok = AsyncM::from_result_or_default(|| async { Ok::<i32, &str>(42) }, 0);
        assert_eq!(ok.try_get().await, 42);

        let err = AsyncM::from_result_or_default(|| async { Err::<i32, &str>("error") }, 99);
        assert_eq!(err.try_get().await, 99);

        let deep_panic: AsyncM<i32> = AsyncM::pure(1)
            .bind(|_| async { panic!("mid-chain panic") })
            .recover_with(500);
        assert_eq!(deep_panic.try_get().await, 500);
    }
}

#[cfg(test)]
mod unit_tests {
    use super::AsyncM;
    use std::sync::{
        Arc,
        atomic::{AtomicUsize, Ordering},
    };
    use std::time::Duration;

    #[tokio::test]
    async fn effect_apply_remains_cold_and_repeatable() {
        let calls = Arc::new(AtomicUsize::new(0));
        let function = AsyncM::pure({
            let calls = Arc::clone(&calls);
            move |value: i32| {
                calls.fetch_add(1, Ordering::SeqCst);
                value * 2
            }
        });
        let applied = AsyncM::new(|| async { 3 }).apply(function);

        assert_eq!(calls.load(Ordering::SeqCst), 0);
        assert_eq!(applied.try_get().await, 6);
        assert_eq!(applied.try_get().await, 6);
        assert_eq!(calls.load(Ordering::SeqCst), 2);
    }

    #[tokio::test]
    async fn pure_zip_with_remains_cold_and_repeatable() {
        let calls = Arc::new(AtomicUsize::new(0));
        let combined = AsyncM::pure(2).zip_with(AsyncM::pure(4), {
            let calls = Arc::clone(&calls);
            move |left, right| {
                calls.fetch_add(1, Ordering::SeqCst);
                left + right
            }
        });

        assert_eq!(calls.load(Ordering::SeqCst), 0);
        assert_eq!(combined.try_get().await, 6);
        assert_eq!(combined.try_get().await, 6);
        assert_eq!(calls.load(Ordering::SeqCst), 2);
    }

    #[tokio::test]
    async fn cancellation_aborts_a_pending_computation() {
        let task = AsyncM::new(|| async {
            tokio::time::sleep(Duration::from_secs(10)).await;
            42
        });
        let handle = tokio::spawn(async move {
            task.bind(|x| async move { AsyncM::pure(x + 1) })
                .try_get()
                .await
        });
        handle.abort();
        let error = handle.await.expect_err("task should be cancelled");
        assert!(error.is_cancelled());
    }
}
