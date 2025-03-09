//! # Asynchronous Monad
//! 
//! The `AsyncM` datatype represents an asynchronous computation that will eventually produce a value of type `A`.
//! It provides a monadic interface for working with asynchronous operations in a functional programming style.
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
//! ## Type Class Implementations
//! 
//! The `AsyncM` type implements several important functional programming abstractions:
//! 
//! - `Functor`: Allows mapping functions over the eventual result
//! - `Applicative`: Enables applying functions wrapped in `AsyncM` to values wrapped in `AsyncM`
//! - `Monad`: Provides sequencing of asynchronous operations
//! 
//! ## Basic Usage
//! 
//! ```rust
//! use rustica::datatypes::async_monad::AsyncM;
//! use tokio;
//! use std::future::Future;
//! 
//! #[tokio::main]
//! async fn main() {
//!     // Create a pure value
//!     let async_value = AsyncM::pure(42);
//!     
//!     // Map over the value
//!     let doubled = async_value.clone().fmap(|x| async move { x * 2 });
//!     assert_eq!(doubled.try_get().await, 84);
//!     
//!     // Chain async computations
//!     let result = async_value
//!         .bind(|x| async move { AsyncM::pure(x + 1) })
//!         .fmap(|x| async move { x * 2 });
//!     assert_eq!(result.try_get().await, 86);
//! }
//! ```
use futures::future::{self, Future, FutureExt};
use std::pin::Pin;
use std::sync::Arc;

/// A type alias for an asynchronous computation that can be sent between threads.
pub type BoxFuture<'a, T> = Pin<Box<dyn Future<Output = T> + Send + 'a>>;

/// The asynchronous monad, which represents a computation that will eventually produce a value.
/// 
/// `AsyncM` provides a way to work with asynchronous operations in a functional style,
/// allowing composition and sequencing of async computations while maintaining
/// referential transparency.
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
#[derive(Clone)]
pub struct AsyncM<A> {
    // Using a boxed function that returns a boxed future
    // This allows for type erasure and dynamic dispatch
    run: Arc<dyn Fn() -> BoxFuture<'static, A> + Send + Sync + 'static>,
}

impl<A: Send + 'static> AsyncM<A> {
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
    #[inline]
    pub fn new<G, F>(f: G) -> Self
    where
        G: Fn() -> F + Send + Sync + 'static,
        F: Future<Output = A> + Send + 'static,
    {
        AsyncM {
            run: Arc::new(move || f().boxed()),
        }
    }

    /// Creates a pure async computation that just returns the given value.
    /// 
    /// This is the `pure` operation for the `Applicative` type class, lifting
    /// a pure value into the `AsyncM` context.
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
    #[inline]
    pub fn pure(value: A) -> Self 
    where 
        A: Clone + Send + Sync + 'static
    {
        AsyncM {
            run: Arc::new(move || {
                let value = value.clone();
                future::ready(value).boxed()
            }),
        }
    }

    /// Tries to get the value from this async computation.
    /// 
    /// This method runs the async computation and waits for it to complete,
    /// returning the final result.
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
    #[inline]
    pub async fn try_get(&self) -> A {
        (self.run)().await
    }

    /// Maps a function over the result of this async computation.
    /// 
    /// This is the `fmap` operation for the `Functor` type class, allowing
    /// transformation of the value inside the `AsyncM` context.
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
    #[inline]
    pub fn fmap<B, F, Fut>(&self, f: F) -> AsyncM<B>
    where
        B: Send + 'static,
        F: Fn(A) -> Fut + Send + Sync + Clone + 'static,
        Fut: Future<Output = B> + Send + 'static,
        A: Clone,
    {
        let run = Arc::clone(&self.run);
        AsyncM {
            run: Arc::new(move || {
                let f = f.clone();
                let fut = run();
                async move {
                    let a = fut.await;
                    f(a).await
                }.boxed()
            }),
        }
    }

    /// Chains this computation with another async computation.
    /// 
    /// This is the `bind` operation for the `Monad` type class, allowing
    /// sequencing of async operations where each operation can depend on
    /// the result of the previous one.
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
    #[inline]
    pub fn bind<B, F, Fut>(self, f: F) -> AsyncM<B>
    where
        B: Send + 'static,
        F: Fn(A) -> Fut + Send + Sync + Clone + 'static,
        Fut: Future<Output = AsyncM<B>> + Send + 'static,
    {
        AsyncM {
            run: Arc::new(move || {
                let f = f.clone();
                let fut = (self.run)();
                
                async move {
                    let a = fut.await;
                    let next_monad = f(a).await;
                    next_monad.try_get().await
                }.boxed()
            }),
        }
    }

    /// Applies a wrapped function to this async computation.
    /// 
    /// This is the `apply` operation for the `Applicative` type class, allowing
    /// application of a function wrapped in `AsyncM` to a value wrapped in `AsyncM`.
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
    /// use std::sync::Arc;
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
    #[inline]
    pub fn apply<B, F>(self, mf: AsyncM<F>) -> AsyncM<B>
    where
        B: Send + 'static,
        F: Fn(A) -> B + Send + Sync + 'static,
    {
        AsyncM {
            run: Arc::new(move || {
                let f_fut = (mf.run)();
                let x_fut = (self.run)();
                
                async move {
                    let f = f_fut.await;
                    let x = x_fut.await;
                    f(x)
                }.boxed()
            }),
        }
    }

    /// Converts an asynchronous Result into an AsyncM.
    ///
    /// # Arguments
    ///
    /// * `f` - A function that produces a future that returns a Result
    /// * `default_value` - The value to return if the Result is an Err
    ///
    /// # Returns
    ///
    /// An AsyncM that contains the Ok value of the Result, or defaults to the provided value on Error
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
    pub fn from_result_or_default<F, E, Fut>(f: F, default_value: A) -> AsyncM<A>
    where
        F: Fn() -> Fut + Send + Sync + Clone + 'static,
        Fut: Future<Output = Result<A, E>> + Send + Sync + 'static,
        A: Clone + Send + Sync + 'static,
    {
        AsyncM::new(move || {
            let f = f.clone();
            let default = default_value.clone();
            async move {
                match f().await {
                    Ok(value) => value,
                    Err(_) => default,
                }
            }
        })
    }
}
