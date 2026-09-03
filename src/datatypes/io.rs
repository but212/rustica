//! # IO Monad
//!
//! The `IO` datatype represents computations that may perform side effects when executed.
//! It provides a way to model effectful operations in a pure functional manner by
//! encapsulating the effects within a monadic context.
//!
//! **Execution model**: `IO` is a *cold* (lazy) computation. Creating an `IO` does not perform effects.
//! Effects happen when you call [`IO::run`], [`IO::try_get`], or other methods that evaluate the
//! computation. If you evaluate the same `IO` multiple times, its effects will run multiple times.
//!
//! ## Quick Start
//!
//! Compose lazy computations and execute them explicitly:
//!
//! ```rust
//! use rustica::datatypes::io::IO;
//!
//! let program = IO::pure(21)
//!     .fmap(|value| value * 2)
//!     .bind(|value| IO::pure(value + 1));
//!
//! assert_eq!(program.run(), 43);
//! ```
//!
//! `IO` is cold: constructing or composing a computation does not run its effects. Calling
//! [`IO::run`] evaluates it, and repeated calls evaluate effectful computations repeatedly.
//!
//! Functional-programming laws for `fmap`, `apply`, and `bind` are covered by the datatype tests.
//!
use crate::error::{BoxedComposableResult, ComposableError, ComposableResult};
#[cfg(any(test, feature = "quickcheck"))]
use quickcheck::{Arbitrary, Gen};
use std::any::Any;
use std::fmt::Debug;
#[cfg(feature = "async")]
use std::future::Future;
use std::sync::Arc;
#[cfg(feature = "async")]
use std::sync::{Mutex, OnceLock};
use std::time::Duration;

/// Type alias for IO morphisms with static lifetime bounds.
///
/// This alias encapsulates the common pattern of `Arc<dyn Fn() -> A + Send + Sync + 'static>`
/// used throughout the IO implementation, making the code more readable and maintainable.
pub type IOMorphism<A> = Arc<dyn Fn() -> A + Send + Sync + 'static>;

/// Type alias for composable error collection results.
///
/// This alias encapsulates the complex type used for collecting multiple ComposableError
/// instances in sequence operations, improving readability and maintainability.
pub type ComposableErrorCollection<E> = smallvec::SmallVec<[Box<ComposableError<E>>; 4]>;

/// A custom error type for IO operations
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum IOError {
    /// The IO operation failed for some other reason
    Other(String),
}

#[inline]
fn panic_message(payload: Box<dyn Any + Send>) -> String {
    match payload.downcast::<String>() {
        Ok(message) => *message,
        Err(payload) => match payload.downcast::<&'static str>() {
            Ok(message) => (*message).to_owned(),
            Err(_) => "IO operation panicked with unknown error".to_owned(),
        },
    }
}

impl std::fmt::Display for IOError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let IOError::Other(msg) = self;
        write!(f, "IO Error: {msg}")
    }
}

impl std::error::Error for IOError {}

/// The IO monad, which represents computations that may perform side effects when executed.
///
/// `IO` provides a way to model effectful operations in a pure functional manner by
/// encapsulating the effects within a monadic context. This allows for composing and
/// sequencing effectful operations while maintaining referential transparency.
///
/// # Thread Safety
///
/// `IO<A>` implements `Send` and `Sync` when `A` implements `Send` and `Sync`, making it safe to share between threads.
/// All operations are thread-safe, though the actual side effects when run depend on the enclosed function.
///
/// # Type Parameters
///
/// * `A` - The type of the value that will be produced by the IO operation
///
/// # Examples
///
/// Basic usage:
///
/// ```rust
/// use rustica::datatypes::io::IO;
///
/// // Create a simple IO operation that prints to stdout and returns a value
/// let io_operation = IO::new(|| {
///     println!("Performing an IO operation");
///     42
/// });
///
/// // Run the IO operation
/// let result = io_operation.run();
/// assert_eq!(result, 42);
///
/// // Transform the result using fmap
/// let transformed = io_operation.fmap(|x| x * 2);
/// assert_eq!(transformed.run(), 84);
/// ```
pub enum IO<A> {
    Pure(A),
    Effect(IOMorphism<A>),
}

#[cfg(feature = "async")]
use std::sync::LazyLock;
#[cfg(feature = "async")]
use tokio::runtime::{Builder, Runtime};

#[cfg(feature = "async")]
static TOKIO_RUNTIME: LazyLock<Runtime> = LazyLock::new(|| {
    Builder::new_multi_thread()
        .enable_all()
        .build()
        .expect("Failed to create Tokio runtime")
});

impl<A: Send + Sync + 'static + Clone> IO<A> {
    /// Creates a new IO operation from a function.
    ///
    /// This constructor allows you to create an `IO` from any function that
    /// produces a value when called, potentially performing side effects.
    ///
    /// # Arguments
    ///
    /// * `f` - A function that performs the IO operation and returns a value
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::io::IO;
    ///
    /// // Create an IO operation that reads from stdin (simulated)
    /// let read_line = IO::new(|| {
    ///     // In a real application, this would read from stdin
    ///     "User input".to_string()
    /// });
    ///
    /// // Create an IO operation that writes to stdout
    /// let write_line = IO::new(|| {
    ///     println!("Writing to stdout");
    ///     ()
    /// });
    /// ```
    #[inline(always)]
    pub fn new<F>(f: F) -> Self
    where
        F: Fn() -> A + Send + Sync + 'static,
    {
        IO::Effect(Arc::new(f))
    }

    /// Runs the IO operation and returns the result.
    ///
    /// This method executes the encapsulated function, performing any side effects
    /// and returning the resulting value.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::io::IO;
    /// use std::time::Instant;
    ///
    /// let io_operation = IO::new(|| {
    ///     // Simulate some work
    ///     (0..1000).sum::<i32>()
    /// });
    ///
    /// let start = Instant::now();
    /// let result = io_operation.run();
    /// let duration = start.elapsed();
    ///
    /// assert_eq!(result, 499500);
    /// println!("Execution took: {:?}", duration);
    /// ```
    #[inline(always)]
    pub fn run(&self) -> A {
        match self {
            IO::Pure(a) => a.clone(),
            IO::Effect(f) => f(),
        }
    }

    /// Runs the IO operation asynchronously.
    ///
    /// This method is available when the `async` feature is enabled.
    /// It executes the encapsulated synchronous function in a non-blocking way
    /// by using `tokio::task::spawn_blocking`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # #[tokio::main]
    /// # async fn main() {
    /// use rustica::datatypes::io::IO;
    ///
    /// let io = IO::new(|| {
    ///     // Simulate a blocking operation
    ///     std::thread::sleep(std::time::Duration::from_millis(10));
    ///     42
    /// });
    ///
    /// let result = io.run_async().await;
    /// assert_eq!(result, 42);
    /// # }
    /// ```
    #[cfg(feature = "async")]
    pub async fn run_async(&self) -> A
    where
        A: Send + Sync,
    {
        let this = self.clone();
        let handle = tokio::runtime::Handle::current();
        handle
            .spawn_blocking(move || this.run())
            .await
            .expect("Failed to run blocking task")
    }

    /// Checks if this IO operation is pure (contains a value without side effects).
    ///
    /// Returns `true` if the IO contains a pure value that was created with `pure()`,
    /// and `false` if it contains an effectful computation created with `new()`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::io::IO;
    ///
    /// let pure_io = IO::pure(42);
    /// assert!(pure_io.is_pure());
    ///
    /// let effect_io = IO::new(|| 42);
    /// assert!(!effect_io.is_pure());
    /// ```
    #[inline(always)]
    pub fn is_pure(&self) -> bool {
        matches!(self, IO::Pure(_))
    }

    /// Checks if this IO operation is effectful (contains a computation with side effects).
    ///
    /// Returns `true` if the IO contains an effectful computation that was created with `new()`,
    /// and `false` if it contains a pure value created with `pure()`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::io::IO;
    ///
    /// let pure_io = IO::pure(42);
    /// assert!(!pure_io.is_effect());
    ///
    /// let effect_io = IO::new(|| 42);
    /// assert!(effect_io.is_effect());
    /// ```
    #[inline(always)]
    pub fn is_effect(&self) -> bool {
        matches!(self, IO::Effect(_))
    }

    /// Creates a new `IO` from an `async` block.
    ///
    /// This method is available when the `async` feature is enabled.
    /// It allows creating an `IO` operation from an asynchronous computation.
    /// The provided future is executed on a shared Tokio runtime.
    ///
    /// # Arguments
    ///
    /// * `fut` - A future that resolves to the value of the IO operation.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # #[tokio::main]
    /// # async fn main() {
    /// use rustica::datatypes::io::IO;
    /// use std::time::Duration;
    ///
    /// let async_io = IO::new_async(async {
    ///     tokio::time::sleep(Duration::from_millis(10)).await;
    ///     "done".to_string()
    /// });
    ///
    /// assert_eq!(async_io.run_async().await, "done");
    /// # }
    /// ```
    #[cfg(feature = "async")]
    pub fn new_async<F>(fut: F) -> Self
    where
        F: Future<Output = A> + Send + 'static,
        A: Send + Sync,
    {
        // The OnceLock makes future execution and result publication one atomic,
        // blocking initialization for all concurrent callers. The separate mutex
        // moves a non-Sync future into that one initialization closure.
        let future_once = Arc::new(Mutex::new(Some(fut)));
        let result_cache = Arc::new(OnceLock::<A>::new());

        IO::new(move || {
            result_cache
                .get_or_init(|| {
                    let future = future_once
                        .lock()
                        .expect("async IO future lock poisoned")
                        .take()
                        .expect("async IO future already consumed");
                    TOKIO_RUNTIME
                        .block_on(
                            TOKIO_RUNTIME.spawn_blocking(move || TOKIO_RUNTIME.block_on(future)),
                        )
                        .expect("Failed to run async IO task")
                })
                .clone()
        })
    }

    /// Maps a function over the result of this IO operation.
    ///
    /// This operation allows transformation of the value inside the `IO` context without executing
    /// the IO operation. It enables function application to the eventual result
    /// of an IO computation while preserving the IO context, following the functor pattern.
    ///
    /// # Arguments
    ///
    /// * `f` - A function that transforms `A` into `B`
    ///
    /// # Examples
    ///
    /// Basic transformation example:
    ///
    /// ```rust
    /// use rustica::datatypes::io::IO;
    ///
    /// let io_number = IO::pure(42);
    /// let io_string = io_number.fmap(|n| format!("The answer is {}", n));
    ///
    /// assert_eq!(io_string.run(), "The answer is 42");
    /// ```
    #[inline(always)]
    pub fn fmap<B: Clone + 'static + Send + Sync>(
        &self, f: impl Fn(A) -> B + Send + Sync + 'static,
    ) -> IO<B> {
        match self {
            IO::Pure(a) => IO::Pure(f(a.clone())),
            IO::Effect(effect) => {
                let effect = Arc::clone(effect);
                IO::Effect(Arc::new(move || f(effect())))
            },
        }
    }

    /// Creates a pure IO operation that just returns the given value.
    ///
    /// This is a fundamental operation that lifts a pure value into the `IO` context
    /// without performing any side effects. It serves as the basis for introducing
    /// values into the IO context.
    ///
    /// # Arguments
    ///
    /// * `value` - The value to wrap in an IO operation
    ///
    /// # Examples
    ///
    /// Basic usage with different types:
    ///
    /// ```rust
    /// use rustica::datatypes::io::IO;
    ///
    /// // Create a pure IO value with an integer
    /// let io_int = IO::pure(42);
    /// assert_eq!(io_int.run(), 42);
    /// ```
    #[inline(always)]
    pub fn pure(value: A) -> Self {
        // Only clone if the IO is run multiple times
        IO::Pure(value)
    }

    /// Chains this IO operation with another IO operation.
    ///
    /// This is a fundamental sequencing operation that allows
    /// IO operations to depend on the results of previous operations.
    /// It enables composing complex IO workflows where each step depends on the
    /// result of previous steps.
    ///
    /// # Arguments
    ///
    /// * `f` - A function that takes the result of this operation and returns a new IO operation
    ///
    /// # Examples
    ///
    /// Basic binding example:
    ///
    /// ```rust
    /// use rustica::datatypes::io::IO;
    ///
    /// let io_operation = IO::pure(42);
    ///
    /// // Chain with another IO operation
    /// let result = io_operation.clone().bind(|x| {
    ///     // This function returns a new IO
    ///     IO::pure(x + 10)
    /// });
    /// assert_eq!(result.run(), 52);
    /// ```
    #[inline(always)]
    pub fn bind<B: Send + Sync + Clone + 'static>(
        &self, f: impl Fn(A) -> IO<B> + Send + Sync + 'static,
    ) -> IO<B> {
        match self {
            IO::Pure(a) => f(a.clone()),
            IO::Effect(effect) => {
                let effect = Arc::clone(effect);
                IO::Effect(Arc::new(move || f(effect()).run()))
            },
        }
    }

    /// Tries to get the value from this IO operation.
    ///
    /// This method runs the IO operation and wraps the result in a `ComposableResult`.
    /// It catches panics from the underlying computation (via `catch_unwind`) and converts them
    /// into a [`ComposableError<IOError>`].
    /// The result contains either the computed value or a `ComposableError<IOError>`,
    /// providing a standardized error handling approach.
    ///
    /// # Returns
    ///
    /// A `ComposableResult<A, IOError>` (i.e., `Result<A, ComposableError<IOError>>`)
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::io::IO;
    ///
    /// let io_operation = IO::pure(42);
    ///
    /// // Try to get the result
    /// let result = io_operation.try_get();
    /// assert_eq!(result.is_ok(), true);
    /// assert_eq!(result.unwrap(), 42);
    /// ```
    pub fn try_get(&self) -> ComposableResult<A, IOError> {
        match std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| self.run())) {
            Ok(value) => Ok(value),
            Err(e) => Err(ComposableError::new(IOError::Other(panic_message(e)))),
        }
    }

    /// Tries to get the value from this IO operation with context.
    ///
    /// This method is similar to `try_get`, but allows you to provide additional
    /// context information that will be included in the error if the operation fails.
    ///
    /// # Arguments
    ///
    /// * `context` - Additional context information to include in the error
    ///
    /// # Returns
    ///
    /// A `Result` containing the computed value of type `A` or a `ComposableError<IOError>`
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::io::{IO, IOError};
    /// use std::panic;
    ///
    /// // Successful operation with context
    /// let io_success: IO<i32> = IO::pure(42);
    /// let result_success = io_success.try_get_with_context("calculating answer");
    /// assert!(result_success.is_ok());
    /// assert_eq!(result_success.unwrap(), 42);
    ///
    /// // Failed operation with context
    /// let io_fail: IO<i32> = IO::new(|| panic!("computation failed"));
    /// let result_fail = io_fail.try_get_with_context("critical calculation");
    /// assert!(result_fail.is_err());
    ///
    /// let error = result_fail.unwrap_err();
    /// // Context is preserved in the error
    /// assert_eq!(error.context(), vec!["critical calculation".to_string()]);
    /// match error.core_error() {
    ///     IOError::Other(msg) => assert!(msg.contains("computation failed")),
    ///     _ => panic!("Unexpected error type"),
    /// }
    /// ```
    pub fn try_get_with_context<C: Into<String>>(
        &self, context: C,
    ) -> ComposableResult<A, IOError> {
        match std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| self.run())) {
            Ok(value) => Ok(value),
            Err(e) => {
                Err(ComposableError::new(IOError::Other(panic_message(e)))
                    .with_context(context.into()))
            },
        }
    }

    /// Tries to get the value using ComposableError for rich error context.
    ///
    /// This method leverages the `ComposableError` type from `src/error` to provide
    /// a more powerful error handling mechanism with context accumulation and error chaining.
    ///
    /// # Returns
    ///
    /// A `ComposableResult<A, IOError>` containing either the value or a composable error
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::io::IO;
    /// use rustica::error::ComposableError;
    ///
    /// // Success case
    /// let io_success = IO::pure(42);
    /// let result = io_success.try_get_composable();
    /// assert!(result.is_ok());
    /// assert_eq!(result.unwrap(), 42);
    ///
    /// // Error case with context
    /// let io_fail: IO<i32> = IO::new(|| panic!("computation failed"));
    /// let result = io_fail.try_get_composable();
    /// assert!(result.is_err());
    ///
    /// let error = result.unwrap_err();
    /// assert!(matches!(error.core_error(), &rustica::datatypes::io::IOError::Other(_)));
    /// ```
    pub fn try_get_composable(&self) -> BoxedComposableResult<A, IOError> {
        match std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| self.run())) {
            Ok(value) => Ok(value),
            Err(e) => Err(Box::new(ComposableError::new(IOError::Other(
                panic_message(e),
            )))),
        }
    }

    /// Tries to get the value with composable error context.
    ///
    /// This method combines the power of `ComposableError` with context information,
    /// allowing for rich error reporting with contextual information stacked appropriately.
    ///
    /// # Arguments
    ///
    /// * `context` - Context information to add to the error if the operation fails
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::io::IO;
    ///
    /// let io_operation = IO::pure(42)
    ///     .bind(|x| IO::new(move || {
    ///         if x > 50 {
    ///             panic!("Value too large")
    ///         }
    ///         x * 2
    ///     }));
    ///
    /// let result = io_operation.try_get_composable_with_context("processing user input");
    /// assert!(result.is_ok());
    /// assert_eq!(result.unwrap(), 84);
    ///
    /// // Failed operation preserves context
    /// let io_fail: IO<i32> = IO::new(|| panic!("database error"));
    /// let result_fail = io_fail.try_get_composable_with_context("fetching user data");
    /// assert!(result_fail.is_err());
    ///
    /// let error = result_fail.unwrap_err();
    /// assert_eq!(error.context().len(), 1);
    /// assert!(error.context()[0].contains("fetching user data"));
    /// ```
    pub fn try_get_composable_with_context<S: Into<String>>(
        &self, context: S,
    ) -> BoxedComposableResult<A, IOError> {
        self.try_get_composable()
            .map_err(|e| Box::new(e.with_context(context.into())))
    }

    /// Recovers from an error using a fallback IO operation.
    ///
    /// This method provides error recovery capabilities, catching panics that occur
    /// during execution and providing an alternative computation. This is useful for
    /// implementing fault-tolerant systems with fallback behaviors.
    ///
    /// # Arguments
    ///
    /// * `recovery` - Function that provides a fallback IO operation given the error
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::io::{IO, IOError};
    ///
    /// let io_risky: IO<i32> = IO::new(|| panic!("primary failed"));
    /// let io_recovered = io_risky.recover(|_error| IO::pure(0));
    ///
    /// assert_eq!(io_recovered.run(), 0);
    ///
    /// // Success case passes through
    /// let io_ok = IO::pure(42);
    /// let io_still_ok = io_ok.recover(|_| IO::pure(0));
    /// assert_eq!(io_still_ok.run(), 42);
    /// ```
    pub fn recover<F>(self, recovery: F) -> Self
    where
        F: Fn(Box<ComposableError<IOError>>) -> IO<A> + Send + Sync + 'static,
    {
        IO::new(move || match self.try_get_composable() {
            Ok(value) => value,
            Err(error) => recovery(error).run(),
        })
    }

    /// Recovers from an error using a simple fallback value.
    ///
    /// This is a convenience method that provides a default value if the IO operation fails.
    /// It's equivalent to `recover(|_| IO::pure(default_value))` but more concise.
    ///
    /// # Arguments
    ///
    /// * `default_value` - The value to use if the operation fails
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::io::IO;
    ///
    /// let io_risky: IO<i32> = IO::new(|| panic!("failed"));
    /// let io_safe = io_risky.recover_with(42);
    ///
    /// assert_eq!(io_safe.run(), 42);
    ///
    /// // Success case returns the original value
    /// let io_ok = IO::pure(100);
    /// let io_still_ok = io_ok.recover_with(42);
    /// assert_eq!(io_still_ok.run(), 100);
    /// ```
    pub fn recover_with(self, default_value: A) -> Self {
        IO::new(move || match self.try_get_composable() {
            Ok(value) => value,
            Err(_) => default_value.clone(),
        })
    }

    /// Sequences multiple IO operations, collecting errors with ComposableError.
    ///
    /// Unlike `sequence`, this method collects all errors that occur during execution
    /// rather than failing fast. This is useful for validation scenarios where you want
    /// to report all problems at once. Errors are boxed to reduce stack usage.
    ///
    /// # Arguments
    ///
    /// * `ios` - Iterator of IO operations to sequence
    ///
    /// # Returns
    ///
    /// A Result containing either all successful values or all collected boxed errors
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::io::IO;
    ///
    /// // All succeed
    /// let ios = vec![IO::pure(1), IO::pure(2), IO::pure(3)];
    /// let result = IO::sequence_composable(ios);
    /// assert!(result.is_ok());
    /// assert_eq!(result.unwrap(), vec![1, 2, 3]);
    ///
    /// // Some fail - collects all errors
    /// let ios_mixed = vec![
    ///     IO::pure(1),
    ///     IO::new(|| panic!("error 1")),
    ///     IO::pure(3),
    ///     IO::new(|| panic!("error 2")),
    /// ];
    /// let result_mixed = IO::sequence_composable(ios_mixed);
    /// assert!(result_mixed.is_err());
    /// // Errors are collected in a SmallVec
    /// ```
    pub fn sequence_composable<I>(ios: I) -> Result<Vec<A>, ComposableErrorCollection<IOError>>
    where
        I: IntoIterator<Item = IO<A>>,
        A: Debug,
    {
        let (successes, failures): (Vec<_>, Vec<_>) = ios
            .into_iter()
            .map(|io| io.try_get_composable())
            .partition(Result::is_ok);

        if failures.is_empty() {
            Ok(successes.into_iter().map(Result::unwrap).collect())
        } else {
            Err(failures.into_iter().map(Result::unwrap_err).collect())
        }
    }

    /// Applies a wrapped function to this IO operation.
    ///
    /// This operation allows application of a function wrapped in `IO` to a value wrapped in `IO`,
    /// following the applicative pattern: `IO<A>.apply(IO<Fn(A) -> B>) -> IO<B>`.
    ///
    /// **Performance optimization**: Pure+Pure combinations are executed immediately
    /// without creating additional closures, similar to AsyncM optimizations.
    ///
    /// # Arguments
    ///
    /// * `mf` - An IO operation that produces a function from `A` to `B`
    ///
    /// # Type Parameters
    ///
    /// * `B` - The type of the result after applying the function
    /// * `F` - The type of the function contained in the IO
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::io::IO;
    ///
    /// // Basic apply usage with Pure values (ultra-fast path)
    /// let io_value = IO::pure(10);
    /// let io_func = IO::pure(|x: i32| x * 2);
    /// let result = io_value.apply(io_func);
    /// assert_eq!(result.run(), 20);
    ///
    /// // Apply with effectful function
    /// let io_value = IO::pure(5);
    /// let io_func = IO::new(|| {
    ///     let multiplier = 3;
    ///     move |x: i32| x * multiplier
    /// });
    /// let result = io_value.apply(io_func);
    /// assert_eq!(result.run(), 15);
    ///
    /// // Chaining apply operations
    /// let result = IO::pure(10)
    ///     .apply(IO::pure(|x: i32| x + 5))
    ///     .apply(IO::pure(|x: i32| x * 2));
    /// assert_eq!(result.run(), 30); // (10 + 5) * 2
    /// ```
    ///
    #[inline(always)]
    pub fn apply<B, F>(&self, mf: IO<F>) -> IO<B>
    where
        B: Send + Sync + Clone + 'static,
        F: Fn(A) -> B + Clone + Send + Sync + 'static,
    {
        // Ultra-fast path: Pure + Pure → Pure
        // Inspired by AsyncM optimization - avoid any Arc overhead
        if let (IO::Pure(v), IO::Pure(f)) = (self, &mf) {
            return IO::Pure(f(v.clone()));
        }

        // Fast path optimizations for mixed cases
        match (self, mf) {
            // Pure value + Effect function
            (IO::Pure(a), IO::Effect(mf)) => {
                let a = a.clone();
                IO::Effect(Arc::new(move || mf()(a.clone())))
            },
            // Effect value + Pure function
            (IO::Effect(ma), IO::Pure(f)) => {
                let ma = Arc::clone(ma);
                IO::Effect(Arc::new(move || f(ma())))
            },
            // Effect value + Effect function
            (IO::Effect(ma), IO::Effect(mf)) => {
                let ma = Arc::clone(ma);
                IO::Effect(Arc::new(move || mf()(ma())))
            },
            // Pure + Pure case already handled above
            _ => unreachable!("All IO enum cases covered"),
        }
    }

    /// Creates an IO operation that completes after a specified duration.
    ///
    /// This method is available when the `async` feature is enabled and uses `tokio::time::sleep`.
    /// The resulting `IO` operation will resolve to the given value `a` after the delay.
    ///
    /// # Arguments
    ///
    /// * `duration` - The duration to wait.
    /// * `a` - The value to be produced after the delay.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # #[tokio::main]
    /// # async fn main() {
    /// use rustica::datatypes::io::IO;
    /// use std::time::{Duration, Instant};
    ///
    /// let start = Instant::now();
    /// let delayed_io = IO::delay(Duration::from_millis(20), 42);
    /// let result = delayed_io.run_async().await;
    ///
    /// assert_eq!(result, 42);
    /// assert!(start.elapsed() >= Duration::from_millis(20));
    /// # }
    /// ```
    #[cfg(feature = "async")]
    pub fn delay(duration: Duration, a: A) -> Self
    where
        A: Send + Sync,
    {
        IO::new_async(async move {
            tokio::time::sleep(duration).await;
            a
        })
    }

    /// Creates a new IO operation that waits for a specified duration before completing (synchronous).
    ///
    /// This method uses `std::thread::sleep`, which yields control to the OS scheduler
    /// for the specified duration, making it an efficient way to pause execution without consuming CPU cycles.
    ///
    /// # Arguments
    ///
    /// * `duration` - The duration to wait.
    /// * `a` - The value to be produced after the delay.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::io::IO;
    /// use std::time::{Duration, Instant};
    ///
    /// let start = Instant::now();
    /// let delayed_io = IO::delay_sync(Duration::from_millis(10), 123);
    /// let result = delayed_io.run();
    ///
    /// assert_eq!(result, 123);
    /// assert!(start.elapsed() >= Duration::from_millis(10));
    /// ```
    pub fn delay_sync(duration: Duration, a: A) -> Self {
        IO::new(move || {
            std::thread::sleep(duration);
            a.clone()
        })
    }

    /// Creates an IO operation that executes conditionally based on a predicate.
    ///
    /// If the predicate is false when evaluated, returns a default value.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::io::IO;
    /// use std::time::SystemTime;
    ///
    /// let conditional_io = IO::when(
    ///     || true, // predicate
    ///     || 42,   // computation if true
    ///     || 0     // default if false
    /// );
    ///
    /// assert_eq!(conditional_io.run(), 42);
    /// ```
    pub fn when<P, F, D>(predicate: P, computation: F, default: D) -> Self
    where
        P: Fn() -> bool + Send + Sync + 'static,
        F: Fn() -> A + Send + Sync + 'static,
        D: Fn() -> A + Send + Sync + 'static,
    {
        IO::new(move || {
            if predicate() {
                computation()
            } else {
                default()
            }
        })
    }

    /// Combines two IO operations, returning a tuple of their results.
    ///
    /// This is similar to FunctionCategory::split but for IO operations.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::io::IO;
    ///
    /// let io1 = IO::pure(10);
    /// let io2 = IO::pure(20);
    /// let combined = IO::combine(&io1, &io2);
    ///
    /// assert_eq!(combined.run(), (10, 20));
    /// ```
    pub fn combine<B>(io1: &IO<A>, io2: &IO<B>) -> IO<(A, B)>
    where
        B: Send + Sync + Clone + 'static,
    {
        let io1_clone = io1.clone();
        let io2_clone = io2.clone();
        IO::new(move || (io1_clone.run(), io2_clone.run()))
    }

    /// Sequences multiple IO operations, collecting their results.
    ///
    /// This is useful for running multiple IO operations and collecting all results.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::io::IO;
    ///
    /// let ios = vec![
    ///     IO::pure(1),
    ///     IO::pure(2),
    ///     IO::pure(3),
    /// ];
    ///
    /// let sequenced = IO::sequence(ios);
    /// assert_eq!(sequenced.run(), vec![1, 2, 3]);
    /// ```
    pub fn sequence<I>(ios: I) -> IO<Vec<A>>
    where
        I: IntoIterator<Item = IO<A>>,
    {
        let ios_vec: Vec<IO<A>> = ios.into_iter().collect();
        IO::new(move || ios_vec.iter().map(|io| io.run()).collect())
    }
}

// Implement Clone for IO<A>
impl<A: Send + Sync + Clone + 'static> Clone for IO<A> {
    fn clone(&self) -> Self {
        match self {
            IO::Pure(a) => IO::Pure(a.clone()),
            IO::Effect(f) => IO::Effect(Arc::clone(f)),
        }
    }
}

// Implement HKT for IO
impl<A> crate::traits::hkt::HKT for IO<A> {
    type Source = A;
    type Output<U> = IO<U>;
}

#[cfg(any(test, feature = "quickcheck"))]
impl<A: Send + Sync + Clone + Arbitrary> Arbitrary for IO<A> {
    fn arbitrary(g: &mut Gen) -> Self {
        let value = A::arbitrary(g);
        IO::pure(value)
    }
}

#[cfg(test)]
mod tests {
    use super::IO;
    use std::sync::{Arc, Mutex};
    use std::time::{Duration, Instant};

    #[test]
    fn test_io_shared_state() {
        let counter = Arc::new(Mutex::new(0));
        let increment = {
            let counter = Arc::clone(&counter);
            IO::new(move || {
                let mut count = counter.lock().unwrap();
                *count += 1;
                *count
            })
        };

        assert_eq!(increment.run(), 1);
        assert_eq!(increment.run(), 2);
        assert_eq!(*counter.lock().unwrap(), 2);
    }

    #[test]
    fn test_io_resilience_and_recovery() {
        let risky: IO<i32> = IO::new(|| panic!("boom"));
        let result = risky.try_get_with_context("critical task");
        assert!(result.is_err());
        assert!(
            result
                .unwrap_err()
                .context()
                .contains(&"critical task".to_string())
        );

        let recovered = IO::<i32>::new(|| panic!("fail")).recover(|_| IO::pure(0));
        let recovered_with = IO::<i32>::new(|| panic!("fail")).recover_with(42);
        assert_eq!(recovered.run(), 0);
        assert_eq!(recovered_with.run(), 42);
    }

    #[test]
    fn test_io_utilities_and_batching() {
        let ios = vec![IO::pure(1), IO::pure(2)];
        assert_eq!(IO::sequence(ios).run(), vec![1, 2]);
        assert_eq!(IO::combine(&IO::pure(10), &IO::pure(20)).run(), (10, 20));

        assert_eq!(IO::when(|| true, || 1, || 0).run(), 1);
        assert_eq!(IO::when(|| false, || 1, || 0).run(), 0);

        let start = Instant::now();
        assert_eq!(IO::delay_sync(Duration::from_millis(10), 123).run(), 123);
        assert!(start.elapsed() >= Duration::from_millis(10));
    }
}

#[cfg(test)]
mod unit_tests {
    use super::IO;

    #[cfg(feature = "async")]
    use std::sync::{
        Arc, Barrier,
        atomic::{AtomicUsize, Ordering},
    };

    #[test]
    fn monadic_fundamentals_and_error_boundaries_hold() {
        let pure_io = IO::pure(42);
        let effect_io = IO::new(|| 42);
        assert!(pure_io.is_pure() && effect_io.is_effect());
        assert_eq!(IO::pure(10).bind(|x| IO::pure(x * 2)).run(), 20);
        assert_eq!(IO::pure(42).bind(IO::pure).run(), 42);
        let app_f = IO::new(|| {
            let multiplier = 3;
            move |x: i32| x * multiplier
        });
        assert_eq!(IO::pure(5).apply(app_f).run(), 15);
        assert_eq!(
            pure_io
                .fmap(|x| x + 8)
                .bind(|x| IO::new(move || x / 2))
                .run(),
            25
        );

        let failed: IO<i32> = IO::new(|| panic!("failed operation"));
        assert_eq!(IO::pure(100).run(), 100);
        assert_eq!(IO::pure(100).try_get_composable(), Ok(100));
        assert_eq!(IO::new(|| 200).try_get_composable(), Ok(200));
        let panicking: IO<i32> = IO::new(|| panic!("failure"));
        assert!(panicking.try_get_composable().is_err());

        assert!(
            failed
                .try_get()
                .unwrap_err()
                .to_string()
                .contains("failed operation")
        );
        let result = IO::sequence_composable(vec![
            IO::pure(1),
            IO::new(|| panic!("error 1")),
            IO::pure(3),
            IO::new(|| panic!("error 2")),
        ]);
        let errors = result.unwrap_err();
        assert_eq!(errors.len(), 2);
        assert!(errors[0].error_chain().contains("error 1"));
        assert!(errors[1].error_chain().contains("error 2"));
    }

    #[cfg(feature = "async")]
    #[test]
    fn async_runs_share_one_initialization() {
        let started = Arc::new(Barrier::new(2));
        let release = Arc::new(Barrier::new(2));
        let executions = Arc::new(AtomicUsize::new(0));
        let io = Arc::new(IO::new_async({
            let started = started.clone();
            let release = release.clone();
            let executions = executions.clone();
            async move {
                executions.fetch_add(1, Ordering::SeqCst);
                started.wait();
                release.wait();
                42
            }
        }));
        let first_io = io.clone();
        let first = std::thread::spawn(move || first_io.run());
        started.wait();
        let second_io = io.clone();
        let second = std::thread::spawn(move || second_io.run());
        release.wait();
        assert_eq!(first.join().unwrap(), 42);
        assert_eq!(second.join().unwrap(), 42);
        assert_eq!(executions.load(Ordering::SeqCst), 1);
    }
}
