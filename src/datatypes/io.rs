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
use std::sync::Arc;
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
/// let result = io_operation.clone().run();
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

impl<O: Send + Sync + 'static> IO<O> {
    /// Creates a new IO operation from a function.
    ///
    /// This constructor allows you to create an `IO` from any function that
    /// produces a value when called, potentially performing side effects.
    ///
    /// # Arguments
    ///
    /// * `f` - A function that performs the IO operation and returns a value
    #[inline(always)]
    pub fn new<F>(f: F) -> Self
    where
        F: Fn() -> O + Send + Sync + 'static,
    {
        IO::Effect(Arc::new(f))
    }

    /// Runs the IO operation and returns the result, consuming the IO.
    ///
    /// This method executes the encapsulated function, performing any side effects
    /// and returning the resulting value.
    #[inline(always)]
    pub fn run(self) -> O {
        match self {
            IO::Pure(a) => a,
            IO::Effect(f) => f(),
        }
    }

    /// Runs the IO operation asynchronously.
    ///
    /// This method is available when the `async` feature is enabled.
    /// It executes the encapsulated synchronous function in a non-blocking way
    /// by using `tokio::task::spawn_blocking`.
    #[cfg(feature = "async")]
    pub async fn run_async(self) -> O {
        let handle = tokio::runtime::Handle::current();
        match handle.spawn_blocking(move || self.run()).await {
            Ok(value) => value,
            Err(error) if error.is_panic() => std::panic::resume_unwind(error.into_panic()),
            Err(error) => panic!("Failed to run blocking task: {error}"),
        }
    }

    /// Checks if this IO operation is pure (contains a value without side effects).
    #[inline(always)]
    pub fn is_pure(&self) -> bool {
        matches!(self, IO::Pure(_))
    }

    /// Checks if this IO operation is effectful (contains a computation with side effects).
    #[inline(always)]
    pub fn is_effect(&self) -> bool {
        matches!(self, IO::Effect(_))
    }

    /// Maps a function over the result of this IO operation.
    #[inline(always)]
    pub fn map<B: Send + Sync + 'static>(
        self, f: impl Fn(O) -> B + Send + Sync + 'static,
    ) -> IO<B> {
        match self {
            IO::Pure(a) => IO::Pure(f(a)),
            IO::Effect(effect) => IO::Effect(Arc::new(move || f(effect()))),
        }
    }

    /// Alias for `map` following functor terminology.
    #[inline(always)]
    pub fn fmap<B: Send + Sync + 'static>(
        self, f: impl Fn(O) -> B + Send + Sync + 'static,
    ) -> IO<B> {
        self.map(f)
    }

    /// Creates a pure IO operation that just returns the given value.
    #[inline(always)]
    pub fn pure(value: O) -> Self {
        IO::Pure(value)
    }

    /// Chains this IO operation with another IO operation.
    #[inline(always)]
    pub fn bind<B: Send + Sync + 'static>(
        self, f: impl Fn(O) -> IO<B> + Send + Sync + 'static,
    ) -> IO<B> {
        match self {
            IO::Pure(a) => f(a),
            IO::Effect(effect) => IO::Effect(Arc::new(move || f(effect()).run())),
        }
    }

    /// Alias for `bind`.
    #[inline(always)]
    pub fn flat_map<B: Send + Sync + 'static>(
        self, f: impl Fn(O) -> IO<B> + Send + Sync + 'static,
    ) -> IO<B> {
        self.bind(f)
    }

    /// Alias for `bind`.
    #[inline(always)]
    pub fn and_then<B: Send + Sync + 'static>(
        self, f: impl Fn(O) -> IO<B> + Send + Sync + 'static,
    ) -> IO<B> {
        self.bind(f)
    }

    /// Tries to get the value from this IO operation.
    pub fn try_get(self) -> ComposableResult<O, IOError> {
        match std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| self.run())) {
            Ok(value) => Ok(value),
            Err(e) => Err(ComposableError::new(IOError::Other(panic_message(e)))),
        }
    }

    /// Tries to get the value from this IO operation with context.
    pub fn try_get_with_context<C: Into<String>>(self, context: C) -> ComposableResult<O, IOError> {
        match std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| self.run())) {
            Ok(value) => Ok(value),
            Err(e) => {
                Err(ComposableError::new(IOError::Other(panic_message(e)))
                    .with_context(context.into()))
            },
        }
    }

    /// Tries to get the value using ComposableError for rich error context.
    pub fn try_get_composable(self) -> BoxedComposableResult<O, IOError> {
        match std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| self.run())) {
            Ok(value) => Ok(value),
            Err(e) => Err(Box::new(ComposableError::new(IOError::Other(
                panic_message(e),
            )))),
        }
    }

    /// Tries to get the value with composable error context.
    pub fn try_get_composable_with_context<S: Into<String>>(
        self, context: S,
    ) -> BoxedComposableResult<O, IOError> {
        self.try_get_composable()
            .map_err(|e| Box::new(e.with_context(context.into())))
    }

    /// Creates an IO operation that executes conditionally based on a predicate.
    pub fn when<P, F, D>(predicate: P, computation: F, default: D) -> Self
    where
        P: Fn() -> bool + Send + Sync + 'static,
        F: Fn() -> O + Send + Sync + 'static,
        D: Fn() -> O + Send + Sync + 'static,
    {
        IO::new(move || {
            if predicate() {
                computation()
            } else {
                default()
            }
        })
    }

    /// Sequences multiple IO operations, collecting errors with ComposableError.
    pub fn sequence_composable<I>(ios: I) -> Result<Vec<O>, ComposableErrorCollection<IOError>>
    where
        I: IntoIterator<Item = IO<O>>,
    {
        let (successes, failures): (Vec<_>, Vec<_>) = ios
            .into_iter()
            .map(|io| io.try_get_composable())
            .partition(Result::is_ok);

        if failures.is_empty() {
            Ok(successes.into_iter().filter_map(Result::ok).collect())
        } else {
            Err(failures.into_iter().filter_map(Result::err).collect())
        }
    }
}

impl<A: Send + Sync + Clone + 'static> IO<A> {
    /// Applies a wrapped function to this IO operation.
    #[inline(always)]
    pub fn apply<B, F>(self, mf: IO<F>) -> IO<B>
    where
        B: Send + Sync + Clone + 'static,
        F: Fn(A) -> B + Clone + Send + Sync + 'static,
    {
        match (self, mf) {
            (IO::Pure(v), IO::Pure(f)) => IO::Pure(f(v)),
            (IO::Pure(a), IO::Effect(mf)) => IO::Effect(Arc::new(move || mf()(a.clone()))),
            (IO::Effect(ma), IO::Pure(f)) => IO::Effect(Arc::new(move || f(ma()))),
            (IO::Effect(ma), IO::Effect(mf)) => IO::Effect(Arc::new(move || mf()(ma()))),
        }
    }

    /// Recovers from an error using a fallback IO operation.
    pub fn recover<F>(self, recovery: F) -> Self
    where
        F: Fn(Box<ComposableError<IOError>>) -> IO<A> + Send + Sync + 'static,
    {
        let this = self;
        IO::new(move || match this.clone().try_get_composable() {
            Ok(value) => value,
            Err(error) => recovery(error).run(),
        })
    }

    /// Recovers from an error using a simple fallback value.
    pub fn recover_with(self, default_value: A) -> Self {
        let this = self;
        IO::new(move || match this.clone().try_get_composable() {
            Ok(value) => value,
            Err(_) => default_value.clone(),
        })
    }

    /// Creates an IO operation that completes after a specified duration.
    #[cfg(feature = "async")]
    pub fn delay(duration: Duration, a: A) -> Self {
        IO::new(move || {
            TOKIO_RUNTIME.block_on(async {
                tokio::time::sleep(duration).await;
            });
            a.clone()
        })
    }

    /// Creates a new IO operation that waits for a specified duration before completing (synchronous).
    pub fn delay_sync(duration: Duration, a: A) -> Self {
        IO::new(move || {
            std::thread::sleep(duration);
            a.clone()
        })
    }

    /// Combines two IO operations, returning a tuple of their results.
    pub fn combine<B>(io1: IO<A>, io2: IO<B>) -> IO<(A, B)>
    where
        B: Send + Sync + Clone + 'static,
    {
        IO::new(move || (io1.clone().run(), io2.clone().run()))
    }

    /// Sequences multiple IO operations, collecting their results.
    pub fn sequence<I>(ios: I) -> IO<Vec<A>>
    where
        I: IntoIterator<Item = IO<A>>,
    {
        let ios_vec: Vec<IO<A>> = ios.into_iter().collect();
        IO::new(move || ios_vec.iter().map(|io| io.clone().run()).collect())
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

        assert_eq!(increment.clone().run(), 1);
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
        assert_eq!(IO::combine(IO::pure(10), IO::pure(20)).run(), (10, 20));

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
    use std::sync::Arc;

    #[cfg(feature = "async")]
    use super::{TOKIO_RUNTIME, panic_message};

    #[test]
    fn pure_combinators_remain_cold_and_repeatable() {
        use std::sync::atomic::{AtomicUsize, Ordering};

        let fmap_calls = Arc::new(AtomicUsize::new(0));
        let mapped = IO::pure(1).fmap({
            let fmap_calls = Arc::clone(&fmap_calls);
            move |value| {
                fmap_calls.fetch_add(1, Ordering::SeqCst);
                value + 1
            }
        });
        assert_eq!(fmap_calls.load(Ordering::SeqCst), 0);
        assert_eq!(mapped.run(), 2);
        assert_eq!(mapped.run(), 2);
        assert_eq!(fmap_calls.load(Ordering::SeqCst), 2);

        let bind_calls = Arc::new(AtomicUsize::new(0));
        let bound = IO::pure(2).bind({
            let bind_calls = Arc::clone(&bind_calls);
            move |value| {
                bind_calls.fetch_add(1, Ordering::SeqCst);
                IO::pure(value * 2)
            }
        });
        assert_eq!(bind_calls.load(Ordering::SeqCst), 0);
        assert_eq!(bound.run(), 4);
        assert_eq!(bound.run(), 4);
        assert_eq!(bind_calls.load(Ordering::SeqCst), 2);

        let apply_calls = Arc::new(AtomicUsize::new(0));
        let function = IO::pure({
            let apply_calls = Arc::clone(&apply_calls);
            move |value: i32| {
                apply_calls.fetch_add(1, Ordering::SeqCst);
                value * 3
            }
        });
        let applied = IO::pure(3).apply(function);
        assert_eq!(apply_calls.load(Ordering::SeqCst), 0);
        assert_eq!(applied.run(), 9);
        assert_eq!(applied.run(), 9);
        assert_eq!(apply_calls.load(Ordering::SeqCst), 2);
    }

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
    fn run_async_preserves_panics_from_the_blocking_operation() {
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            TOKIO_RUNTIME.block_on(IO::new(|| panic!("run_async panic")).run_async())
        }));

        let payload = result.expect_err("run_async should propagate the operation panic");
        assert_eq!(panic_message(payload), "run_async panic");
    }

    #[cfg(feature = "async")]
    #[test]
    fn test_io_delay_runs_synchronously_without_reactor_panic() {
        use std::time::Duration;
        let result = IO::delay(Duration::from_millis(1), 42).run();
        assert_eq!(result, 42);
    }
}
