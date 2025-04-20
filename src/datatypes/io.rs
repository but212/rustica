//! # IO Monad
//!
//! The `IO` datatype represents computations that may perform side effects when executed.
//! It provides a way to model effectful operations in a pure functional manner by
//! encapsulating the effects within a monadic context.
//!
//! ## Functional Programming Context
//!
//! In functional programming, the IO monad is used to:
//!
//! - Separate pure computation from effectful operations
//! - Make side effects explicit in the type system
//! - Compose and sequence effectful operations
//! - Maintain referential transparency in the presence of side effects
//!
//! Similar constructs in other functional programming languages include:
//!
//! - `IO` in Haskell
//! - `IO` in Cats Effect (Scala)
//! - `IO` in fp-ts (TypeScript)
//! - `IO` in Arrow (Kotlin)
//!
//! ## Type Class Implementations
//!
//! The `IO` type implements several important functional programming abstractions:
//!
//! - `Functor`: Allows mapping functions over the result of an IO operation
//! - `Applicative`: Enables applying functions wrapped in `IO` to values wrapped in `IO`
//! - `Monad`: Provides sequencing of IO operations where each operation can depend on the result of previous ones
//!
//! ## Basic Usage
//!
//! Basic usage:
//!
//! ```rust
//! use rustica::datatypes::io::IO;
//!
//! // Create a pure IO value (i32)
//! let io_int: IO<i32> = IO::pure(42);
//! assert_eq!(io_int.run(), 42);
//!
//! // IO with a String
//! let io_string: IO<String> = IO::pure("hello".to_string());
//! assert_eq!(io_string.run(), "hello");
//!
//! // fmap usage
//! let doubled = io_int.clone().fmap(|x| x * 2);
//! assert_eq!(doubled.run(), 84);
//!
//! // bind usage
//! let chained = io_int.clone().bind(|x| IO::pure(x + 1));
//! assert_eq!(chained.run(), 43);
//!
//! // Error handling with try_get
//! let safe = io_int.try_get();
//! assert!(safe.is_ok());
//! assert_eq!(safe.unwrap(), 42);
//! ```
//!
//! Error case:
//!
//! ```rust
//! use rustica::datatypes::io::IO;
//! use std::panic;
//!
//! // IO that panics
//! let io_fail: IO<i32> = IO::new(|| panic!("fail"));
//! let result = io_fail.try_get();
//! assert!(result.is_err());
//! let msg = format!("{}", result.unwrap_err());
//! assert!(msg.contains("fail"));
//! ```
//!
//! ## Advanced Usage
//!
//! ```rust
//! use rustica::datatypes::io::IO;
//!
//! // Create a pure IO value
//! let io_value = IO::pure(42);
//!
//! // Map over the value
//! let doubled = io_value.clone().fmap(|x| x * 2);
//! assert_eq!(doubled.run(), 84);
//!
//! // Chain IO operations
//! let result = io_value
//!     .bind(|x| IO::new(move || x + 1))
//!     .fmap(|x| x * 2);
//! assert_eq!(result.run(), 86);
//! ```

use crate::utils::error_utils::AppError;
use spin_sleep::SpinSleeper;
use std::sync::Arc;

/// A custom error type for IO operations
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum IOError {
    /// The IO operation failed because the value hasn't been set yet
    ValueNotSet,
    /// The IO operation failed for some other reason
    Other(String),
}

impl std::fmt::Display for IOError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            IOError::ValueNotSet => write!(f, "Value not set"),
            IOError::Other(msg) => write!(f, "IO Error: {}", msg),
        }
    }
}

impl std::error::Error for IOError {}

/// The IO monad, which represents computations that may perform side effects when executed.
///
/// `IO` provides a way to model effectful operations in a pure functional manner by
/// encapsulating the effects within a monadic context. This allows for composing and
/// sequencing effectful operations while maintaining referential transparency.
///
/// # Type Parameters
///
/// * `A` - The type of the value that will be produced by the IO operation
///
/// # Examples
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
#[derive(Clone)]
pub struct IO<A> {
    run: Arc<dyn Fn() -> A + 'static>,
}

impl<A: 'static + Clone> IO<A> {
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
    #[inline]
    pub fn new<F>(f: F) -> Self
    where
        F: Fn() -> A + 'static,
    {
        IO { run: Arc::new(f) }
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
    ///
    /// let io_operation = IO::new(|| 42);
    ///
    /// // Run the IO operation
    /// let result = io_operation.run();
    /// assert_eq!(result, 42);
    /// ```
    #[inline]
    pub fn run(&self) -> A {
        (self.run)()
    }

    /// Maps a function over the result of this IO operation.
    ///
    /// This is the `fmap` operation for the `Functor` type class, allowing
    /// transformation of the value inside the `IO` context without executing
    /// the IO operation.
    ///
    /// # Arguments
    ///
    /// * `f` - A function that transforms `A` into `B`
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::io::IO;
    ///
    /// let io_operation = IO::new(|| 42);
    ///
    /// // Map a function over the IO value
    /// let doubled = io_operation.clone().fmap(|x| x * 2);
    /// assert_eq!(doubled.run(), 84);
    ///
    /// // Chain multiple transformations
    /// let result = io_operation
    ///     .fmap(|x| x + 10)
    ///     .fmap(|x| x.to_string());
    /// assert_eq!(result.run(), "52");
    /// ```
    #[inline]
    pub fn fmap<B: Clone + 'static>(&self, f: impl Fn(A) -> B + 'static) -> IO<B> {
        // Avoid unnecessary Arc::clone if not needed
        let run = if Arc::strong_count(&self.run) == 1 {
            // Only one reference, move it
            Arc::clone(&self.run)
        } else {
            Arc::clone(&self.run)
        };
        IO::new(move || f(run()))
    }

    /// Creates a pure IO operation that just returns the given value.
    ///
    /// This is the `pure` operation for the `Applicative` type class, lifting
    /// a pure value into the `IO` context without performing any side effects.
    ///
    /// # Arguments
    ///
    /// * `value` - The value to wrap in an IO operation
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::io::IO;
    ///
    /// // Create a pure IO value
    /// let io_int = IO::pure(42);
    /// assert_eq!(io_int.run(), 42);
    ///
    /// // Works with any type that implements Clone
    /// let io_string = IO::pure("hello".to_string());
    /// assert_eq!(io_string.run(), "hello");
    /// ```
    #[inline]
    pub fn pure(value: A) -> Self {
        // Only clone if the IO is run multiple times
        IO::new(move || value.clone())
    }

    /// Chains this IO operation with another IO operation.
    ///
    /// This is the `bind` operation for the `Monad` type class, allowing
    /// sequencing of IO operations where each operation can depend on
    /// the result of the previous one.
    ///
    /// # Arguments
    ///
    /// * `f` - A function that takes the result of this operation and returns a new IO operation
    ///
    /// # Examples
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
    ///
    /// // Chain multiple bind operations
    /// let result = io_operation
    ///     .bind(|x| IO::pure(x + 10))
    ///     .bind(|x| IO::pure(x * 2));
    /// assert_eq!(result.run(), 104);
    ///
    /// // Real-world example: reading and processing input
    /// let read_and_process = IO::new(|| "user input".to_string())
    ///     .bind(|input| IO::new(move || {
    ///         // Process the input
    ///         let processed = input.to_uppercase();
    ///         // Return the processed result
    ///         processed
    ///     }));
    /// assert_eq!(read_and_process.run(), "USER INPUT");
    /// ```
    #[inline]
    pub fn bind<B: Clone + 'static>(&self, f: impl Fn(A) -> IO<B> + 'static) -> IO<B> {
        let run = Arc::clone(&self.run);
        IO::new(move || {
            let a = run();
            f(a).run()
        })
    }

    /// Tries to get the value from this IO operation.
    ///
    /// This method runs the IO operation and wraps the result in a `Result`.
    /// The result contains either the computed value or an `AppError<IOError>`,
    /// providing a standardized error handling approach.
    ///
    /// # Returns
    ///
    /// A `Result` containing the computed value of type `A` or an `AppError<IOError>`
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
    pub fn try_get(&self) -> Result<A, AppError<IOError>> {
        match std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| self.run())) {
            Ok(value) => Ok(value),
            Err(e) => {
                let msg = if let Some(s) = e.downcast_ref::<&str>() {
                    (*s).to_string()
                } else if let Some(s) = e.downcast_ref::<String>() {
                    s.clone()
                } else {
                    "IO operation panicked with unknown error".to_string()
                };
                Err(AppError::new(IOError::Other(msg)))
            },
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
    /// A `Result` containing the computed value of type `A` or an `AppError<IOError, C>`
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::io::IO;
    ///
    /// let io_operation = IO::pure(42);
    ///
    /// // Try to get the result with context
    /// let result = io_operation.try_get_with_context("loading configuration");
    /// assert_eq!(result.is_ok(), true);
    /// assert_eq!(result.unwrap(), 42);
    /// ```
    pub fn try_get_with_context<C: Clone + 'static>(
        &self, context: C,
    ) -> Result<A, AppError<IOError, C>> {
        match std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| self.run())) {
            Ok(value) => Ok(value),
            Err(e) => {
                let msg = if let Some(s) = e.downcast_ref::<&str>() {
                    (*s).to_string()
                } else if let Some(s) = e.downcast_ref::<String>() {
                    s.clone()
                } else {
                    "IO operation panicked with unknown error".to_string()
                };
                Err(AppError::with_context(IOError::Other(msg), context))
            },
        }
    }

    /// Applies a function that returns an IO to this IO operation.
    ///
    /// This is similar to `bind` but with a different signature to support
    /// the `Applicative` pattern in certain contexts.
    ///
    /// # Arguments
    ///
    /// * `mf` - A function that takes the result of this operation and returns a new IO operation
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::io::IO;
    ///
    /// let io_operation = IO::pure(42);
    ///
    /// // Apply a function that returns an IO
    /// let result = io_operation.apply(|x| IO::pure(x * 2));
    /// assert_eq!(result.run(), 84);
    /// ```
    #[inline]
    pub fn apply<B: Clone + 'static>(&self, mf: impl Fn(A) -> IO<B> + 'static) -> IO<B> {
        self.bind(mf)
    }

    /// Creates a new IO operation that delays execution for a specified duration.
    ///
    /// This is a utility function that allows you to create an `IO` that will
    /// delay its execution for a specified duration before returning a value.
    ///
    /// # Arguments
    ///
    /// * `duration` - The duration to delay the execution
    /// * `value` - The value to return after the delay
    ///
    /// # Tradeoffs
    ///
    /// Uses `std::thread::sleep`, which is efficient for longer delays and doesn't consume CPU, but is imprecise for short waits (<2ms) and blocks the thread. For high-throughput or concurrent IO chains, prefer `delay_efficient` for sub-millisecond precision, or consider async IO for non-blocking.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::io::IO;
    ///
    /// // Create an IO operation that delays for 1 second and returns 42
    /// let io_operation = IO::delay(std::time::Duration::from_secs(1), 42);
    ///
    /// // Run the IO operation
    /// let result = io_operation.run();
    /// assert_eq!(result, 42);
    /// ```
    #[inline]
    pub fn delay(duration: std::time::Duration, value: A) -> Self {
        IO::new(move || {
            std::thread::sleep(duration);
            value.clone()
        })
    }

    /// Creates a new IO operation that delays execution for a specified duration using spin-based sleeping.
    ///
    /// This is similar to `delay` but uses the `spin_sleep` crate for more precise, non-blocking timing for short durations.
    ///
    /// # Tradeoffs
    ///
    /// Uses busy-waiting (spinning), which gives high precision for sub-millisecond waits and avoids thread context switching, but consumes CPU while waiting. Best for short, high-precision delays in large IO chains. For longer delays or when CPU efficiency is critical, prefer `delay` or async IO.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::io::IO;
    /// use std::time::Duration;
    ///
    /// // Create an IO operation that uses spin_sleep for precise timing
    /// let io_operation = IO::delay_efficient(Duration::from_micros(500), 42);
    ///
    /// // Run the IO operation (uses spin sleep for better precision)
    /// let result = io_operation.run();
    /// assert_eq!(result, 42);
    /// ```
    #[inline]
    pub fn delay_efficient(duration: std::time::Duration, value: A) -> Self {
        IO::new(move || {
            SpinSleeper::new(0).sleep(duration);
            value.clone()
        })
    }
}

// Implement HKT for IO
impl<A> crate::traits::hkt::HKT for IO<A> {
    type Source = A;
    type Output<U> = IO<U>;
}

// Implement Evaluate for IO
impl<A: Clone + 'static> crate::traits::evaluate::Evaluate for IO<A> {
    #[inline]
    fn evaluate(&self) -> Self::Source {
        self.run()
    }
}
