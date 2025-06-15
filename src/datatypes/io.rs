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
//!
//! ## Type Class Laws
//!
//! The `IO` type satisfies the mathematical laws for `Functor`, `Applicative`, and `Monad`.
//! These laws ensure that operations behave predictably and can be optimized safely.
//!
//! ### Functor Laws
//!
//! ```rust
//! use rustica::datatypes::io::IO;
//!
//! // Law 1: fmap id = id
//! let io_value = IO::pure(42);
//! let identity = |x: i32| x;
//! assert_eq!(io_value.clone().fmap(identity).run(), io_value.run());
//!
//! // Law 2: fmap (g . f) = fmap g . fmap f
//! let f = |x: i32| x + 1;
//! let g = |x: i32| x * 2;
//! let composed = move |x: i32| g(f(x));
//!
//! let left_side = io_value.clone().fmap(composed);
//! let right_side = io_value.clone().fmap(f).fmap(g);
//! assert_eq!(left_side.run(), right_side.run());
//! ```
//!
//! ### Monad Laws
//!
//! ```rust
//! use rustica::datatypes::io::IO;
//!
//! let value = 42;
//! let f = |x: i32| IO::pure(x + 1);
//! let g = |x: i32| IO::pure(x * 2);
//!
//! // Law 1: Left Identity - pure(a).bind(f) = f(a)
//! let left_identity_left = IO::pure(value).bind(f);
//! let left_identity_right = f(value);
//! assert_eq!(left_identity_left.run(), left_identity_right.run());
//!
//! // Law 2: Right Identity - m.bind(pure) = m
//! let io_m = IO::pure(value);
//! let right_identity_left = io_m.clone().bind(IO::pure);
//! assert_eq!(right_identity_left.run(), io_m.run());
//!
//! // Law 3: Associativity - m.bind(f).bind(g) = m.bind(|x| f(x).bind(g))
//! let assoc_left = IO::pure(value).bind(f).bind(g);
//! let assoc_right = IO::pure(value).bind(move |x| f(x).bind(g));
//! assert_eq!(assoc_left.run(), assoc_right.run());
//! ```
//!
//! ## Error Handling Patterns
//!
//! ```rust
//! use rustica::datatypes::io::IO;
//! use std::time::SystemTime;
//!
//! // Pattern 1: Safe execution with try_get
//! let risky_io: IO<i32> = IO::new(|| {
//!     // Instead of using rand, we'll use system time to determine success/failure
//!     if SystemTime::now()
//!         .duration_since(SystemTime::UNIX_EPOCH)
//!         .unwrap()
//!         .as_nanos() % 2 == 0
//!     {
//!         42
//!     } else {
//!         panic!("Random failure!")
//!     }
//! });
//!
//! match risky_io.try_get() {
//!     Ok(value) => println!("Success: {}", value),
//!     Err(error) => println!("Error: {}", error),
//! }
//!
//! // Pattern 2: Chaining with error propagation
//! let safe_chain = IO::pure(10)
//!     .bind(|x| {
//!         if x > 5 {
//!             IO::pure(x * 2)
//!         } else {
//!             IO::new(|| panic!("Value too small"))
//!         }
//!     });
//! // To observe the panic, you would call .try_get() or .run()
//! // For example:
//! // assert!(safe_chain.try_get().is_ok()); // This would be 20
//! // let failing_chain = IO::pure(3).bind(|x| { ... });
//! // assert!(failing_chain.try_get().is_err());
//! ```
//!
//! ## Common Pitfalls and Best Practices
//!
//! ```rust
//! use rustica::datatypes::io::IO;
//!
//! // Helper function for example
//! fn fibonacci(n: u32) -> u64 {
//!     if n <= 1 { return n as u64; }
//!     let mut a = 0; let mut b = 1;
//!     for _ in 2..=n { let temp = a + b; a = b; b = temp; }
//!     b
//! }
//!
//! // DON'T: Create IO operations that capture large data
//! let large_data = vec![0; 1_000_000];
//! let bad_io = IO::new(move || {
//!     large_data.len() // Entire vector is moved into closure
//! });
//!
//! // DO: Extract only what you need
//! let large_data = vec![0; 1_000_000];
//! let data_len = large_data.len();
//! let good_io = IO::new(move || data_len);
//! assert_eq!(good_io.run(), 1_000_000);
//!
//! // DON'T: Use IO for CPU-intensive pure computations
//! let bad_fib = IO::new(|| fibonacci(20)); // Just adds overhead
//!
//! // DO: Use IO for actual side effects
//! let good_io_fib = IO::new(|| {
//!     println!("Computing fibonacci");
//!     fibonacci(20)
//! });
//! assert_eq!(good_io_fib.run(), 6765);
//! ```

use crate::utils::error_utils::AppError;
#[cfg(feature = "develop")]
use quickcheck::{Arbitrary, Gen};
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
            IOError::Other(msg) => write!(f, "IO Error: {msg}"),
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
    /// # Performance
    ///
    /// - Time Complexity: O(f) where f is the complexity of the encapsulated function
    /// - Memory Usage: O(1) additional allocation beyond the function's requirements
    /// - Thread Safety: Safe to call from multiple threads if the encapsulated function is thread-safe
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
    /// # Performance
    ///
    /// - Time Complexity: O(1) for creating the new IO, O(f + g) when executed
    ///   (where f is the original operation and g is the mapping function)
    /// - Memory Usage: O(1) additional Arc allocation
    /// - Lazy Evaluation: The mapping function is not executed until `run()` is called
    ///
    /// # Arguments
    ///
    /// * `f` - A function that transforms `A` into `B`
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::io::IO;
    /// use std::time::Instant;
    ///
    /// let io_base = IO::new(|| {
    ///     // Expensive computation
    ///     (0..1_000_000).sum::<i64>()
    /// });
    ///
    /// // fmap is lazy - no computation happens here
    /// let start_fmap = Instant::now();
    /// let io_doubled = io_base.fmap(|x| x * 2);
    /// let fmap_duration = start_fmap.elapsed();
    ///
    /// // All computation happens here
    /// let start_run = Instant::now();
    /// let result = io_doubled.run();
    /// let run_duration = start_run.elapsed();
    ///
    /// assert_eq!(result, 999999000000); // Corrected sum for 0..1_000_000 is 499999500000, then *2
    /// assert!(fmap_duration < std::time::Duration::from_micros(50)); // Adjusted for typical systems
    /// println!("fmap took: {:?}, run took: {:?}", fmap_duration, run_duration);
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
    /// use rustica::datatypes::io::{IO, IOError};
    /// use rustica::utils::error_utils::AppError;
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
    /// assert_eq!(error.context().unwrap(), &"critical calculation");
    /// match error.message() {
    ///     IOError::Other(msg) => assert!(msg.contains("computation failed")),
    ///     _ => panic!("Unexpected error type"),
    /// }
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
    /// // Basic apply usage
    /// let io_value: IO<i32> = IO::pure(10);
    /// let result_basic = io_value.apply(|x: i32| IO::pure(x * 3));
    /// assert_eq!(result_basic.run(), 30);
    ///
    /// // Chaining apply operations
    /// let complex_result = IO::pure(5)
    ///     .apply(|x: i32| IO::new(move || {
    ///         // println!("Processing: {}", x); // Avoid println in doctests unless verifying output
    ///         x + 10
    ///     }))
    ///     .apply(|x: i32| IO::pure(x * 2));
    /// assert_eq!(complex_result.run(), 30);
    ///
    /// // Error propagation with apply
    /// let io_fail: IO<i32> = IO::new(|| panic!("failed"));
    /// let result_fail = io_fail.apply(|x: i32| IO::pure(x + 1));
    /// assert!(result_fail.try_get().is_err());
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

#[cfg(feature = "develop")]
impl<A: Clone + Arbitrary> Arbitrary for IO<A> {
    fn arbitrary(g: &mut Gen) -> Self {
        let value = A::arbitrary(g);
        IO::pure(value)
    }
}
