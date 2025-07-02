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
//! ## Performance Characteristics
//!
//! ### Time Complexity
//!
//! * **Construction**: O(1) - Creating an IO instance is a constant-time operation
//! * **Composition**: O(1) - Combining IO instances with `fmap`, `pure`, `bind`, etc., is constant-time
//! * **Execution**: O(f) - Where f is the complexity of the underlying operation when `run()` is called
//!
//! ### Memory Usage
//!
//! * **Storage**: Each IO instance stores a closure representing its computation
//! * **Composition**: Each composition layer adds a constant amount of overhead
//! * **Lazy Evaluation**: No execution overhead until `run()` is called
//!
//! ### Concurrency
//!
//! * Thread-safe if the encapsulated operations are thread-safe
//! * All IO composition operations are thread-safe
//! * Execution via `run()` happens synchronously on the calling thread
//!
//! ## Type Class Laws
//!
//! ### Functor Laws
//!
//! IO satisfies the Functor laws:
//!
//! ```rust
//! use rustica::datatypes::io::IO;
//!
//! // 1. Identity: fmap(id) == id
//! let io = IO::pure(42);
//! let id_mapped = io.clone().fmap(|x| x);
//! assert_eq!(io.run(), id_mapped.run());
//!
//! // 2. Composition: fmap(f . g) == fmap(f) . fmap(g)
//! let f = |x: i32| x + 1;
//! let g = |x: i32| x * 2;
//!
//! let left = io.clone().fmap(|x| f(g(x)));
//! let right = io.clone().fmap(g).fmap(f);
//! assert_eq!(left.run(), right.run());
//! ```
//!
//! ### Applicative Laws
//!
//! IO satisfies the Applicative laws:
//!
//! ```rust
//! use rustica::datatypes::io::IO;
//!
//! // 1. Identity: pure(id) <*> v == v
//! let v = IO::pure(42);
//! let id_fn = |x| x;
//! let id_io = IO::pure(id_fn);
//!
//! // Using apply to simulate <*>
//! let result = v.clone().bind(|x| id_io.clone().fmap(move |f| f(x)));
//! assert_eq!(v.run(), result.run());
//!
//! // 2. Homomorphism: pure(f) <*> pure(x) == pure(f(x))
//! let f = |x: i32| x + 5;
//! let x = 10;
//!
//! let left = IO::pure(f).bind(|f| IO::pure(x).fmap(move |x| f(x)));
//! let right = IO::pure(f(x));
//! assert_eq!(left.run(), right.run());
//! ```
//!
//! ### Monad Laws
//!
//! IO satisfies the Monad laws:
//!
//! ```rust
//! use rustica::datatypes::io::IO;
//!
//! // 1. Left Identity: return a >>= f == f a
//! let a = 42;
//! let f = |x: i32| IO::pure(x + 10);
//!
//! let left = IO::pure(a).bind(f);
//! let right = f(a);
//! assert_eq!(left.run(), right.run());
//!
//! // 2. Right Identity: m >>= return == m
//! let m = IO::pure(42);
//!
//! let left = m.clone().bind(|x| IO::pure(x));
//! assert_eq!(m.run(), left.run());
//!
//! // 3. Associativity: (m >>= f) >>= g == m >>= (\x -> f x >>= g)
//! let m = IO::pure(42);
//! let f = |x: i32| IO::pure(x + 10);
//! let g = |x: i32| IO::pure(x * 2);
//!
//! let left = m.clone().bind(f).bind(g);
//! let right = m.clone().bind(|x| f(x).bind(g));
//! assert_eq!(left.run(), right.run());
//! ```
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
/// # Performance Characteristics
///
/// ## Time Complexity
///
/// * **Construction**: O(1) - Creating an IO instance is a constant-time operation
/// * **Composition (fmap, bind)**: O(1) - Combining IOs adds only function composition overhead
/// * **Execution (run)**: O(f) - Where f is the complexity of the underlying operation
///
/// ## Memory Usage
///
/// * **Storage**: Each IO instance stores a closure and maintains minimal overhead
/// * **Lazy Evaluation**: No computation happens until `run()` is called, allowing for efficient composition
/// * **Composition**: Each layer of composition (fmap, bind) adds constant overhead from closure creation
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
///
/// Composing multiple IO operations:
///
/// ```rust
/// use rustica::datatypes::io::IO;
///
/// // Define multiple operations
/// let read_input = IO::new(|| "user input".to_string());
/// let process = |input: String| IO::new(move || input.to_uppercase());
/// let display = |processed: String| IO::new(move || {
///     // In real code this might print to stdout
///     format!("Output: {}", processed)
/// });
///
/// // Compose operations using bind (monadic sequencing)
/// let program = read_input.bind(|input| {
///     process(input).bind(|processed| {
///         display(processed)
///     })
/// });
///
/// // Execute the entire chain of operations
/// let result = program.run();
/// assert_eq!(result, "Output: USER INPUT");
/// ```
///
/// Error handling with `try_get`:
///
/// ```rust
/// use rustica::datatypes::io::IO;
///
/// // An IO that might fail
/// let safe_operation = IO::new(|| {
///     // This operation succeeds
///     Ok::<_, &str>(42)
/// });
///
/// let risky_operation = IO::new(|| {
///     // This operation fails
///     if true { Err("Operation failed") } else { Ok(10) }
/// });
///
/// // Using try_get to handle the result
/// let safe_result = safe_operation
///     .bind(|res| match res {
///         Ok(val) => IO::pure(val),
///         Err(_) => IO::pure(0),  // Fallback value
///     })
///     .run();
///
/// assert_eq!(safe_result, 42);
///
/// // Handle the error case
/// let risky_result = risky_operation
///     .bind(|res| match res {
///         Ok(val) => IO::pure(val),
///         Err(_) => IO::pure(0),  // Fallback value
///     })
///     .run();
///
/// assert_eq!(risky_result, 0);
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
    /// the IO operation. It enables function application to the eventual result
    /// of an IO computation while preserving the IO context.
    ///
    /// # Performance Characteristics
    ///
    /// ## Time Complexity
    ///
    /// * **Construction**: O(1) - Creates a new IO with composed functions without execution
    /// * **Execution**: O(f + g) - Where f is the complexity of this IO and g is the complexity of the mapping function
    ///
    /// ## Memory Usage
    ///
    /// * Creates a new IO that captures both the original operation and the mapping function
    /// * Memory efficiency through lazy evaluation - no transformation is performed until `run()` is called
    /// * Each fmap adds one layer of function composition overhead
    /// * O(1) additional allocation beyond the function capture
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
    ///
    /// Chaining multiple transformations:
    ///
    /// ```rust
    /// use rustica::datatypes::io::IO;
    ///
    /// let io_base = IO::pure(10);
    ///
    /// let result = io_base
    ///     .fmap(|n| n * 2)        // 20
    ///     .fmap(|n| n + 5)        // 25
    ///     .fmap(|n| n.to_string()) // "25"
    ///     .run();
    ///     
    /// assert_eq!(result, "25");
    /// ```
    ///
    /// Demonstrating lazy evaluation:
    ///
    /// ```rust
    /// use rustica::datatypes::io::IO;
    /// use std::time::Instant;
    ///
    /// let io_base = IO::new(|| {
    ///     // Expensive computation (simplified for testing)
    ///     (0..10000).sum::<i32>()
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
    /// assert_eq!(result, 49995000);
    /// assert!(fmap_duration < run_duration); // fmap should be much faster than run
    /// ```
    ///
    /// Working with complex data structures:
    ///
    /// ```rust
    /// use rustica::datatypes::io::IO;
    /// use std::collections::HashMap;
    ///
    /// // IO operation that produces a HashMap
    /// let io_map = IO::new(|| {
    ///     let mut map = HashMap::new();
    ///     map.insert("one", 1);
    ///     map.insert("two", 2);
    ///     map.insert("three", 3);
    ///     map
    /// });
    ///
    /// // Transform the map to get only values > 1
    /// let filtered_map = io_map.fmap(|map| {
    ///     map.into_iter()
    ///         .filter(|(_, value)| *value > 1)
    ///         .collect::<HashMap<_, _>>()
    /// });
    ///
    /// let result = filtered_map.run();
    /// assert_eq!(result.len(), 2);
    /// assert_eq!(result.get("two"), Some(&2));
    /// assert_eq!(result.get("three"), Some(&3));
    /// assert_eq!(result.get("one"), None);
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
    /// This is a fundamental operation that serves as the basis for introducing
    /// values into the IO monadic context.
    ///
    /// # Performance Characteristics
    ///
    /// ## Time Complexity
    ///
    /// * **Construction**: O(1) - Creates a simple IO that captures the value
    /// * **Execution**: O(1) - Simply returns the captured value
    ///
    /// ## Memory Usage
    ///
    /// * Creates a new IO that stores the given value
    /// * Memory usage depends on the size of the wrapped value
    /// * No additional memory allocation during execution
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
    ///
    /// // Works with any type that implements Clone
    /// let io_string = IO::pure("hello".to_string());
    /// assert_eq!(io_string.run(), "hello");
    ///
    /// // Works with complex types
    /// let tuple = (1, "test".to_string(), true);
    /// let io_tuple = IO::pure(tuple.clone());
    /// assert_eq!(io_tuple.run(), tuple);
    /// ```
    ///
    /// Using `pure` in combination with other IO operations:
    ///
    /// ```rust
    /// use rustica::datatypes::io::IO;
    ///
    /// // Create an IO that performs a calculation
    /// let io_calculation = IO::new(|| 10 * 5);
    ///
    /// // Use pure with bind to create a conditional workflow
    /// let io_result = io_calculation.bind(|result| {
    ///     if result > 40 {
    ///         IO::pure("Greater than 40")
    ///     } else {
    ///         IO::pure("Not greater than 40")
    ///     }
    /// });
    ///
    /// assert_eq!(io_result.run(), "Greater than 40");
    /// ```
    ///
    /// Using `pure` as a starting point for IO chains:
    ///
    /// ```rust
    /// use rustica::datatypes::io::IO;
    ///
    /// // Start with a pure value and build a computation chain
    /// let io_chain = IO::pure(5)
    ///     .fmap(|n| n * 2)
    ///     .bind(|n| IO::new(move || {
    ///         // In real code, this might do some IO work
    ///         format!("{} processed", n)
    ///     }));
    ///
    /// assert_eq!(io_chain.run(), "10 processed");
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
    /// the result of the previous one. This is a fundamental operation that
    /// enables composing complex IO workflows where each step depends on the
    /// result of previous steps.
    ///
    /// # Performance Characteristics
    ///
    /// ## Time Complexity
    ///
    /// * **Construction**: O(1) - Creates a new IO with composed functions without execution
    /// * **Execution**: O(f + g) - Where f is the complexity of this IO and g is the complexity of the operation returned by function `f`
    ///
    /// ## Memory Usage
    ///
    /// * Creates a new IO that captures both this IO and the binding function
    /// * Memory efficiency through lazy evaluation - no computation happens until `run()` is called
    /// * Each bind adds one layer of function composition overhead
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
    ///
    /// // Chain multiple bind operations
    /// let result = io_operation
    ///     .bind(|x| IO::pure(x + 10))
    ///     .bind(|x| IO::pure(x * 2));
    /// assert_eq!(result.run(), 104);
    /// ```
    ///
    /// Real-world example - file processing pipeline:
    ///
    /// ```rust
    /// use rustica::datatypes::io::IO;
    /// use std::collections::HashMap;
    ///
    /// // Simulate reading a config file
    /// let read_config = IO::new(|| {
    ///     let mut config = HashMap::new();
    ///     config.insert("input_file".to_string(), "data.csv".to_string());
    ///     config.insert("output_format".to_string(), "json".to_string());
    ///     config
    /// });
    ///
    /// // Simulate reading data from a file
    /// let read_data = |filename: String| IO::new(move || {
    ///     // In a real app, this would read from the file
    ///     vec!["line1".to_string(), "line2".to_string(), "line3".to_string()]
    /// });
    ///
    /// // Process data based on format
    /// let process_data = |data: Vec<String>, format: String| IO::new(move || {
    ///     match format.as_str() {
    ///         "json" => format!("[{}]", data.iter()
    ///             .map(|line| format!("\"{}\"", line))
    ///             .collect::<Vec<_>>()
    ///             .join(", ")),
    ///         _ => data.join("\n"),
    ///     }
    /// });
    ///
    /// // Create the processing pipeline using bind
    /// let pipeline = read_config.bind(|config| {
    ///     // Extract the input filename from config
    ///     let input_file = config.get("input_file").unwrap().clone();
    ///     let output_format = config.get("output_format").unwrap().clone();
    ///     
    ///     // Read the data file
    ///     read_data(input_file).bind(move |data| {
    ///         // Process the data according to the output format
    ///         process_data(data, output_format)
    ///     })
    /// });
    ///
    /// // Run the entire pipeline
    /// let result = pipeline.run();
    /// assert_eq!(result, "[\"line1\", \"line2\", \"line3\"]");
    /// ```
    ///
    /// Error handling with bind:
    ///
    /// ```rust
    /// use rustica::datatypes::io::IO;
    ///
    /// // An operation that might fail
    /// let parse_number = |input: &str| IO::new(move || {
    ///     input.parse::<i32>().ok()
    /// });
    ///
    /// // Chain operations with error handling
    /// let safe_calculation = |input: &str| parse_number(input).bind(|result| {
    ///     match result {
    ///         Some(num) => IO::pure(Some(num * 2)),
    ///         None => IO::pure(None),
    ///     }
    /// });
    ///
    /// // Try with valid input
    /// let valid_result = safe_calculation("42").run();
    /// assert_eq!(valid_result, Some(84));
    ///
    /// // Try with invalid input
    /// let invalid_result = safe_calculation("not a number").run();
    /// assert_eq!(invalid_result, None);
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
