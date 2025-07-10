//! # Reader Monad
//!
//! The Reader monad represents computations that depend on some environment or configuration.
//! It provides a way to thread an environment through a computation without explicitly passing
//! it as a parameter to every function.
//!
//! ## Functional Programming Context
//!
//! In functional programming, the Reader monad is part of the core set of primitive monads
//! commonly used across different functional languages. It serves several important roles:
//!
//! - **Dependency Injection**: Reader provides a functional approach to dependency injection without
//!   relying on mutable state or global variables.
//! - **Environmental Effects**: It represents computations that need to read from a shared context
//!   without modifying it, forming part of the "effects system" in pure FP.
//! - **Function Environment**: Reader can be understood as a generalization of curried functions,
//!   allowing a more composable way to provide configuration to functions.
//!
//!
//! ## Core Concepts
//!
//! - **Environment Access**: Functions can access a shared read-only environment
//! - **Environment Modification**: Functions can run in a modified environment without affecting others
//! - **Composition**: Sequential operations share the same environment
//!
//! ## Performance Characteristics
//!
//! ### Time Complexity
//!
//! - **Construction (new)**: O(1) - Constant time to create a Reader instance
//! - **Environment Access (ask)**: O(1) - Constant time to capture the environment
//! - **Function Application (run_reader)**: O(f) - Where f is the complexity of the wrapped function
//! - **Composition (fmap/bind)**: O(f + g) - Where f and g are the complexities of the composed functions
//!
//! ### Memory Usage
//!
//! - **Structure**: Size of Reader<E, A> = size of a function pointer + any captured state
//! - **Implementation Detail**: Uses a function closure as the internal representation
//!
//! ## Functional Programming Context
//!
//! In functional programming, the Reader monad provides a way to pass a shared context
//! or configuration to a group of functions without explicitly threading it through
//! every function call. This creates cleaner, more composable code, particularly when
//! dealing with deeply nested function calls that all need access to some shared data.
//!
//! ## Type Class Implementations
//!
//! The Reader monad implements several important functional programming type classes:
//!
//! - **Functor**: Reader implements the Functor type class through its `fmap` method,
//!   which transforms the result value of a Reader while preserving the environment.
//!   - Implementation: `fmap :: (A -> B) -> Reader<E, A> -> Reader<E, B>`
//!
//! - **Applicative**: While not explicitly implemented with this name, Reader supports
//!   applicative operations through its `pure` and `apply`/`lift` functions.
//!   - `pure`: Creates a Reader that ignores the environment and returns a constant value
//!     - Implementation: `pure :: A -> Reader<E, A>`
//!   
//!   - `apply`: Applies a function from one Reader to a value from another Reader
//!     - Implementation: `apply :: Reader<E, A -> B> -> Reader<E, A> -> Reader<E, B>`
//!
//! - **Monad**: Reader implements the Monad type class through its `bind` method, which
//!   allows chaining operations that depend on both the environment and previous results.
//!   - Implementation: `bind :: Reader<E, A> -> (A -> Reader<E, B>) -> Reader<E, B>`
//!
//! ## Type Class Laws
//!
//! ### Functor Laws
//!
//! 1. **Identity Law**: `fmap(id) = id`
//! 2. **Composition Law**: `fmap(f . g) = fmap(f) . fmap(g)`
//!
//! ### Monad Laws
//!
//! 1. **Left Identity**: `pure(a).bind(f) = f(a)`
//! 2. **Right Identity**: `m.bind(pure) = m`
//! 3. **Associativity**: `m.bind(f).bind(g) = m.bind(x => f(x).bind(g))`
//!
//! ## Use Cases
//!
//! The Reader monad is particularly useful for:
//!
//! - **Configuration Management**: Providing access to application settings
//! - **Dependency Injection**: Supplying dependencies to functions
//! - **Environment Access**: Accessing shared read-only context
//! - **Testing**: Making code more testable by parameterizing the environment
//!
//! ## Function-Level Documentation
//!
//! Refer to the documentation for specific functions to see practical examples demonstrating:
//! - Type class law compliance
//! - Usage patterns
//! - Environment access and modification
//! - Composition of Reader operations
//! - Integration with other monadic operations
//!
//! ### Modifying the Environment
//!
//! ```rust
//! use rustica::datatypes::reader::Reader;
//!
//! // A reader that depends on a string environment
//! let reader = Reader::new(|s: String| s.len());
//!
//! // Modify the environment before running the reader
//! let modified = reader.local(|s| s.to_uppercase());
//!
//! assert_eq!(modified.run_reader("hello".to_string()), 5);
//! assert_eq!(reader.run_reader("hello".to_string()), 5);
//! ```

use crate::datatypes::id::Id;
use crate::prelude::*;
use crate::transformers::ReaderT;
#[cfg(feature = "full")]
use quickcheck::{Arbitrary, Gen};

/// The Reader monad represents computations that depend on some environment value.
/// It enables functions to access a shared environment without passing it explicitly as a parameter.
///
/// # Performance Characteristics
///
/// ## Time Complexity
///
/// * **Construction**: O(1) - Only wraps a function reference
/// * **Execution** (`run_reader`): O(f) - Where f is the complexity of the wrapped function
/// * **Transformation** (`fmap`, `bind`): O(1) for construction, O(f + g) when executed where:
///   - f is the complexity of the original reader function
///   - g is the complexity of the applied function
///
/// ## Memory Usage
///
/// * **Storage**: Contains a single `ReaderT` transformer with an `Id` monad
/// * **Lazy Evaluation**: Operations are composed without immediate execution
/// * **Function Composition**: Each transformation adds a layer of function composition,
///   but no intermediate results are stored until `run_reader` is called
///
/// # When to Use
///
/// * When multiple functions need access to a shared environment
/// * For dependency injection without using global state
/// * When you want to compose operations that all depend on the same context
/// * To make testing easier by substituting different environments
///
/// # Type Parameters
///
/// * `E` - The environment type
/// * `A` - The result type
///
/// # Examples
///
/// Basic usage:
///
/// ```rust
/// use rustica::datatypes::reader::Reader;
///
/// // Create a reader that doubles the environment value
/// let reader: Reader<i32, i32> = Reader::new(|e: i32| e * 2);
/// assert_eq!(reader.run_reader(21), 42);
///
/// // Transform the result using fmap
/// let string_reader: Reader<i32, String> = reader.fmap(|x| x.to_string());
/// assert_eq!(string_reader.run_reader(21), "42");
/// ```
///
/// Using with a complex environment:
///
/// ```rust
/// use rustica::datatypes::reader::Reader;
///
/// // Application configuration
/// #[derive(Clone)]
/// struct Config {
///     base_url: String,
///     timeout_ms: u32,
///     retry_count: u8,
/// }
///
/// // Service that depends on configuration
/// struct ApiService {
///     url_reader: Reader<Config, String>,
///     timeout_reader: Reader<Config, u32>,
/// }
///
/// impl ApiService {
///     fn new() -> Self {
///         ApiService {
///             url_reader: Reader::asks(|config: Config| config.base_url.clone()),
///             timeout_reader: Reader::asks(|config: Config| config.timeout_ms),
///         }
///     }
///     
///     // Compose readers to build a connection string
///     fn connection_string(&self) -> Reader<Config, String> {
///         self.url_reader.combine(&self.timeout_reader, |url, timeout| {
///             format!("{} (timeout: {}ms)", url, timeout)
///         })
///     }
/// }
///
/// // Create the service
/// let service = ApiService::new();
///
/// // Run with a specific configuration
/// let config = Config {
///     base_url: "https://api.example.com".to_string(),
///     timeout_ms: 3000,
///     retry_count: 3,
/// };
///
/// // Get the connection string
/// let conn_str = service.connection_string().run_reader(config);
/// assert_eq!(conn_str, "https://api.example.com (timeout: 3000ms)");
/// ```
#[repr(transparent)]
pub struct Reader<E, A> {
    inner: ReaderT<E, Id<A>, A>,
}

impl<E, A> Reader<E, A>
where
    E: Clone + Send + Sync + 'static,
    A: Clone + Send + Sync + 'static,
    Id<A>: HKT<Source = A, Output<A> = Id<A>> + Monad,
{
    /// Creates a new Reader monad from a function that depends on an environment.
    ///
    /// # Parameters
    ///
    /// * `f` - Function that takes an environment and returns a value
    ///
    /// # Returns
    ///
    /// A new Reader monad
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::reader::Reader;
    ///
    /// // Create a reader that doubles the environment value
    /// let reader: Reader<i32, i32> = Reader::new(|n: i32| n * 2);
    /// assert_eq!(reader.run_reader(21), 42);
    /// ```
    #[inline]
    pub fn new<F>(f: F) -> Self
    where
        F: Fn(E) -> A + Clone + Send + Sync + 'static,
    {
        Reader {
            inner: ReaderT::new(move |e: E| Id::new(f(e))),
        }
    }

    /// Runs this Reader with the given environment, returning the final value.
    ///
    /// # Parameters
    ///
    /// * `env` - The environment to run the Reader with
    ///
    /// # Returns
    ///
    /// The result of running the Reader with the given environment
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::reader::Reader;
    ///
    /// let reader: Reader<i32, i32> = Reader::new(|n: i32| n * 2);
    /// assert_eq!(reader.run_reader(21), 42);
    /// ```
    #[inline]
    pub fn run_reader(&self, env: E) -> A {
        let id_value = self.inner.run_reader(env);
        id_value.value().clone()
    }

    /// Maps a function over the value produced by this Reader, implementing the Functor typeclass.
    /// This allows transforming the output of a Reader without affecting its environment dependency.
    ///
    /// # Performance Characteristics
    ///
    /// ## Time Complexity
    ///
    /// * **Construction**: O(1) - Only creates a new Reader with composed functions
    /// * **Execution**: O(f + g) - Where f is the complexity of the original Reader's function and
    ///   g is the complexity of the mapping function
    ///
    /// ## Memory Usage
    ///
    /// * Creates a new Reader with a closure that captures both the original Reader and the mapping function
    /// * Memory efficiency through lazy evaluation - no transformation is performed until `run_reader` is called
    /// * The mapping function is stored as part of the Reader's closure
    ///
    /// # Parameters
    ///
    /// * `f` - Function to apply to the value produced by this Reader
    ///
    /// # Returns
    ///
    /// A new Reader that applies the function to the result of the original Reader
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::reader::Reader;
    /// use rustica::datatypes::id::Id;
    ///
    /// let reader: Reader<i32, i32> = Reader::new(|n: i32| n + 10);
    /// let mapped: Reader<i32, String> = reader.fmap(|n| n.to_string());
    /// assert_eq!(mapped.run_reader(5), "15");
    /// ```
    pub fn fmap<B, F>(&self, f: F) -> Reader<E, B>
    where
        F: Fn(A) -> B + Clone + Send + Sync + 'static,
        B: Clone + Send + Sync + 'static,
        Id<B>: HKT<Source = B, Output<B> = Id<B>> + Monad,
    {
        let inner_clone = self.inner.clone();

        Reader {
            inner: ReaderT::new(move |e: E| {
                let id_a = inner_clone.run_reader(e);
                let a = id_a.value();
                Id::new(f(a.clone()))
            }),
        }
    }

    /// Sequences two Reader computations, passing the result of the first to the second.
    /// This is the core method that implements the Monad typeclass, allowing for chained
    /// operations where each operation can depend on the result of the previous one.
    ///
    /// # Performance Characteristics
    ///
    /// ## Time Complexity
    ///
    /// * **Construction**: O(1) - Only creates a new Reader with composed functions
    /// * **Execution**: O(f + g) - Where f is the complexity of the original Reader's function and
    ///   g is the complexity of the binding function
    ///
    /// ## Memory Usage
    ///
    /// * Creates a new Reader with a closure that captures both the original Reader and the binding function
    /// * Memory efficiency is maintained by lazy evaluation - no intermediate results are stored until
    ///   `run_reader` is called
    /// * Each bind adds a layer of function composition to the call stack when executed
    ///
    /// # Parameters
    ///
    /// * `f` - Function that takes the result of this Reader and returns a new Reader
    ///
    /// # Returns
    ///
    /// A new Reader that represents the sequential computation
    ///
    /// # Example
    ///
    /// ```rust
    /// use rustica::datatypes::reader::Reader;
    ///
    /// let reader: Reader<i32, i32> = Reader::new(|n: i32| n + 5);
    /// let bound: Reader<i32, i32> = reader.bind(|n| Reader::new(move |env: i32| env * n));
    /// assert_eq!(bound.run_reader(10), 150); // (10 + 5) * 10 = 150
    /// ```
    pub fn bind<B, F>(&self, f: F) -> Reader<E, B>
    where
        F: Fn(A) -> Reader<E, B> + Clone + Send + Sync + 'static,
        B: Clone + Send + Sync + 'static,
        Id<B>: HKT<Source = B, Output<B> = Id<B>> + Monad,
    {
        let inner_clone = self.inner.clone();

        Reader {
            inner: ReaderT::new(move |e: E| {
                let id_a = inner_clone.run_reader(e.clone());
                let a = id_a.value().clone();
                let reader_b = f(a);
                reader_b.inner.run_reader(e)
            }),
        }
    }

    /// Creates a Reader that returns the environment itself. This is a fundamental operation
    /// for the Reader monad, allowing direct access to the environment.
    ///
    /// # Performance Characteristics
    ///
    /// ## Time Complexity
    ///
    /// * **Construction**: O(1) - Creates a simple Reader that just returns the environment
    /// * **Execution**: O(1) - Simply returns the environment without transformation
    ///
    /// ## Memory Usage
    ///
    /// * Creates a minimal Reader that just returns the environment value
    /// * No additional memory allocation during execution beyond the environment itself
    /// * If `E` (environment type) doesn't implement `Clone` efficiently, consider using `asks` instead
    ///
    /// # Type Requirements
    ///
    /// * `E`: The environment type must implement `Clone`
    /// * `A`: The result type must be able to be created `From<E>` (must implement the `From<E>` trait)
    ///
    /// # Returns
    ///
    /// A Reader that returns the environment as its result
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::reader::Reader;
    ///
    /// let reader: Reader<String, String> = Reader::ask();
    /// assert_eq!(reader.run_reader("hello".to_string()), "hello");
    /// ```
    #[inline]
    pub fn ask() -> Self
    where
        E: Clone,
        A: From<E>,
    {
        Reader {
            inner: ReaderT::new(move |e: E| Id::new(A::from(e))),
        }
    }

    /// Creates a Reader that returns the environment itself with a transformation function.
    ///
    /// # Parameters
    ///
    /// * `f` - Function to transform the environment into a value
    ///
    /// # Returns
    ///
    /// A Reader that returns the transformed environment
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::reader::Reader;
    ///
    /// let reader: Reader<String, String> = Reader::ask_transform(|env: String| env);
    /// assert_eq!(reader.run_reader("hello".to_string()), "hello");
    /// ```
    #[inline]
    pub fn ask_transform<F>(f: F) -> Self
    where
        F: Fn(E) -> A + Clone + Send + Sync + 'static,
    {
        Reader {
            inner: ReaderT::new(move |e: E| Id::new(f(e))),
        }
    }

    /// Creates a Reader that returns a value derived from the environment. This is a fundamental
    /// operation that allows for selective access to the environment, extracting or transforming
    /// only the parts needed.
    ///
    /// # Performance Characteristics
    ///
    /// ## Time Complexity
    ///
    /// * **Construction**: O(1) - Creates a Reader that wraps the selector function
    /// * **Execution**: O(f) - Where f is the complexity of the selector function
    ///
    /// ## Memory Usage
    ///
    /// * Creates a Reader that stores the selector function
    /// * More memory-efficient than `ask()` when only part of the environment is needed
    /// * Avoids unnecessary cloning of the entire environment when only a subset is required
    /// * Particularly useful when working with large environment structures
    ///
    /// # Use Cases
    ///
    /// * Extracting specific fields from a configuration
    /// * Converting environment values into different types
    /// * Focusing on a subset of a large environment
    /// * Performing calculations based on the environment
    ///
    /// # Parameters
    ///
    /// * `selector` - Function to extract or transform a value from the environment
    ///
    /// # Returns
    ///
    /// A Reader that returns a value derived from the environment
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```rust
    /// use rustica::datatypes::reader::Reader;
    ///
    /// let reader: Reader<String, usize> = Reader::asks(|s: String| s.len());
    /// assert_eq!(reader.run_reader("hello".to_string()), 5);
    /// ```
    #[inline]
    pub fn asks<S>(selector: S) -> Self
    where
        S: Fn(E) -> A + Clone + Send + Sync + 'static,
    {
        Reader {
            inner: ReaderT::new(move |e: E| Id::new(selector(e))),
        }
    }

    /// Creates a Reader with direct access to the environment.
    ///
    /// # Parameters
    ///
    /// * `f` - Function that processes the environment directly
    /// * `transform` - Function to transform the extracted value into the monad
    ///
    /// # Returns
    ///
    /// A Reader that processes the environment directly
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::reader::Reader;
    /// use rustica::datatypes::id::Id;
    ///
    /// let reader: Reader<i32, String> = Reader::ask_with(
    ///     |env: &i32| format!("Env is: {}", env),
    ///     |s: String| Id::new(s)
    /// );
    /// assert_eq!(reader.run_reader(42), "Env is: 42");
    /// ```
    #[inline]
    pub fn ask_with<F, G>(f: F, transform: G) -> Self
    where
        F: Fn(&E) -> A + Clone + Send + Sync + 'static,
        G: Fn(A) -> Id<A> + Clone + Send + Sync + 'static,
    {
        Reader {
            inner: ReaderT::new(move |e: E| transform(f(&e))),
        }
    }

    /// Modifies the environment before running this Reader, allowing environment transformation
    /// without changing the underlying computation. This is a key operation that distinguishes
    /// the Reader monad from other monads.
    ///
    /// # Performance Characteristics
    ///
    /// ## Time Complexity
    ///
    /// * **Construction**: O(1) - Only creates a new Reader with composed functions
    /// * **Execution**: O(f + g) - Where f is the complexity of the environment transformation function and
    ///   g is the complexity of the original Reader's function
    ///
    /// ## Memory Usage
    ///
    /// * Creates a new Reader with a closure that captures both the original Reader and the environment transformer
    /// * Memory efficiency through lazy evaluation - no transformation is performed until `run_reader` is called
    /// * No additional memory overhead beyond function composition
    ///
    /// # Use Cases
    ///
    /// * When you need to adapt an existing Reader to work with a different environment
    /// * For focusing on a part of a complex environment structure
    /// * To provide default values or add additional context to the environment
    /// * For testing different environment configurations with the same Reader
    ///
    /// # Parameters
    ///
    /// * `f` - Function that transforms the environment
    ///
    /// # Returns
    ///
    /// A new Reader that runs with the modified environment
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::reader::Reader;
    ///
    /// let reader: Reader<i32, i32> = Reader::new(|n: i32| n * 2);
    /// let local: Reader<i32, i32> = reader.local(|n: i32| n + 1);
    /// assert_eq!(local.run_reader(5), 12); // (5 + 1) * 2 = 12
    /// ```
    pub fn local<F>(&self, f: F) -> Self
    where
        F: Fn(E) -> E + Clone + Send + Sync + 'static,
    {
        let inner_clone = self.inner.clone();

        Reader {
            inner: ReaderT::new(move |e: E| inner_clone.run_reader(f(e))),
        }
    }

    /// Combines two Readers using a binary function, implementing Applicative functor functionality.
    /// This allows parallel composition of Readers that share the same environment type but
    /// may produce different result types.
    ///
    /// # Performance Characteristics
    ///
    /// ## Time Complexity
    ///
    /// * **Construction**: O(1) - Only creates a new Reader with composed functions
    /// * **Execution**: O(f + g + h) - Where:
    ///   - f is the complexity of the first Reader's function
    ///   - g is the complexity of the second Reader's function
    ///   - h is the complexity of the combining function
    ///
    /// ## Memory Usage
    ///
    /// * Creates a new Reader with a closure that captures both original Readers and the combining function
    /// * Both Readers are evaluated with the same environment instance, but independently
    /// * Memory efficiency through lazy evaluation - combining only happens when `run_reader` is called
    ///
    /// # Use Cases
    ///
    /// * When you need to combine results from multiple independent Readers
    /// * For parallel data extraction from the same environment
    /// * Building composite results from multiple environment queries
    /// * Implementing applicative-style programming patterns
    ///
    /// # Parameters
    ///
    /// * `other` - Another Reader to combine with this one
    /// * `f` - Function to combine the results of both Readers
    ///
    /// # Returns
    ///
    /// A new Reader with the combined result
    ///
    /// # Examples
    ///
    /// Basic combination:
    ///
    /// ```rust
    /// use rustica::datatypes::reader::Reader;
    ///
    /// let reader1: Reader<i32, i32> = Reader::new(|n: i32| n + 1);
    /// let reader2: Reader<i32, i32> = Reader::new(|n: i32| n * 2);
    /// let combined: Reader<i32, String> = reader1.combine(&reader2, |a: i32, b: i32| format!("{} and {}", a, b));
    /// assert_eq!(combined.run_reader(10), "11 and 20");
    /// ```
    pub fn combine<B, C, F>(&self, other: &Reader<E, B>, f: F) -> Reader<E, C>
    where
        F: Fn(A, B) -> C + Clone + Send + Sync + 'static,
        B: Clone + Send + Sync + 'static,
        C: Clone + Send + Sync + 'static,
        Id<B>: HKT<Source = B, Output<B> = Id<B>> + Monad,
        Id<C>: HKT<Source = C, Output<C> = Id<C>> + Monad,
    {
        let self_inner = self.inner.clone();
        let other_inner = other.inner.clone();

        Reader {
            inner: ReaderT::new(move |e: E| {
                let a = self_inner.run_reader(e.clone()).value().clone();
                let b = other_inner.run_reader(e).value().clone();
                Id::new(f(a, b))
            }),
        }
    }
}

/// Allows conversion from a `ReaderT<E, Id<A>, A>` to a `Reader<E, A>`.
///
/// This implementation enables seamless conversion from the transformer type to the base type.
/// Typically, this is only valid when the base monad is `Id`.
///
/// # Examples
///
/// ```rust
/// use rustica::datatypes::reader::Reader;
/// use rustica::transformers::reader_t::ReaderT;
/// use rustica::datatypes::id::Id;
///
/// // Create a ReaderT that doubles the environment value
/// let reader_t: ReaderT<i32, Id<i32>, i32> = ReaderT::new(|env: i32| Id::new(env * 2));
///
/// // Convert to Reader
/// let reader: Reader<i32, i32> = Reader::from(reader_t);
/// assert_eq!(reader.run_reader(21), 42);
/// ```
impl<E: Clone + Send + Sync + 'static, A: Clone + Send + Sync + 'static> From<ReaderT<E, Id<A>, A>>
    for Reader<E, A>
where
    Id<A>: HKT<Source = A, Output<A> = Id<A>> + Monad,
{
    fn from(reader_t: ReaderT<E, Id<A>, A>) -> Self {
        Reader { inner: reader_t }
    }
}

impl<E: Clone + 'static, A: Clone + 'static> Clone for Reader<E, A> {
    fn clone(&self) -> Self {
        Reader {
            inner: self.inner.clone(),
        }
    }
}

#[cfg(feature = "full")]
impl<E: Arbitrary + 'static + Send + Sync, A: Arbitrary + 'static + Send + Sync> Arbitrary
    for Reader<E, A>
{
    fn arbitrary(g: &mut Gen) -> Self {
        let value = A::arbitrary(g);
        Reader::new(move |_: E| value.clone())
    }
}
