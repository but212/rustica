//! # Reader Monad
//!
//! The Reader monad represents computations that depend on some environment or configuration.
//! It provides a way to thread an environment through a computation without explicitly passing
//! it as a parameter to every function.
//!
//! ## Quick Start
//!
//! Access shared configuration without explicit parameter passing:
//!
//! ```rust
//! use rustica::datatypes::reader::Reader;
//!
//! // Configuration type
//! #[derive(Clone)]
//! struct Config {
//!     database_url: String,
//!     timeout: u32,
//! }
//!
//! // Reader that accesses database URL from config
//! let db_reader = Reader::asks(|config: Config| config.database_url);
//!
//! // Reader that accesses timeout and doubles it
//! let timeout_reader = Reader::asks(|config: Config| config.timeout * 2);
//!
//! // Combine readers
//! let connection_reader = db_reader.combine(&timeout_reader, |url, timeout| {
//!     format!("{}?timeout={}", url, timeout)
//! });
//!
//! // Run with environment
//! let config = Config {
//!     database_url: "postgresql://localhost:5432/mydb".to_string(),
//!     timeout: 30,
//! };
//! let connection_string = connection_reader.run_reader(config);
//! assert_eq!(connection_string, "postgresql://localhost:5432/mydb?timeout=60");
//! ```
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
//! ## Functional Programming Context
//!
//! In functional programming, the Reader monad provides a way to pass a shared context
//! or configuration to a group of functions without explicitly threading it through
//! every function call. This creates cleaner, more composable code, particularly when
//! dealing with deeply nested function calls that all need access to some shared data.
//!
//! ## Functional Programming Methods
//!
//! The Reader monad provides inherent methods that follow functional programming patterns:
//!
//! - **Functor-like**: `fmap` transforms the result value of a Reader while preserving the environment.
//!   - Implementation: `fmap :: (A -> B) -> Reader<E, A> -> Reader<E, B>`
//!
//! - **Applicative-like**: Reader supports applicative operations through its `pure` and `apply` methods.
//!   - `pure`: Creates a Reader that ignores the environment and returns a constant value
//!     - Implementation: `pure :: A -> Reader<E, A>`
//!   
//!   - `apply`: Applies a function from one Reader to a value from another Reader
//!     - Implementation: `apply :: Reader<E, A -> B> -> Reader<E, A> -> Reader<E, B>`
//!
//! - **Monad-like**: `bind` allows chaining operations that depend on both the environment and previous results.
//!   - Implementation: `bind :: Reader<E, A> -> (A -> Reader<E, B>) -> Reader<E, B>`
//!
//! **Note**: These are inherent methods, not trait implementations. `Reader` does not implement
//! the `Functor`, `Applicative`, or `Monad` traits, but provides equivalent functionality
//! through its own methods optimized for environment-based computations.
//!
//! ## Functional Programming Laws
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
use quickcheck::{Arbitrary, Gen};

/// The Reader monad represents computations that depend on some environment value.
/// It enables functions to access a shared environment without passing it explicitly as a parameter.
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
        id_value.into_inner()
    }

    /// Maps a function over the value produced by this Reader.
    /// This allows transforming the output of a Reader without affecting its environment dependency.
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
                let a = id_a.into_inner();
                Id::new(f(a))
            }),
        }
    }

    /// Sequences two Reader computations, passing the result of the first to the second.
    /// This is the core method that enables chained operations where each operation can depend
    /// on the result of the previous one, following the monadic bind pattern.
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
                let a = id_a.into_inner();
                let reader_b = f(a);
                reader_b.inner.run_reader(e)
            }),
        }
    }

    /// Creates a Reader that returns the environment itself. This is a fundamental operation
    /// for the Reader monad, allowing direct access to the environment.
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
                let a = self_inner.run_reader(e.clone()).into_inner();
                let b = other_inner.run_reader(e).into_inner();
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

impl<E: Arbitrary + 'static + Send + Sync, A: Arbitrary + 'static + Send + Sync> Arbitrary
    for Reader<E, A>
{
    fn arbitrary(g: &mut Gen) -> Self {
        let value = A::arbitrary(g);
        Reader::new(move |_: E| value.clone())
    }
}
