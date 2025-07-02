//! # Reader Monad
//!
//! The Reader monad represents computations that depend on some environment or configuration.
//! It provides a way to thread an environment through a computation without explicitly passing
//! it as a parameter to every function.
//!
//! ## Core Concepts
//!
//! - **Environment Dependency**: Reader allows functions to access a shared environment without
//!   explicitly passing it around.
//! - **Pure Computation**: Reader maintains purity by making the environment dependency explicit
//!   in the type system.
//! - **Composition**: Multiple Reader computations can be combined while sharing the same environment.
//!
//! ## Performance Characteristics
//!
//! ### Time Complexity
//!
//! - **Construction** (`new`, `ask`, `asks`): O(1) - Only wraps a function
//! - **Execution** (`run_reader`): O(f) - Where f is the complexity of the wrapped function
//! - **Transformation** (`fmap`): O(1) for construction, O(f + g) when executed where:
//!   - f is the complexity of the original reader function
//!   - g is the complexity of the mapping function
//! - **Sequencing** (`bind`): O(1) for construction, O(f + g) when executed where:
//!   - f is the complexity of the original reader function
//!   - g is the complexity of the binding function
//! - **Environment Modification** (`local`): O(1) for construction, O(f + g) when executed where:
//!   - f is the complexity of the environment transformation
//!   - g is the complexity of the original reader function
//!
//! ### Memory Usage
//!
//! - **Reader**: Stores a single function pointer and any captured environment
//! - **Transformation** (`fmap`, `bind`): Each transformation adds a layer of function composition
//! - **Optimization**: Reader operations can be composed without immediate execution, allowing
//!   for memory-efficient computations that only allocate when finally executed
//!
//! ## Use Cases
//!
//! Reader is particularly useful in scenarios such as:
//!
//! - **Configuration Management**: When multiple functions need access to configuration settings
//! - **Dependency Injection**: For providing dependencies to functions without global state
//! - **Context-Aware Computations**: When operations need access to contextual information
//! - **Testing**: Makes it easy to substitute different environments for testing purposes
//!
//! ## Type Class Implementations
//!
//! Reader implements several functional programming type classes:
//!
//! - **Functor**: Via the `fmap` method, allowing transformation of the result
//! - **Applicative**: Through the `combine` and `lift2` methods
//! - **Monad**: With the `bind` method for sequencing operations that depend on previous results
//!
//! ## Type Class Laws
//!
//! ### Functor Laws
//!
//! ```rust
//! use rustica::datatypes::reader::Reader;
//! use rustica::traits::functor::Functor;
//!
//! // Identity: fmap id = id
//! let reader = Reader::new(|x: i32| x * 2);
//! let id = |x: &i32| *x;
//! let env = 10;
//! assert_eq!(reader.fmap(id).run_reader(env), reader.run_reader(env));
//!
//! // Composition: fmap (f . g) = fmap f . fmap g
//! let f = |x: &i32| x + 5;
//! let g = |x: &i32| x * 3;
//! let compose = |x: &i32| f(&g(x));
//! let reader = Reader::new(|x: i32| x + 1);
//! assert_eq!(reader.fmap(compose).run_reader(env), reader.fmap(g).fmap(f).run_reader(env));
//! ```
//!
//! ### Monad Laws
//!
//! ```rust
//! use rustica::datatypes::reader::Reader;
//! use rustica::traits::monad::Monad;
//!
//! // Left identity: return a >>= f = f a
//! let a = 42;
//! let f = |x: &i32| Reader::new(move |_: i32| *x + 10);
//! let return_a = Reader::new(move |_: i32| a);
//! let env = 10;
//! assert_eq!(return_a.bind(f).run_reader(env), f(&a).run_reader(env));
//!
//! // Right identity: m >>= return = m
//! let m = Reader::new(|x: i32| x * 2);
//! let return_fn = |x: &i32| Reader::new(move |_: i32| *x);
//! assert_eq!(m.bind(return_fn).run_reader(env), m.run_reader(env));
//!
//! // Associativity: (m >>= f) >>= g = m >>= (\x -> f x >>= g)
//! let m = Reader::new(|x: i32| x + 3);
//! let f = |x: &i32| Reader::new(move |_: i32| *x * 2);
//! let g = |x: &i32| Reader::new(move |_: i32| *x + 10);
//! let left = m.bind(f).bind(g).run_reader(env);
//! let right = m.bind(|x| f(x).bind(g)).run_reader(env);
//! assert_eq!(left, right);
//! ```
//!
//! ## Examples
//!
//! ### Basic Usage
//!
//! ```rust
//! use rustica::datatypes::reader::Reader;
//!
//! // Create a reader that depends on a numeric environment
//! let reader = Reader::new(|config: i32| config * 2);
//! assert_eq!(reader.run_reader(21), 42);
//! ```
//!
//! ### Composing Readers
//!
//! ```rust
//! use rustica::datatypes::reader::Reader;
//!
//! // Define a more complex environment
//! #[derive(Clone)]
//! struct AppConfig {
//!     base_url: String,
//!     timeout: u32,
//! }
//!
//! // Create readers that extract different parts of the config
//! let url_reader: Reader<AppConfig, String> = Reader::asks(|config: AppConfig| config.base_url.clone());
//! let timeout_reader: Reader<AppConfig, u32> = Reader::asks(|config: AppConfig| config.timeout);
//!
//! // Combine them to create a formatted output
//! let combined = url_reader.combine(&timeout_reader, |url, timeout| {
//!     format!("URL: {} with timeout: {}ms", url, timeout)
//! });
//!
//! // Run with a specific config
//! let config = AppConfig {
//!     base_url: "https://example.com".to_string(),
//!     timeout: 5000,
//! };
//!
//! assert_eq!(
//!     combined.run_reader(config),
//!     "URL: https://example.com with timeout: 5000ms"
//! );
//! ```
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
    /// Basic transformation:
    ///
    /// ```rust
    /// use rustica::datatypes::reader::Reader;
    /// use rustica::datatypes::id::Id;
    ///
    /// let reader: Reader<i32, i32> = Reader::new(|n: i32| n + 10);
    /// let mapped: Reader<i32, String> = reader.fmap(|n| n.to_string());
    /// assert_eq!(mapped.run_reader(5), "15");
    /// ```
    ///
    /// Chaining multiple transformations:
    ///
    /// ```rust
    /// use rustica::datatypes::reader::Reader;
    ///
    /// let reader = Reader::new(|n: i32| n + 5);
    ///
    /// // Apply multiple transformations in sequence
    /// let result = reader
    ///     .fmap(|n| n * 2)
    ///     .fmap(|n| n - 1)
    ///     .fmap(|n| format!("{} is the answer", n));
    ///     
    /// assert_eq!(result.run_reader(3), "15 is the answer"); // ((3 + 5) * 2) - 1 = 15
    /// ```
    ///
    /// Working with complex types:
    ///
    /// ```rust
    /// use rustica::datatypes::reader::Reader;
    /// use std::collections::HashMap;
    ///
    /// // Reader with HashMap result
    /// let reader = Reader::new(|prefix: &str| {
    ///     let mut map = HashMap::new();
    ///     map.insert("key1".to_string(), format!("{}-value1", prefix));
    ///     map.insert("key2".to_string(), format!("{}-value2", prefix));
    ///     map
    /// });
    ///
    /// // Transform to get only the values
    /// let values_reader = reader.fmap(|map| {
    ///     map.values().cloned().collect::<Vec<String>>()
    /// });
    ///
    /// let values = values_reader.run_reader("test");
    /// assert!(values.contains(&"test-value1".to_string()));
    /// assert!(values.contains(&"test-value2".to_string()));
    /// assert_eq!(values.len(), 2);
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
    /// # Examples
    ///
    /// Basic sequencing of operations:
    ///
    /// ```rust
    /// use rustica::datatypes::reader::Reader;
    /// use rustica::datatypes::id::Id;
    ///
    /// let reader: Reader<i32, i32> = Reader::new(|n: i32| n + 5);
    /// let bound: Reader<i32, i32> = reader.bind(|n| Reader::new(move |env: i32| env * n));
    /// assert_eq!(bound.run_reader(10), 150); // (10 + 5) * 10 = 150
    /// ```
    ///
    /// Chaining multiple binds:
    ///
    /// ```rust
    /// use rustica::datatypes::reader::Reader;
    ///
    /// // Create a series of readers where each depends on the previous result
    /// let start = Reader::new(|config: i32| config + 3);
    ///
    /// // Chain operations with bind
    /// let result = start
    ///     .bind(|n| Reader::new(move |_: i32| n * 2))
    ///     .bind(|n| Reader::new(move |config: i32| n + config))
    ///     .bind(|n| Reader::new(move |_: i32| n.to_string()));
    ///     
    /// assert_eq!(result.run_reader(10), "26"); // ((10 + 3) * 2) + 10 = 26
    /// ```
    ///
    /// Using bind with complex environment:
    ///
    /// ```rust
    /// use rustica::datatypes::reader::Reader;
    ///
    /// // Define configuration with multiple settings
    /// #[derive(Clone)]
    /// struct Config {
    ///     multiplier: i32,
    ///     offset: i32,
    /// }
    ///
    /// // First reader extracts the offset
    /// let get_offset = Reader::asks(|config: Config| config.offset);
    ///
    /// // Use bind to create a reader that uses both offset and multiplier
    /// let computed = get_offset.bind(|offset| {
    ///     Reader::new(move |config: Config| {
    ///         offset * config.multiplier
    ///     })
    /// });
    ///
    /// let config = Config { multiplier: 3, offset: 5 };
    /// assert_eq!(computed.run_reader(config), 15); // 5 * 3 = 15
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
    /// Basic usage:
    ///
    /// ```rust
    /// use rustica::datatypes::reader::Reader;
    ///
    /// let reader: Reader<String, String> = Reader::ask();
    /// assert_eq!(reader.run_reader("hello".to_string()), "hello");
    /// ```
    ///
    /// Using with environment type conversion:
    ///
    /// ```rust
    /// use rustica::datatypes::reader::Reader;
    ///
    /// // Custom type that can be created from a string
    /// #[derive(Debug, PartialEq)]
    /// struct Config {
    ///     value: String,
    /// }
    ///
    /// impl From<String> for Config {
    ///     fn from(s: String) -> Self {
    ///         Config { value: s }
    ///     }
    /// }
    ///
    /// // Reader that takes String environment and returns Config
    /// let reader: Reader<String, Config> = Reader::ask();
    /// let result = reader.run_reader("test".to_string());
    /// assert_eq!(result, Config { value: "test".to_string() });
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
    ///
    /// Extracting from a complex environment:
    ///
    /// ```rust
    /// use rustica::datatypes::reader::Reader;
    /// use std::collections::HashMap;
    ///
    /// // Define a complex application environment
    /// #[derive(Clone)]
    /// struct AppEnvironment {
    ///     config: HashMap<String, String>,
    ///     debug_mode: bool,
    ///     version: String,
    /// }
    ///
    /// // Create readers for different aspects of the environment
    /// let debug_reader = Reader::asks(|env: AppEnvironment| env.debug_mode);
    /// let version_reader = Reader::asks(|env: AppEnvironment| env.version.clone());
    /// let config_value_reader = |key: &str| Reader::asks(move |env: AppEnvironment| {
    ///     env.config.get(key).cloned().unwrap_or_default()
    /// });
    ///
    /// // Create the environment
    /// let mut config = HashMap::new();
    /// config.insert("api_url".to_string(), "https://api.example.com".to_string());
    /// config.insert("timeout".to_string(), "30000".to_string());
    ///
    /// let env = AppEnvironment {
    ///     config,
    ///     debug_mode: true,
    ///     version: "1.0.0".to_string(),
    /// };
    ///
    /// // Use the readers
    /// assert_eq!(debug_reader.run_reader(env.clone()), true);
    /// assert_eq!(version_reader.run_reader(env.clone()), "1.0.0");
    ///
    /// let api_url_reader = config_value_reader("api_url");
    /// assert_eq!(api_url_reader.run_reader(env.clone()), "https://api.example.com");
    /// ```
    ///
    /// Computing derived values:
    ///
    /// ```rust
    /// use rustica::datatypes::reader::Reader;
    ///
    /// struct Rectangle {
    ///     width: f64,
    ///     height: f64,
    /// }
    ///
    /// // Create readers that compute different properties
    /// let area_reader = Reader::asks(|rect: Rectangle| rect.width * rect.height);
    /// let perimeter_reader = Reader::asks(|rect: Rectangle| 2.0 * (rect.width + rect.height));
    /// let aspect_ratio_reader = Reader::asks(|rect: Rectangle| rect.width / rect.height);
    ///
    /// // Use with a specific rectangle
    /// let rect = Rectangle { width: 10.0, height: 5.0 };
    ///
    /// assert_eq!(area_reader.run_reader(rect.clone()), 50.0);
    /// assert_eq!(perimeter_reader.run_reader(rect.clone()), 30.0);
    /// assert_eq!(aspect_ratio_reader.run_reader(rect), 2.0);
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
    /// Basic environment modification:
    ///
    /// ```rust
    /// use rustica::datatypes::reader::Reader;
    ///
    /// let reader: Reader<i32, i32> = Reader::new(|n: i32| n * 2);
    /// let local: Reader<i32, i32> = reader.local(|n: i32| n + 1);
    /// assert_eq!(local.run_reader(5), 12); // (5 + 1) * 2 = 12
    /// ```
    ///
    /// Working with complex environments:
    ///
    /// ```rust
    /// use rustica::datatypes::reader::Reader;
    /// use std::collections::HashMap;
    ///
    /// // Define a complex configuration type
    /// #[derive(Clone)]
    /// struct AppConfig {
    ///     settings: HashMap<String, String>,
    ///     default_value: String,
    /// }
    ///
    /// // Reader that looks up a value from the config
    /// let lookup = |key: &str| Reader::new(move |config: AppConfig| {
    ///     config.settings.get(key)
    ///         .cloned()
    ///         .unwrap_or(config.default_value.clone())
    /// });
    ///
    /// // Create a base configuration
    /// let mut settings = HashMap::new();
    /// settings.insert("name".to_string(), "original".to_string());
    ///
    /// let config = AppConfig {
    ///     settings,
    ///     default_value: "default".to_string(),
    /// };
    ///
    /// // Get the "name" value
    /// let name_reader = lookup("name");
    /// assert_eq!(name_reader.run_reader(config.clone()), "original");
    ///
    /// // Modify the environment to provide a different setting
    /// let modified_reader = name_reader.local(|mut config: AppConfig| {
    ///     config.settings.insert("name".to_string(), "modified".to_string());
    ///     config
    /// });
    ///
    /// assert_eq!(modified_reader.run_reader(config.clone()), "modified");
    ///
    /// // Using local to provide a default for a missing key
    /// let key_reader = lookup("missing_key");
    /// assert_eq!(key_reader.run_reader(config.clone()), "default");
    ///
    /// // Modify the environment to change the default
    /// let with_custom_default = key_reader.local(|mut config: AppConfig| {
    ///     config.default_value = "custom default".to_string();
    ///     config
    /// });
    ///
    /// assert_eq!(with_custom_default.run_reader(config), "custom default");
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
    ///
    /// Working with a complex environment:
    ///
    /// ```rust
    /// use rustica::datatypes::reader::Reader;
    ///
    /// // Define a database configuration
    /// #[derive(Clone)]
    /// struct DbConfig {
    ///     host: String,
    ///     port: u16,
    ///     username: String,
    ///     password: String,
    /// }
    ///
    /// // Create readers that extract different parts of the config
    /// let host_reader = Reader::asks(|config: DbConfig| config.host.clone());
    /// let port_reader = Reader::asks(|config: DbConfig| config.port);
    /// let credentials_reader = Reader::asks(|config: DbConfig| {
    ///     format!("{}/{}", config.username, config.password)
    /// });
    ///
    /// // Build a connection string by combining readers
    /// let connection_string = host_reader.combine(&port_reader, |host, port| {
    ///     format!("{}:{}", host, port)
    /// }).combine(&credentials_reader, |server, credentials| {
    ///     format!("{}@{}", credentials, server)
    /// });
    ///
    /// // Run with a specific configuration
    /// let config = DbConfig {
    ///     host: "localhost".to_string(),
    ///     port: 5432,
    ///     username: "user".to_string(),
    ///     password: "pass".to_string(),
    /// };
    ///
    /// assert_eq!(connection_string.run_reader(config), "user/pass@localhost:5432");
    /// ```
    ///
    /// Combining multiple values with the same type:
    ///
    /// ```rust
    /// use rustica::datatypes::reader::Reader;
    ///
    /// // Define a settings object
    /// #[derive(Clone)]
    /// struct Settings {
    ///     min_value: i32,
    ///     max_value: i32,
    ///     default_value: i32,
    /// }
    ///
    /// // Create readers that extract different numeric properties
    /// let min_reader = Reader::asks(|s: Settings| s.min_value);
    /// let max_reader = Reader::asks(|s: Settings| s.max_value);
    /// let default_reader = Reader::asks(|s: Settings| s.default_value);
    ///
    /// // Combine all three readers to calculate a valid value
    /// let range_reader = min_reader.combine(&max_reader, |min, max| (min, max))
    ///     .combine(&default_reader, |(min, max), default| {
    ///         if default < min {
    ///             min
    ///         } else if default > max {
    ///             max
    ///         } else {
    ///             default
    ///         }
    ///     });
    ///     
    /// // Test with various settings
    /// let settings1 = Settings { min_value: 1, max_value: 10, default_value: 5 };
    /// let settings2 = Settings { min_value: 1, max_value: 10, default_value: 0 };
    /// let settings3 = Settings { min_value: 1, max_value: 10, default_value: 15 };
    ///
    /// assert_eq!(range_reader.run_reader(settings1), 5);  // Default is within range
    /// assert_eq!(range_reader.run_reader(settings2), 1);  // Default is below min
    /// assert_eq!(range_reader.run_reader(settings3), 10); // Default is above max
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
