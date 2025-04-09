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
//! ## Use Cases
//!
//! Reader is particularly useful in scenarios such as:
//!
//! - **Configuration Management**: When multiple functions need access to configuration settings
//! - **Dependency Injection**: For providing dependencies to functions without global state
//! - **Context-Aware Computations**: When operations need access to contextual information
//! - **Testing**: Makes it easy to substitute different environments for testing purposes
//!
//! ## Functional Patterns
//!
//! Reader implements several functional programming patterns:
//!
//! - **Functor**: Via the `fmap` method, allowing transformation of the result
//! - **Applicative**: Through the `combine` and `lift2` methods
//! - **Monad**: With the `bind` method for sequencing operations that depend on previous results
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

/// The Reader monad represents computations that depend on some environment value.
///
/// # Type Parameters
///
/// * `E` - The environment type
/// * `A` - The result type
///
/// # Examples
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
    pub fn run_reader(&self, env: E) -> A {
        let id_value = self.inner.run_reader(env);
        id_value.value().clone()
    }

    /// Maps a function over the value produced by this Reader.
    ///
    /// # Parameters
    ///
    /// * `f` - Function to apply to the value
    ///
    /// # Returns
    ///
    /// A new Reader with the function applied
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
    /// ```rust
    /// use rustica::datatypes::reader::Reader;
    /// use rustica::datatypes::id::Id;
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

    /// Creates a Reader that returns the environment itself.
    ///
    /// # Returns
    ///
    /// A Reader that returns the environment
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::reader::Reader;
    ///
    /// let reader: Reader<String, String> = Reader::ask();
    /// assert_eq!(reader.run_reader("hello".to_string()), "hello");
    /// ```
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
    pub fn ask_transform<F>(f: F) -> Self
    where
        F: Fn(E) -> A + Clone + Send + Sync + 'static,
    {
        Reader {
            inner: ReaderT::new(move |e: E| Id::new(f(e))),
        }
    }

    /// Creates a Reader that returns a value derived from the environment.
    ///
    /// # Parameters
    ///
    /// * `selector` - Function to extract a value from the environment
    ///
    /// # Returns
    ///
    /// A Reader that returns a value derived from the environment
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::reader::Reader;
    ///
    /// let reader: Reader<String, usize> = Reader::asks(|s: String| s.len());
    /// assert_eq!(reader.run_reader("hello".to_string()), 5);
    /// ```
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
    pub fn ask_with<F, G>(f: F, transform: G) -> Self
    where
        F: Fn(&E) -> A + Clone + Send + Sync + 'static,
        G: Fn(A) -> Id<A> + Clone + Send + Sync + 'static,
    {
        Reader {
            inner: ReaderT::new(move |e: E| transform(f(&e))),
        }
    }

    /// Modifies the environment before running this Reader.
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

    /// Combines two Readers using a binary function.
    ///
    /// # Parameters
    ///
    /// * `other` - Another Reader to combine with this one
    /// * `f` - Function to combine the results
    ///
    /// # Returns
    ///
    /// A new Reader with the combined result
    ///
    /// # Examples
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

    /// Converts this Reader into a ReaderT with any monad type.
    ///
    /// This method provides a way to lift a Reader into any monad transformer context
    /// by providing a function to lift the inner value into the target monad.
    ///
    /// # Type Parameters
    ///
    /// * `M` - The target monad
    /// * `F` - The type of the lifting function
    ///
    /// # Parameters
    ///
    /// * `lift_fn` - Function to lift a value of type A into the monad M
    ///
    /// # Returns
    ///
    /// A new `ReaderT` instance with the same environment type but with values in monad M
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::reader::Reader;
    /// use rustica::transformers::ReaderT;
    /// use rustica::prelude::*;
    ///
    /// // Create a simple Reader
    /// let reader: Reader<i32, i32> = Reader::new(|env: i32| env * 2);
    ///
    /// // Convert to a ReaderT with Option as the monad
    /// let reader_t: ReaderT<i32, Option<i32>, i32> = reader.clone().to_reader_t(|a: i32| Some(a));
    ///
    /// assert_eq!(reader_t.run_reader(21), Some(42));
    ///
    /// // Convert to a ReaderT with Result as the monad
    /// let result_reader_t: ReaderT<i32, Result<i32, String>, i32> =
    ///     reader.to_reader_t(|a: i32| Ok(a));
    ///
    /// assert_eq!(result_reader_t.run_reader(21), Ok(42));
    /// ```
    pub fn to_reader_t<M, F>(self, lift_fn: F) -> ReaderT<E, M, A>
    where
        M: Clone + Send + Sync + 'static,
        F: Fn(A) -> M + Clone + Send + Sync + 'static,
    {
        ReaderT::new(move |env: E| {
            let id_value = self.run_reader(env);
            lift_fn(id_value)
        })
    }
}

impl<E: Clone + 'static, A: Clone + 'static> Clone for Reader<E, A> {
    fn clone(&self) -> Self {
        Reader {
            inner: self.inner.clone(),
        }
    }
}
