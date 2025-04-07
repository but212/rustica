//! # Reader Transformer
//!
//! This module provides the `ReaderT` monad transformer, which adds the ability to read
//! from an environment to any base monad.
//!
//! The `ReaderT` transformer represents computations that can read from a shared environment
//! while also supporting the effects of the base monad.
//!
//! ## Basic Usage
//!
//! ```rust
//! use rustica::transformers::ReaderT;
//! use rustica::prelude::*;
//!
//! // Create a ReaderT over Vec for a configuration environment
//! let reader_t: ReaderT<i32, Vec<i32>, i32> = ReaderT::new(|config: i32| vec![config, config * 2, config * 3]);
//!
//! // Run with a specific environment value
//! let result = reader_t.run_reader(10);
//! assert_eq!(result, vec![10, 20, 30]);
//! ```
//!
//! ## Environment Access and Composition
//!
//! ```rust
//! use rustica::transformers::ReaderT;
//! use rustica::prelude::*;
//!
//! // Configuration struct
//! #[derive(Clone)]
//! struct Config {
//!     base_url: String,
//!     timeout: u32,
//! }
//!
//! // Create a ReaderT that extracts the base_url
//! let get_url: ReaderT<Config, Option<String>, String> = ReaderT::new(|config: Config| Some(config.base_url));
//!
//! // Create a ReaderT that extracts the timeout
//! let get_timeout: ReaderT<Config, Option<u32>, u32> = ReaderT::new(|config: Config| Some(config.timeout));
//!
//! // Combine both readers to create a formatted URL with timeout parameters
//! let formatted_url: ReaderT<Config, Option<String>, String> = ReaderT::new(move |config: Config| {
//!     let base = get_url.run_reader(config.clone())?;
//!     let timeout = get_timeout.run_reader(config)?;
//!     Some(format!("{}?timeout={}", base, timeout))
//! });
//!
//! // Run with a specific config
//! let config = Config {
//!     base_url: "https://api.example.com".to_string(),
//!     timeout: 30,
//! };
//!
//! let result = formatted_url.run_reader(config);
//! assert_eq!(result, Some("https://api.example.com?timeout=30".to_string()));
//! ```
//!
//! ## Transforming Environments with `local`
//!
//! ```rust
//! use rustica::transformers::ReaderT;
//! use rustica::prelude::*;
//!
//! // Create a ReaderT that reads an integer environment
//! let reader: ReaderT<i32, Vec<i32>, i32> = ReaderT::new(|n: i32| vec![n, n*n]);
//!
//! // Create a new ReaderT that modifies the environment before running
//! let modified = reader.local(|n: i32| n * 2);
//!
//! // The original reader runs with an integer
//! let result1 = reader.run_reader(5);
//! assert_eq!(result1, vec![5, 25]);
//!
//! // The modified reader runs with an integer, which is doubled before being passed to the original reader
//! let result2 = modified.run_reader(5);
//! assert_eq!(result2, vec![10, 100]); // 5 is doubled to 10, then squared to 100
//! ```
//!
//! ## Advanced Composition
//!
//! ```rust
//! use rustica::transformers::ReaderT;
//! use rustica::prelude::*;
//!
//! // Application context
//! #[derive(Clone)]
//! struct AppContext {
//!     debug_mode: bool,
//!     multiplier: i32,
//! }
//!
//! // Create readers that perform different operations
//!
//! // This reader retrieves the multiplier from context
//! let get_multiplier: ReaderT<AppContext, Result<i32, String>, i32> = ReaderT::new(|ctx: AppContext| -> Result<i32, String> {
//!     Ok(ctx.multiplier)
//! });
//!
//! // This reader performs a calculation with the multiplier
//! let calculate: ReaderT<AppContext, Result<i32, String>, i32> = ReaderT::new(move |ctx: AppContext| -> Result<i32, String> {
//!     let multiplier = get_multiplier.run_reader(ctx.clone())?;
//!     if multiplier <= 0 {
//!         return Err("Multiplier must be positive".to_string());
//!     }
//!     Ok(42 * multiplier)
//! });
//!
//! // This reader logs the result if in debug mode
//! let log_result = move |value: i32| {
//!     ReaderT::new(move |ctx: AppContext| -> Result<i32, String> {
//!         if ctx.debug_mode {
//!             // In a real app, this would log to a file or console
//!             println!("DEBUG: Calculated value is {}", value);
//!         }
//!         Ok(value)
//!     }) as ReaderT<AppContext, Result<i32, String>, i32>
//! };
//!
//! // Compose operations using bind_with
//! let program = calculate.bind_with(
//!     log_result,
//!     |m: Result<i32, String>, f| m.and_then(|v| f(v))
//! );
//!
//! // Run with different contexts
//! let context1 = AppContext { debug_mode: true, multiplier: 2 };
//! let result1 = program.run_reader(context1);
//! assert_eq!(result1, Ok(84)); // 42 * 2 = 84
//!
//! let context2 = AppContext { debug_mode: false, multiplier: 0 };
//! let result2 = program.run_reader(context2);
//! assert_eq!(result2, Err("Multiplier must be positive".to_string()));
//! ```
//!
//! ## Creating a ReaderT by Applying a Function to the Environment
//!
//! ```rust
//! use rustica::transformers::ReaderT;
//! use rustica::prelude::*;
//!
//! // Define a configuration type
//! #[derive(Clone)]
//! struct Config {
//!     max_connections: usize,
//!     timeout_seconds: u32,
//! }
//!
//! // Create a reader that extracts just the max_connections field
//! let get_max_conn = ReaderT::<Config, Result<usize, String>, usize>::asks(
//!     |config: Config| config.max_connections,
//!     |value: usize| Ok(value)
//! );
//!
//! // Test with a config
//! let config = Config {
//!     max_connections: 100,
//!     timeout_seconds: 30,
//! };
//!
//! assert_eq!(get_max_conn.run_reader(config), Ok(100));
//! ```

use super::MonadTransformer;
use crate::traits::monad::Monad;
use crate::utils::error_utils::AppError;
use std::marker::PhantomData;
use std::sync::Arc;

/// The `ReaderT` monad transformer adds environment reading capabilities to any base monad.
///
/// `ReaderT<E, M, A>` represents a computation that can read from an environment of type `E`,
/// and produces a value of type `A` within the context of monad `M`.
///
/// # Type Parameters
///
/// * `E` - The environment type
/// * `M` - The base monad type constructor
/// * `A` - The result type
///
/// # Examples
///
/// ```rust
/// use rustica::transformers::ReaderT;
/// use rustica::prelude::*;
///
/// // Create a reader transformer over Vec
/// let reader_t: ReaderT<String, Vec<usize>, usize> = ReaderT::new(|config: String| {
///     vec![config.len(), config.chars().count()]
/// });
///
/// // Run with a specific environment
/// let result = reader_t.run_reader("hello".to_string());
/// assert_eq!(result, vec![5, 5]);
/// ```
pub struct ReaderT<E, M, A> {
    /// Internal function that runs with an environment to produce a monadic value
    run_reader_fn: Arc<dyn Fn(E) -> M + Send + Sync>,
    /// Phantom data to track the value type
    _phantom: PhantomData<A>,
}

impl<E, M, A> Clone for ReaderT<E, M, A>
where
    E: 'static,
    M: 'static,
{
    fn clone(&self) -> Self {
        ReaderT {
            run_reader_fn: self.run_reader_fn.clone(),
            _phantom: PhantomData,
        }
    }
}

impl<E, M, A> ReaderT<E, M, A>
where
    E: 'static,
    M: 'static,
{
    /// Creates a new `ReaderT` transformer.
    ///
    /// # Parameters
    ///
    /// * `f` - A function that takes an environment and returns a monadic value
    ///
    /// # Returns
    ///
    /// A new `ReaderT` instance
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::transformers::ReaderT;
    /// use rustica::prelude::*;
    ///
    /// // Create a ReaderT that reads a configuration and returns an Optional value
    /// let reader: ReaderT<String, Option<usize>, usize> = ReaderT::new(|config: String| {
    ///     if config.is_empty() {
    ///         None
    ///     } else {
    ///         Some(config.len())
    ///     }
    /// });
    ///
    /// assert_eq!(reader.run_reader("hello".to_string()), Some(5));
    /// assert_eq!(reader.run_reader("".to_string()), None);
    /// ```
    #[inline]
    pub fn new<F>(f: F) -> Self
    where
        F: Fn(E) -> M + 'static + Send + Sync,
    {
        ReaderT {
            run_reader_fn: Arc::new(f),
            _phantom: PhantomData,
        }
    }

    /// Runs the reader transformer with a specific environment.
    ///
    /// # Parameters
    ///
    /// * `env` - The environment to run with
    ///
    /// # Returns
    ///
    /// The resulting monadic value
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::transformers::ReaderT;
    /// use rustica::prelude::*;
    /// use std::collections::HashMap;
    ///
    /// // Create a reader that looks up a value in a HashMap
    /// let reader: ReaderT<HashMap<&str, i32>, Option<i32>, i32> =
    ///     ReaderT::new(|env: HashMap<&str, i32>| env.get("key").copied());
    ///     
    /// // Create two different environments
    /// let mut env1 = HashMap::new();
    /// env1.insert("key", 42);
    ///
    /// let mut env2 = HashMap::new();
    /// env2.insert("other_key", 100);
    ///
    /// // Run with different environments
    /// assert_eq!(reader.run_reader(env1), Some(42));
    /// assert_eq!(reader.run_reader(env2), None);
    /// ```
    #[inline]
    pub fn run_reader(&self, env: E) -> M
    where
        E: Clone,
    {
        (self.run_reader_fn)(env)
    }

    /// Creates a `ReaderT` that returns the environment itself, wrapped in the base monad.
    ///
    /// # Type Parameters
    ///
    /// * `M` - The base monad type constructor
    ///
    /// # Returns
    ///
    /// A `ReaderT` that returns the environment
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::transformers::ReaderT;
    /// use rustica::prelude::*;
    ///
    /// // Define a configuration type
    /// #[derive(Clone)]
    /// struct Config {
    ///     max_connections: usize,
    ///     timeout_seconds: u32,
    /// }
    ///
    /// // Create a reader that extracts just the max_connections field
    /// let get_max_conn = ReaderT::<Config, Result<usize, String>, usize>::asks(
    ///     |config: Config| config.max_connections,
    ///     |value: usize| Ok(value)
    /// );
    ///
    /// // Test with a config
    /// let config = Config {
    ///     max_connections: 100,
    ///     timeout_seconds: 30,
    /// };
    ///
    /// assert_eq!(get_max_conn.run_reader(config), Ok(100));
    /// ```
    #[inline]
    pub fn ask<P>(pure: P) -> ReaderT<E, M, E>
    where
        P: Fn(E) -> M + Send + Sync + 'static,
    {
        ReaderT::new(pure)
    }

    /// Modifies the environment before running a reader transformer.
    ///
    /// # Parameters
    ///
    /// * `f` - Function to modify the environment
    ///
    /// # Returns
    ///
    /// A `ReaderT` that runs with a modified environment
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::transformers::ReaderT;
    /// use rustica::prelude::*;
    ///
    /// // A ReaderT that divides 100 by the environment value
    /// let div_reader: ReaderT<i32, Result<i32, String>, i32> =
    ///     ReaderT::new(|n: i32| {
    ///         if n == 0 {
    ///             Err("Division by zero".to_string())
    ///         } else {
    ///             Ok(100 / n)
    ///         }
    ///     });
    ///
    /// // Create a new reader that works with string length instead of direct integers
    /// let string_reader = div_reader.local(|n: i32| n * 2);
    ///
    /// // Original reader works with integers
    /// assert_eq!(div_reader.run_reader(5), Ok(20));  // 100 / 5 = 20
    /// assert_eq!(div_reader.run_reader(0), Err("Division by zero".to_string()));
    ///
    /// // Modified reader works with doubled integers
    /// assert_eq!(string_reader.run_reader(5), Ok(10));  // 100 / (5 * 2) = 10
    /// assert_eq!(string_reader.run_reader(0), Err("Division by zero".to_string()));
    /// ```
    #[inline]
    pub fn local<F>(&self, f: F) -> Self
    where
        F: Fn(E) -> E + Send + Sync + 'static,
    {
        let inner_fn = self.run_reader_fn.clone();
        ReaderT::new(move |e| inner_fn(f(e)))
    }

    /// Creates a `ReaderT` by applying a function to the environment.
    ///
    /// # Parameters
    ///
    /// * `f` - Function to apply to the environment
    /// * `pure` - Function to lift a value into the base monad
    ///
    /// # Returns
    ///
    /// A `ReaderT` that applies a function to the environment
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::transformers::ReaderT;
    /// use rustica::prelude::*;
    ///
    /// // Define a configuration type
    /// #[derive(Clone)]
    /// struct Config {
    ///     max_connections: usize,
    ///     timeout_seconds: u32,
    /// }
    ///
    /// // Create a reader that extracts just the max_connections field
    /// let get_max_conn = ReaderT::<Config, Result<usize, String>, usize>::asks(
    ///     |config: Config| config.max_connections,
    ///     |value: usize| Ok(value)
    /// );
    ///
    /// // Test with a config
    /// let config = Config {
    ///     max_connections: 100,
    ///     timeout_seconds: 30,
    /// };
    ///
    /// assert_eq!(get_max_conn.run_reader(config), Ok(100));
    /// ```
    #[inline]
    pub fn asks<B, F, P>(f: F, pure: P) -> ReaderT<E, M, B>
    where
        F: Fn(E) -> B + Send + Sync + 'static,
        P: Fn(B) -> M + Send + Sync + 'static,
    {
        ReaderT::new(move |e| pure(f(e)))
    }
}

impl<E, M, A> ReaderT<E, M, A>
where
    E: Clone + Send + Sync + 'static,
    M: Monad<Source = A> + Clone + 'static,
    A: Clone + 'static,
{
    /// Maps a function over the values inside this ReaderT.
    ///
    /// This is a specialized implementation that works with monads that have a map function.
    ///
    /// # Parameters
    ///
    /// * `f` - Function to apply to the values
    /// * `map_fn` - Function that knows how to map over the base monad
    ///
    /// # Returns
    ///
    /// A new ReaderT with the function applied to its values
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::transformers::ReaderT;
    /// use rustica::prelude::*;
    ///
    /// // Create a reader transformer over Option
    /// let reader_t: ReaderT<String, Option<usize>, usize> = ReaderT::new(|config: String| {
    ///     Some(config.len())
    /// });
    ///
    /// // Map over the value using fmap_with
    /// let doubled_reader = reader_t.fmap_with(
    ///     |n: usize| n * 2,
    ///     |m: Option<usize>, f| m.fmap_owned(f)
    /// );
    ///
    /// assert_eq!(doubled_reader.run_reader("hello".to_string()), Some(10));
    /// ```
    #[inline]
    pub fn fmap_with<B, F, MapFn>(&self, f: F, map_fn: MapFn) -> ReaderT<E, M, B>
    where
        F: Fn(A) -> B + Clone + Send + Sync + 'static,
        MapFn: Fn(M, F) -> M + Send + Sync + 'static,
        A: 'static,
        B: 'static,
        M: 'static,
    {
        let inner_fn = self.run_reader_fn.clone();
        let f_clone = f.clone();

        ReaderT::new(move |e| {
            let m = inner_fn(e);
            map_fn(m, f_clone.clone())
        })
    }

    /// Binds this ReaderT with a function that produces another ReaderT.
    ///
    /// This is the monadic bind operation, which allows sequencing operations that depend
    /// on the result of previous operations.
    ///
    /// # Parameters
    ///
    /// * `f` - Function that takes a value and returns a new ReaderT
    /// * `bind_fn` - Function that knows how to perform bind on the base monad
    ///
    /// # Returns
    ///
    /// A new ReaderT representing the sequenced computation
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::transformers::ReaderT;
    /// use rustica::prelude::*;
    ///
    /// // Create a reader that returns the input environment
    /// let div_reader: ReaderT<i32, Option<i32>, i32> =
    ///     ReaderT::new(|env: i32| Some(env));
    ///
    /// // Create a function that takes the output and produces another reader
    /// let validate = |n: i32| {
    ///     ReaderT::new(move |_: i32| {
    ///         if n == 0 {
    ///             None  // Division by zero
    ///         } else {
    ///             Some(100 / n)
    ///         }
    ///     }) as ReaderT<i32, Option<i32>, i32>
    /// };
    ///
    /// // Compose using bind_with
    /// let safe_div: ReaderT<i32, Option<i32>, i32> = div_reader.bind_with(
    ///     validate,
    ///     |m: Option<i32>, f| m.and_then(|v| f(v))
    /// );
    ///
    /// assert_eq!(safe_div.run_reader(5), Some(20));  // 100 / 5 = 20
    /// assert_eq!(safe_div.run_reader(0), None);  // Division by zero
    /// ```
    #[inline]
    pub fn bind_with<B, N, F, BindFn>(&self, f: F, bind_fn: BindFn) -> ReaderT<E, N, B>
    where
        F: Fn(A) -> ReaderT<E, N, B> + Clone + Send + Sync + 'static,
        BindFn: Fn(M, Arc<dyn Fn(A) -> N + Send + Sync>) -> N + Send + Sync + 'static,
        A: Clone + 'static,
        B: 'static,
        M: 'static,
        N: 'static,
    {
        let inner_fn = self.run_reader_fn.clone();
        let f_clone = f.clone();

        ReaderT::new(move |e: E| {
            let m = inner_fn(e.clone());
            let e_for_closure = e.clone();
            let f_for_closure = f_clone.clone();

            let bind_closure = Arc::new(move |a: A| {
                let reader_b = f_for_closure(a);
                reader_b.run_reader(e_for_closure.clone())
            });

            bind_fn(m, bind_closure)
        })
    }

    /// Applies a function from another ReaderT to the values in this ReaderT.
    ///
    /// This implements the applicative functor pattern.
    ///
    /// # Parameters
    ///
    /// * `f` - ReaderT containing functions to apply
    /// * `ap_fn` - Function that knows how to perform function application in the base monad
    ///
    /// # Returns
    ///
    /// A new ReaderT with the functions applied
    #[inline]
    pub fn apply_with<B, F, ApFn>(&self, f: &ReaderT<E, M, F>, ap_fn: ApFn) -> ReaderT<E, M, B>
    where
        F: Fn(&A) -> B + Clone + Send + Sync + 'static,
        ApFn: Fn(M, M) -> M + Clone + Send + Sync + 'static,
        A: Clone + 'static,
        B: 'static,
        M: 'static,
    {
        let self_fn = self.run_reader_fn.clone();
        let f_fn = f.run_reader_fn.clone();
        let ap_fn_clone = ap_fn.clone();

        ReaderT::new(move |e: E| {
            let ma = self_fn(e.clone());
            let mf = f_fn(e.clone());
            ap_fn_clone(ma, mf)
        })
    }

    /// Combines this ReaderT with another using a binary function.
    ///
    /// This is useful for combining the results of two reader operations that depend
    /// on the same environment.
    ///
    /// # Parameters
    ///
    /// * `other` - Another ReaderT to combine with
    /// * `f` - Function to combine the results
    /// * `combine_fn` - Function that knows how to combine values in the base monad
    ///
    /// # Returns
    ///
    /// A new ReaderT with the combined results
    #[inline]
    pub fn combine_with<B, C, F, CombineFn>(
        &self,
        other: &ReaderT<E, M, B>,
        f: F,
        combine_fn: CombineFn,
    ) -> ReaderT<E, M, C>
    where
        F: Fn(&A, &B) -> C + Clone + Send + Sync + 'static,
        CombineFn: Fn(M, M, F) -> M + Clone + Send + Sync + 'static,
        A: Clone + 'static,
        B: Clone + 'static,
        C: 'static,
        M: 'static,
    {
        let self_fn = self.run_reader_fn.clone();
        let other_fn = other.run_reader_fn.clone();
        let f_clone = f.clone();
        let combine_fn_clone = combine_fn.clone();

        ReaderT::new(move |e: E| {
            let ma = self_fn(e.clone());
            let mb = other_fn(e.clone());
            combine_fn_clone(ma, mb, f_clone.clone())
        })
    }

    /// Unwraps this ReaderT to get the base monad value by providing an environment.
    ///
    /// This method allows for safely unwrapping a ReaderT by providing the
    /// environment needed to run the computation.
    ///
    /// # Parameters
    ///
    /// * `env` - The environment to use for unwrapping
    ///
    /// # Returns
    ///
    /// The base monad value
    #[inline]
    pub fn unwrap_with(self, env: E) -> M {
        self.run_reader(env)
    }
}

impl<E, Err, A> ReaderT<E, Result<A, Err>, A>
where
    E: Clone + 'static,
    Err: 'static,
    A: Clone + 'static,
{
    /// Runs the reader transformer and converts errors to AppError for standardized error handling.
    ///
    /// This method executes the reader transformer with the given environment and converts
    /// any errors to the standardized AppError type, providing consistent error handling
    /// across the library.
    ///
    /// # Parameters
    ///
    /// * `env` - Environment to run the reader with
    ///
    /// # Returns
    ///
    /// Result containing either the value or an AppError
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::transformers::ReaderT;
    /// use rustica::utils::error_utils::AppError;
    ///
    /// // Create a ReaderT that may fail with division
    /// let safe_div: ReaderT<i32, Result<i32, String>, i32> = ReaderT::new(|n: i32| {
    ///     if n == 0 {
    ///         Err("Division by zero".to_string())
    ///     } else {
    ///         Ok(100 / n)
    ///     }
    /// });
    ///
    /// // Convert regular errors to AppError
    /// let result = safe_div.try_run_reader(4);
    /// assert!(result.is_ok());
    /// assert_eq!(result.unwrap(), 25); // 100/4 = 25
    ///
    /// // With error
    /// let result = safe_div.try_run_reader(0);
    /// assert!(result.is_err());
    /// assert_eq!(result.unwrap_err().message(), &"Division by zero");
    /// ```
    pub fn try_run_reader(&self, env: E) -> Result<A, AppError<Err>> {
        self.run_reader(env).map_err(AppError::new)
    }

    /// Runs the reader transformer with context information for better error reporting.
    ///
    /// This method is similar to `try_run_reader` but allows for adding context to the error,
    /// which can provide more information about what was happening when the error occurred.
    ///
    /// # Parameters
    ///
    /// * `env` - Environment to run the reader with
    /// * `context` - Context information to include with errors
    ///
    /// # Returns
    ///
    /// Result containing either the value or an AppError with context
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::transformers::ReaderT;
    /// use rustica::utils::error_utils::AppError;
    ///
    /// // Create a ReaderT that may fail with division
    /// let safe_div: ReaderT<i32, Result<i32, String>, i32> = ReaderT::new(|n: i32| {
    ///     if n == 0 {
    ///         Err("Division by zero".to_string())
    ///     } else {
    ///         Ok(100 / n)
    ///     }
    /// });
    ///
    /// // Run with context
    /// let result = safe_div.try_run_reader_with_context(4, "processing user input");
    /// assert!(result.is_ok());
    /// assert_eq!(result.unwrap(), 25); // 100/4 = 25
    ///
    /// // With error and context
    /// let result = safe_div.try_run_reader_with_context(0, "processing user input");
    /// assert!(result.is_err());
    /// let error = result.unwrap_err();
    /// assert_eq!(error.message(), &"Division by zero");
    /// assert_eq!(error.context(), Some(&"processing user input"));
    /// ```
    pub fn try_run_reader_with_context<C>(&self, env: E, context: C) -> Result<A, AppError<Err, C>>
    where
        C: Clone + 'static,
    {
        self.run_reader(env).map_err(|e| AppError::with_context(e, context))
    }

    /// Maps a function over the error contained in this ReaderT.
    ///
    /// This method transforms the error type of the ReaderT, allowing for conversion
    /// between different error types while preserving the structure of the ReaderT.
    ///
    /// # Parameters
    ///
    /// * `f` - Function to apply to the error
    ///
    /// # Returns
    ///
    /// A new ReaderT with the mapped error
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::transformers::ReaderT;
    ///
    /// // Create a ReaderT with a string error
    /// let reader_t: ReaderT<i32, Result<i32, String>, i32> = ReaderT::new(|n: i32| {
    ///     if n == 0 {
    ///         Err("Division by zero".to_string())
    ///     } else {
    ///         Ok(100 / n)
    ///     }
    /// });
    ///
    /// // Map the error to a different type
    /// let mapped = reader_t.map_error(|e: String| e.len() as i32);
    ///
    /// // Now the error is an i32 (the length of the original error string)
    /// let result = mapped.run_reader(0);
    /// assert_eq!(result, Err(16)); // "Division by zero" has length 16
    /// ```
    pub fn map_error<F, Err2>(&self, f: F) -> ReaderT<E, Result<A, Err2>, A>
    where
        F: Fn(Err) -> Err2 + Send + Sync + 'static,
        Err2: 'static,
    {
        // Clone the function before capturing it in the closure
        let run_reader_fn_clone = self.run_reader_fn.clone();
        ReaderT::new(move |e: E| {
            run_reader_fn_clone(e).map_err(|err| f(err))
        })
    }
}

impl<E, M, A> MonadTransformer for ReaderT<E, M, A>
where
    E: Clone + 'static,
    M: Monad<Source = A> + Send + Sync + Clone + 'static,
    A: Clone + 'static,
{
    type BaseMonad = M;

    #[inline]
    fn lift(base: Self::BaseMonad) -> Self {
        let base_clone = base.clone();
        ReaderT::new(move |_| base_clone.clone())
    }
}
