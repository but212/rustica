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
//!
//! // Run the reader with a specific environment
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
//! let url_reader = Reader::<AppConfig, String>::asks(|config| config.base_url.clone());
//! let timeout_reader = Reader::<AppConfig, u32>::asks(|config| config.timeout);
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

use std::sync::Arc;

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
/// let reader = Reader::new(|e: i32| e * 2);
/// assert_eq!(reader.run_reader(21), 42);
///
/// // Transform the result using fmap
/// let string_reader = reader.fmap(|x| x.to_string());
/// assert_eq!(string_reader.run_reader(21), "42");
/// ```
#[derive(Clone)]
pub struct Reader<E, A> {
    run: Arc<dyn Fn(E) -> A>,
}

impl<E: Clone + 'static, A: Clone + 'static> Reader<E, A> {
    /// Creates a new Reader from a function.
    ///
    /// # Arguments
    ///
    /// * `f` - Function that takes an environment and returns a value
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::reader::Reader;
    ///
    /// let reader = Reader::new(|env: i32| env + 1);
    /// assert_eq!(reader.run_reader(41), 42);
    /// ```
    pub fn new<F>(f: F) -> Self
    where
        F: Fn(E) -> A + 'static,
    {
        Reader { run: Arc::new(f) }
    }

    /// Runs the reader with a given environment.
    ///
    /// # Arguments
    ///
    /// * `e` - The environment to run with
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::reader::Reader;
    ///
    /// let reader = Reader::new(|env: i32| env * 2);
    /// assert_eq!(reader.run_reader(21), 42);
    /// ```
    pub fn run_reader(&self, e: E) -> A {
        (self.run)(e)
    }

    /// Creates a reader that returns the environment itself.
    ///
    /// This is a fundamental operation in the Reader monad, providing direct access
    /// to the environment. It corresponds to the `ask` operation in other functional
    /// programming languages.
    ///
    /// # Reader Monad Context
    ///
    /// The `ask` operation is often used as a building block for more complex reader
    /// operations, allowing access to the environment within a computation chain.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::reader::Reader;
    ///
    /// // Create a reader that simply returns the environment
    /// let reader = Reader::<i32, i32>::ask();
    /// assert_eq!(reader.run_reader(42), 42);
    ///
    /// // Use ask as part of a more complex computation
    /// let complex = Reader::<i32, i32>::ask().bind(|env| {
    ///     Reader::new(move |_| env * 2)
    /// });
    /// assert_eq!(complex.run_reader(21), 42);
    /// ```
    pub fn ask() -> Reader<E, E> {
        Reader::new(|e| e)
    }

    /// Creates a reader by applying a function to the environment.
    ///
    /// This is a convenience method that creates a reader which transforms the
    /// environment using the provided function. It's similar to `ask` followed by `fmap`,
    /// but more concise.
    ///
    /// # Reader Monad Context
    ///
    /// The `asks` operation is commonly used to extract or transform specific parts
    /// of the environment without needing to explicitly chain operations.
    ///
    /// # Arguments
    ///
    /// * `f` - Function to apply to the environment
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::reader::Reader;
    ///
    /// // Extract a specific part of the environment
    /// let reader = Reader::<(i32, String), String>::asks(|(_, s)| s.clone());
    /// assert_eq!(reader.run_reader((42, "hello".to_string())), "hello");
    ///
    /// // Transform the environment
    /// let reader = Reader::<i32, String>::asks(|env: i32| env.to_string());
    /// assert_eq!(reader.run_reader(42), "42");
    ///
    /// // Equivalent to ask().fmap(f)
    /// let reader1 = Reader::<i32, String>::asks(|env| env.to_string());
    /// let reader2 = Reader::<i32, i32>::ask().fmap(|env| env.to_string());
    /// assert_eq!(reader1.run_reader(42), reader2.run_reader(42));
    /// ```
    pub fn asks<B: Clone + 'static>(f: impl Fn(E) -> B + 'static) -> Reader<E, B> {
        Reader::new(f)
    }

    /// Maps a function over the reader's result.
    ///
    /// This implements the Functor pattern for Reader, allowing transformation of the
    /// result value while preserving the Reader structure and environment access.
    ///
    /// # Functor Properties
    ///
    /// The fmap operation satisfies the functor laws:
    /// - Identity: `reader.fmap(|x| x) ≡ reader`
    /// - Composition: `reader.fmap(|x| g(f(x))) ≡ reader.fmap(f).fmap(g)`
    ///
    /// # Arguments
    ///
    /// * `f` - Function to apply to the result
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::reader::Reader;
    ///
    /// // Create a reader that accesses the environment
    /// let reader = Reader::new(|env: i32| env + 1);
    ///
    /// // Transform the result to a string
    /// let string_reader = reader.fmap(|x| x.to_string());
    /// assert_eq!(string_reader.run_reader(41), "42");
    ///
    /// // Chain multiple transformations
    /// let complex_reader = reader
    ///     .fmap(|x| x * 2)
    ///     .fmap(|x| format!("The answer is {}", x));
    /// assert_eq!(complex_reader.run_reader(20), "The answer is 42");
    /// ```
    pub fn fmap<B: Clone + 'static>(&self, f: impl Fn(A) -> B + 'static) -> Reader<E, B> {
        let run = self.run.clone();
        Reader::new(move |e| f((run)(e)))
    }

    /// Chains two readers together.
    ///
    /// This is the monadic bind operation for the Reader monad. It allows sequencing
    /// operations where the next operation depends on the result of the previous one,
    /// while maintaining access to the shared environment.
    ///
    /// # Monadic Properties
    ///
    /// The bind operation satisfies the monad laws:
    /// - Left identity: `Reader::new(|_| a).bind(f) ≡ f(a)`
    /// - Right identity: `reader.bind(|a| Reader::new(|_| a)) ≡ reader`
    /// - Associativity: `reader.bind(f).bind(g) ≡ reader.bind(|a| f(a).bind(g))`
    ///
    /// # Arguments
    ///
    /// * `f` - Function that takes the result of this reader and returns a new reader
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::reader::Reader;
    ///
    /// // A reader that adds 1 to the environment
    /// let reader = Reader::new(|env: i32| env + 1);
    ///
    /// // Chain with another reader that multiplies the result by 2
    /// let result = reader.bind(|x| Reader::new(move |_| x * 2));
    /// assert_eq!(result.run_reader(41), 84);
    ///
    /// // More complex example with environment access in the second reader
    /// let complex = reader.bind(|x| {
    ///     Reader::new(move |env: i32| format!("{} derived from {}", x, env))
    /// });
    /// assert_eq!(complex.run_reader(41), "42 derived from 41");
    /// ```
    pub fn bind<B: Clone + 'static>(
        &self,
        f: impl Fn(A) -> Reader<E, B> + 'static,
    ) -> Reader<E, B> {
        let run = self.run.clone();
        Reader::new(move |e: E| {
            let a = (run)(e.clone());
            f(a).run_reader(e)
        })
    }

    /// Modifies the environment before running a reader.
    ///
    /// This operation allows for local modifications to the environment that only
    /// affect the current reader, without changing the environment for subsequent
    /// operations in a chain.
    ///
    /// # Reader Monad Context
    ///
    /// The `local` operation is crucial for creating readers that work with modified
    /// environments while maintaining the original environment for other operations.
    /// It's similar to the concept of lexical scoping in programming languages.
    ///
    /// # Arguments
    ///
    /// * `f` - Function to modify the environment
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::reader::Reader;
    ///
    /// // Create a reader that works with strings
    /// let reader = Reader::new(|env: String| env.len());
    ///
    /// // Run with a modified environment (uppercase)
    /// let modified = reader.local(|e| e.to_uppercase());
    /// assert_eq!(modified.run_reader("hello".to_string()), 5);
    ///
    /// // The original environment transformation is preserved
    /// assert_eq!(reader.run_reader("hello".to_string()), 5);
    ///
    /// // More complex example with a configuration struct
    /// #[derive(Clone)]
    /// struct Config { debug: bool, value: i32 }
    ///
    /// let reader = Reader::new(|config: Config| {
    ///     if config.debug {
    ///         format!("Debug: {}", config.value)
    ///     } else {
    ///         format!("Value: {}", config.value)
    ///     }
    /// });
    ///
    /// // Run with modified config (debug mode enabled)
    /// let debug_reader = reader.local(|mut c| { c.debug = true; c });
    /// let config = Config { debug: false, value: 42 };
    ///
    /// assert_eq!(reader.run_reader(config.clone()), "Value: 42");
    /// assert_eq!(debug_reader.run_reader(config), "Debug: 42");
    /// ```
    pub fn local(&self, f: impl Fn(E) -> E + 'static) -> Reader<E, A> {
        let run = self.run.clone();
        Reader::new(move |e| (run)(f(e)))
    }

    /// Combines two readers using a function.
    ///
    /// This is part of the Applicative pattern implementation for Reader. It allows
    /// combining the results of two readers that share the same environment type,
    /// applying a function to both results.
    ///
    /// # Applicative Properties
    ///
    /// When used with appropriate functions, this operation helps satisfy the applicative laws.
    ///
    /// # Arguments
    ///
    /// * `other` - Another reader to combine with
    /// * `f` - Function to combine the results
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::reader::Reader;
    ///
    /// // Two readers that extract different information from the same environment
    /// let reader1 = Reader::new(|env: i32| env + 1);
    /// let reader2 = Reader::new(|env: i32| env * 2);
    ///
    /// // Combine them to produce a formatted string
    /// let combined = reader1.combine(&reader2, |x, y| format!("{} and {}", x, y));
    /// assert_eq!(combined.run_reader(20), "21 and 40");
    ///
    /// // Combine them for computation
    /// let sum = reader1.combine(&reader2, |x, y| x + y);
    /// assert_eq!(sum.run_reader(20), 61); // (20 + 1) + (20 * 2)
    /// ```
    pub fn combine<B, C>(
        &self,
        other: &Reader<E, B>,
        f: impl Fn(A, B) -> C + 'static,
    ) -> Reader<E, C>
    where
        B: Clone + 'static,
        C: Clone + 'static,
    {
        let run1 = self.run.clone();
        let run2 = other.run.clone();
        Reader::new(move |e: E| {
            let a = (run1)(e.clone());
            let b = (run2)(e);
            f(a, b)
        })
    }

    /// Lifts a binary function to work with readers.
    ///
    /// This is another part of the Applicative pattern implementation. It takes a function
    /// that works on plain values and lifts it to work with Reader values. This allows for
    /// more flexible composition of readers.
    ///
    /// # Applicative Context
    ///
    /// This function enables point-free style programming with readers, where functions
    /// can be composed without explicitly naming intermediate values.
    ///
    /// # Arguments
    ///
    /// * `f` - Binary function to lift
    ///
    /// # Returns
    ///
    /// A function that takes two readers and returns a new reader containing the result
    /// of applying the function to the results of both readers.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::reader::Reader;
    ///
    /// // Define a binary function
    /// let add = |x: i32, y: i32| x + y;
    ///
    /// // Create two readers
    /// let reader1 = Reader::new(|env: i32| env + 1);
    /// let reader2 = Reader::new(|env: i32| env * 2);
    ///
    /// // Lift the function to work with readers
    /// let lifted = Reader::lift2(add);
    ///
    /// // Apply the lifted function to the readers
    /// let result = lifted(&reader1, &reader2);
    /// assert_eq!(result.run_reader(20), 61); // (20 + 1) + (20 * 2)
    ///
    /// // This is equivalent to using combine
    /// let combined = reader1.combine(&reader2, add);
    /// assert_eq!(combined.run_reader(20), 61);
    /// ```
    pub fn lift2<B, C>(
        f: impl Fn(A, B) -> C + Clone + 'static,
    ) -> impl Fn(&Reader<E, A>, &Reader<E, B>) -> Reader<E, C>
    where
        B: Clone + 'static,
        C: Clone + 'static,
    {
        move |ra, rb| {
            let run_a = ra.run.clone();
            let run_b = rb.run.clone();
            let f = f.clone();
            Reader::new(move |e: E| {
                let a = (run_a)(e.clone());
                let b = (run_b)(e);
                f(a, b)
            })
        }
    }

    /// Creates a reader that returns a transformed version of the environment.
    /// Similar to `ask`, but allows specifying a transformation function.
    ///
    /// This is a convenience method that combines the functionality of `ask` and `fmap`
    /// into a single operation, making it easier to work with the environment.
    ///
    /// # Reader Monad Context
    ///
    /// `ask_with` is particularly useful when you need to extract or transform information
    /// from the environment without modifying it. It provides a more direct way to
    /// access and transform the environment compared to chaining `ask` and `fmap`.
    ///
    /// # Arguments
    ///
    /// * `f` - Function to transform the environment
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::reader::Reader;
    ///
    /// // Get the length of a string environment
    /// let reader: Reader<String, usize> = Reader::<String, usize>::ask_with(|s: &String| s.len());
    /// assert_eq!(reader.run_reader("hello".to_string()), 5);
    ///
    /// // Extract a specific property from a complex environment
    /// #[derive(Clone)]
    /// struct AppConfig {
    ///     name: String,
    ///     version: String,
    /// }
    ///
    /// let version_reader = Reader::<AppConfig, String>::ask_with(|config| config.version.clone());
    /// let config = AppConfig {
    ///     name: "MyApp".to_string(),
    ///     version: "1.0.0".to_string(),
    /// };
    /// assert_eq!(version_reader.run_reader(config), "1.0.0");
    /// ```
    pub fn ask_with<B: Clone + 'static>(f: impl Fn(&E) -> B + 'static) -> Reader<E, B> {
        Reader::new(move |e| f(&e))
    }

    /// Creates a reader that returns a part of the environment.
    /// Similar to `asks`, but allows specifying both a selector and a transformation.
    ///
    /// This method provides a convenient way to select a part of the environment and
    /// then transform it, all in a single operation. It's particularly useful for
    /// working with complex environment types.
    ///
    /// # Reader Monad Context
    ///
    /// `asks_with` enables more complex transformations of the environment by separating
    /// the selection of a part of the environment from its transformation. This separation
    /// of concerns can make code more readable and maintainable.
    ///
    /// # Arguments
    ///
    /// * `select` - Function to select a part of the environment
    /// * `f` - Function to transform the selected part
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::reader::Reader;
    ///
    /// #[derive(Clone)]
    /// struct Config {
    ///     count: i32,
    ///     name: String,
    /// }
    ///
    /// // Extract and format the count from the config
    /// let count_reader: Reader<Config, String> = Reader::<Config, String>::asks_with(
    ///     |c| c.count,
    ///     |count| format!("Count is {}", count)
    /// );
    /// assert_eq!(
    ///     count_reader.run_reader(Config { count: 42, name: "Test".to_string() }),
    ///     "Count is 42"
    /// );
    ///
    /// // Extract and transform the name
    /// let name_reader: Reader<Config, String> = Reader::<Config, String>::asks_with(
    ///     |c| c.name.clone(),
    ///     |name| name.to_uppercase()
    /// );
    /// assert_eq!(
    ///     name_reader.run_reader(Config { count: 42, name: "Test".to_string() }),
    ///     "TEST"
    /// );
    /// ```
    pub fn asks_with<B: Clone + 'static, C: Clone + 'static>(
        select: impl Fn(&E) -> B + 'static,
        f: impl Fn(B) -> C + 'static,
    ) -> Reader<E, C> {
        Reader::new(move |e| f(select(&e)))
    }
}
