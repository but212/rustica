//! # Validated Datatype
//!
//! The `Validated` datatype represents a validation result that can either be valid with a value
//! or invalid with a collection of errors. Unlike `Result`, which fails fast on the first error,
//! `Validated` can accumulate multiple errors during validation.
//!
//! ## Functional Programming Context
//!
//! In functional programming, validation is often handled through types that can represent
//! either success or failure. The `Validated` type is inspired by similar constructs in other
//! functional programming languages, such as:
//!
//! - `Validated` in Cats (Scala)
//! - `Validation` in Arrow (Kotlin)
//! - `Validation` in fp-ts (TypeScript)
//!
//! The key difference between `Validated` and `Result` is that `Validated` is designed for
//! scenarios where you want to collect all validation errors rather than stopping at the first one.
//!
//! ## Applicative Validation
//!
//! One of the most powerful aspects of `Validated` is its applicative instance, which allows
//! combining multiple validations while accumulating errors. This is particularly useful for
//! form validation, configuration validation, or any scenario where you want to report all
//! errors at once rather than one at a time.
//!
//! ```rust
//! use rustica::datatypes::validated::Validated;
//! use rustica::prelude::*;
//!
//! // Validate a username
//! fn validate_username(username: &str) -> Validated<String, String> {
//!     if username.len() >= 3 {
//!         Validated::valid(username.to_string())
//!     } else {
//!         Validated::invalid("Username must be at least 3 characters".to_string())
//!     }
//! }
//!
//! // Validate a password
//! fn validate_password(password: &str) -> Validated<String, String> {
//!     if password.len() >= 8 {
//!         Validated::valid(password.to_string())
//!     } else {
//!         Validated::invalid("Password must be at least 8 characters".to_string())
//!     }
//! }
//!
//! // Combine validations using lift2
//! let username_validation = validate_username("ab");
//! let password_validation = validate_password("1234");
//!
//! // This will collect both errors
//! let combined = username_validation.lift2(
//!     &password_validation,
//!     |username: &String, password: &String| format!("User: {}, Pass: {}", username, password)
//! );
//!
//! // Result contains both error messages
//! assert!(matches!(combined, Validated::SingleInvalid(_) | Validated::MultiInvalid(_)));
//!
//! ```
//!
//! ## Type Class Implementations
//!
//! `Validated` implements several type classes from functional programming:
//!
//! - **Functor**: Allows mapping over the valid value with `fmap`
//! - **Applicative**: Enables combining multiple validations with `apply`, `lift2`, and `lift3`
//! - **Monad**: Provides sequencing operations with `bind` and `join`
//!
//! ## Interoperability with Result
//!
//! `Validated` provides methods to convert to and from `Result`:
//!
//! ```rust
//! use rustica::datatypes::validated::Validated;
//!
//! // Convert from Result
//! let result: Result<i32, &str> = Ok(42);
//! let validated = Validated::from_result(&result);
//!
//! // Convert back to Result
//! let result_again = validated.to_result();
//! assert_eq!(result_again, Ok(42));
//! ```
//!
//! ## When to Use Validated vs Result
//!
//! - Use `Validated` when you want to collect multiple errors
//! - Use `Result` when you want to fail fast on the first error
//! - Use `Validated` for parallel, independent validations
//! - Use `Result` for sequential, dependent operations

use crate::traits::applicative::Applicative;
use crate::traits::composable::Composable;
use crate::traits::foldable::Foldable;
use crate::traits::functor::Functor;
use crate::traits::hkt::HKT;
use crate::traits::identity::Identity;
use crate::traits::monad::Monad;
use crate::traits::pure::Pure;
use smallvec::SmallVec;

/// A validation type that can accumulate multiple errors.
///
/// `Validated<E, A>` represents either a valid value of type `A` or a collection of
/// errors of type `E`. Unlike `Result`, which fails fast on the first error,
/// `Validated` can collect multiple errors during validation.
///
/// # Performance Optimization
///
/// `Validated` uses `SmallVec<[E; 4]>` internally to store errors, which optimizes for
/// the common case of having 1-4 validation errors without requiring heap allocation.
/// This provides better performance than using `Vec<E>` for small error lists.
///
/// # Type Parameters
///
/// * `E` - The error type
/// * `A` - The value type
///
/// # Examples
///
/// ```rust
/// use rustica::datatypes::validated::Validated;
///
/// // Create a valid value
/// let valid: Validated<&str, i32> = Validated::valid(42);
///
/// // Create an invalid value with one error
/// let invalid: Validated<&str, i32> = Validated::invalid("error message");
///
/// // Map over valid values
/// let mapped = valid.map_valid(&|x| x * 2);
/// ```
///
/// # Functional Programming Context
///
/// `Validated` implements several type classes from functional programming:
///
/// - **Functor**: Transform the inner value with `fmap`
/// - **Applicative**: Combine multiple validations with `apply`, `lift2`, and `lift3`
/// - **Monad**: Chain computations with `bind`
///
/// These implementations allow `Validated` to be used in a functional programming style,
/// enabling composition and transformation of validations.
#[derive(Clone, PartialEq, PartialOrd, Eq, Ord, Debug, Hash)]
pub enum Validated<E, A> {
    /// Represents a valid value of type `A`.
    Valid(A),
    /// Represents an invalid state with a single error of type `E`.
    /// Optimized for the common case of a single error.
    SingleInvalid(E),
    /// Represents an invalid state with multiple errors of type `E`.
    /// Uses SmallVec for better performance with small error counts.
    MultiInvalid(SmallVec<[E; 4]>),
}

impl<E: Clone, A: Clone> Validated<E, A> {
    /// Creates a new valid instance.
    ///
    /// # Arguments
    ///
    /// * `x` - The valid value
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::validated::Validated;
    ///
    /// let valid: Validated<(), i32> = Validated::valid(42);
    /// ```
    #[inline]
    pub fn valid(x: A) -> Self {
        Validated::Valid(x)
    }

    /// Creates a new invalid instance with a single error.
    ///
    /// # Arguments
    ///
    /// * `e` - The error value
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::validated::Validated;
    ///
    /// let invalid: Validated<&str, ()> = Validated::invalid("validation error");
    /// ```
    #[inline]
    pub fn invalid(e: E) -> Self {
        Validated::SingleInvalid(e)
    }

    /// Creates a new invalid instance with multiple errors from a collection.
    ///
    /// # Arguments
    ///
    /// * `errors` - A collection of error values that can be converted into a SmallVec
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::validated::Validated;
    ///
    /// let invalid: Validated<&str, ()> = Validated::invalid_vec(vec!["error1", "error2"]);
    /// ```
    #[inline]
    pub fn invalid_vec<I>(errors: I) -> Self
    where
        I: IntoIterator<Item = E>,
    {
        let e: SmallVec<[E; 4]> = errors.into_iter().collect();
        match e.len() {
            0 => panic!("Validated::invalid_vec requires at least one error"),
            1 => Validated::SingleInvalid(e[0].clone()),
            _ => Validated::MultiInvalid(e),
        }
    }

    /// Maps a function over the valid value.
    ///
    /// If this is valid, applies the function to transform the value.
    /// If this is invalid, returns the errors unchanged.
    ///
    /// # Performance
    ///
    /// This method clones the errors when returning an invalid result. For better performance
    /// when you have ownership of the Validated value, use `map_valid_owned`.
    ///
    /// # Type Parameters
    ///
    /// * `B`: The result type of the mapping function
    /// * `F`: The type of the mapping function
    ///
    /// # Arguments
    ///
    /// * `f` - Function to apply to the valid value
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::validated::Validated;
    ///
    /// let valid: Validated<&str, i32> = Validated::valid(42);
    /// let mapped = valid.map_valid(&|x| x * 2);
    /// assert_eq!(mapped, Validated::valid(84));
    /// ```
    #[inline]
    pub fn map_valid<B, F>(&self, f: &F) -> Validated<E, B>
    where
        F: Fn(&A) -> B,
        B: Clone,
    {
        match self {
            Validated::Valid(x) => Validated::Valid(f(x)),
            Validated::SingleInvalid(e) => Validated::SingleInvalid(e.clone()),
            Validated::MultiInvalid(e) => Validated::MultiInvalid(e.clone()),
        }
    }

    /// Maps a function over the valid value, taking ownership of the Validated.
    ///
    /// If this is valid, applies the function to transform the value.
    /// If this is invalid, returns the errors unchanged.
    ///
    /// # Performance
    ///
    /// This method avoids cloning errors when returning an invalid result, making it more
    /// efficient than `map_valid` when you have ownership of the Validated value.
    ///
    /// # Type Parameters
    ///
    /// * `B`: The result type of the mapping function
    /// * `F`: The type of the mapping function
    ///
    /// # Arguments
    ///
    /// * `f` - Function to apply to the valid value
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::validated::Validated;
    ///
    /// let valid: Validated<&str, i32> = Validated::valid(42);
    /// let mapped = valid.map_valid_owned(|x| x * 2);
    /// assert_eq!(mapped, Validated::valid(84));
    /// ```
    #[inline]
    pub fn map_valid_owned<B, F>(self, f: F) -> Validated<E, B>
    where
        F: FnOnce(A) -> B,
        B: Clone,
    {
        match self {
            Validated::Valid(x) => Validated::Valid(f(x)),
            Validated::SingleInvalid(e) => Validated::SingleInvalid(e),
            Validated::MultiInvalid(e) => Validated::MultiInvalid(e),
        }
    }

    /// Maps a function over the error values.
    ///
    /// If this is invalid, applies the function to transform each error.
    /// If this is valid, returns the value unchanged.
    ///
    /// # Performance
    ///
    /// This method clones the valid value when returning a valid result. For better performance
    /// when you have ownership of the Validated value, use `map_invalid_owned`.
    ///
    /// # Type Parameters
    ///
    /// * `G`: The result type of the mapping function
    /// * `F`: The type of the mapping function
    ///
    /// # Arguments
    ///
    /// * `f` - Function to apply to each error
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::validated::Validated;
    ///
    /// let invalid: Validated<&str, i32> = Validated::invalid("error");
    /// let mapped = invalid.map_invalid(&|e| format!("Error: {}", e));
    /// assert_eq!(mapped, Validated::invalid("Error: error"));
    /// ```
    #[inline]
    pub fn map_invalid<G, F>(&self, f: &F) -> Validated<G, A>
    where
        F: Fn(&E) -> G,
        G: Clone,
    {
        match self {
            Validated::Valid(x) => Validated::Valid(x.clone()),
            Validated::SingleInvalid(e) => Validated::SingleInvalid(f(e)),
            Validated::MultiInvalid(es) => {
                let transformed: SmallVec<[G; 4]> = es.iter().map(f).collect();
                Validated::MultiInvalid(transformed)
            }
        }
    }

    /// Maps a function over the error values, taking ownership of the Validated.
    ///
    /// If this is invalid, applies the function to transform each error.
    /// If this is valid, returns the value unchanged.
    ///
    /// # Performance
    ///
    /// This method avoids cloning the valid value when returning a valid result, making it more
    /// efficient than `map_invalid` when you have ownership of the Validated value.
    ///
    /// # Type Parameters
    ///
    /// * `G`: The result type of the mapping function
    /// * `F`: The type of the mapping function
    ///
    /// # Arguments
    ///
    /// * `f` - Function to apply to each error
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::validated::Validated;
    ///
    /// let invalid: Validated<&str, i32> = Validated::invalid("error");
    /// let mapped = invalid.map_invalid_owned(|e| format!("Error: {}", e));
    /// assert_eq!(mapped, Validated::invalid("Error: error"));
    /// ```
    #[inline]
    pub fn map_invalid_owned<G, F>(self, f: F) -> Validated<G, A>
    where
        F: Fn(E) -> G,
        G: Clone,
    {
        match self {
            Validated::Valid(x) => Validated::Valid(x),
            Validated::SingleInvalid(e) => Validated::SingleInvalid(f(e)),
            Validated::MultiInvalid(es) => {
                let transformed: SmallVec<[G; 4]> = es.into_iter().map(f).collect();
                Validated::MultiInvalid(transformed)
            }
        }
    }

    /// Converts from `Result<A, E>` to `Validated<E, A>`.
    ///
    /// # Type Parameters
    ///
    /// * `A`: The value type
    /// * `E`: The error type
    ///
    /// # Arguments
    ///
    /// * `result` - The Result to convert
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::validated::Validated;
    ///
    /// let result: Result<i32, &str> = Ok(42);
    /// let validated = Validated::from_result(&result);
    /// assert_eq!(validated, Validated::valid(42));
    ///
    /// let error_result: Result<i32, &str> = Err("error");
    /// let validated = Validated::from_result(&error_result);
    /// assert_eq!(validated, Validated::invalid("error"));
    /// ```
    #[inline]
    pub fn from_result(result: &Result<A, E>) -> Validated<E, A> {
        match result {
            Ok(value) => Validated::Valid(value.clone()),
            Err(err) => Validated::SingleInvalid(err.clone()),
        }
    }

    /// Converts from `Result<A, E>` to `Validated<E, A>`, taking ownership of the Result.
    ///
    /// # Type Parameters
    ///
    /// * `A`: The value type
    /// * `E`: The error type
    ///
    /// # Arguments
    ///
    /// * `result` - The Result to convert and consume
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::validated::Validated;
    ///
    /// let result: Result<i32, String> = Ok(42);
    /// let validated = Validated::from_result_owned(result);
    /// assert_eq!(validated, Validated::valid(42));
    ///
    /// let error_result: Result<i32, String> = Err("error".to_string());
    /// let validated = Validated::from_result_owned(error_result);
    /// assert!(validated.is_invalid());
    /// ```
    #[inline]
    pub fn from_result_owned(result: Result<A, E>) -> Validated<E, A> {
        match result {
            Ok(value) => Validated::Valid(value),
            Err(err) => Validated::SingleInvalid(err),
        }
    }

    /// Converts this `Validated` into a `Result`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::validated::Validated;
    ///
    /// let valid: Validated<&str, i32> = Validated::valid(42);
    /// let result = valid.to_result();
    /// assert_eq!(result, Ok(42));
    ///
    /// let invalid: Validated<&str, i32> = Validated::invalid("error");
    /// assert!(invalid.to_result().is_err());
    /// ```
    #[inline]
    pub fn to_result(&self) -> Result<A, SmallVec<[E; 4]>> {
        match self {
            Validated::Valid(a) => Ok(a.clone()),
            Validated::SingleInvalid(e) => {
                let mut errors = SmallVec::new();
                errors.push(e.clone());
                Err(errors)
            }
            Validated::MultiInvalid(e) => Err(e.clone()),
        }
    }

    /// Converts this `Validated` into a `Result`, taking ownership of the Validated.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::validated::Validated;
    ///
    /// let valid: Validated<String, i32> = Validated::valid(42);
    /// let result = valid.to_result_owned();
    /// assert_eq!(result, Ok(42));
    ///
    /// let invalid: Validated<String, i32> = Validated::invalid("error".to_string());
    /// assert!(invalid.to_result_owned().is_err());
    /// ```
    #[inline]
    pub fn to_result_owned(self) -> Result<A, SmallVec<[E; 4]>> {
        match self {
            Validated::Valid(a) => Ok(a),
            Validated::SingleInvalid(e) => {
                let mut errors = SmallVec::new();
                errors.push(e);
                Err(errors)
            }
            Validated::MultiInvalid(e) => Err(e),
        }
    }

    /// Converts from `Option<A>` to `Validated<E, A>` with a provided error.
    ///
    /// If the Option is Some, returns a Valid value.
    /// If the Option is None, returns an Invalid with the provided error.
    ///
    /// # Arguments
    ///
    /// * `option` - The Option to convert
    /// * `error` - The error to use if the Option is None
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::validated::Validated;
    ///
    /// let some_value: Option<i32> = Some(42);
    /// let validated: Validated<&str, i32> = Validated::from_option(&some_value, &"missing value");
    /// assert_eq!(validated, Validated::valid(42));
    ///
    /// let none_value: Option<i32> = None;
    /// let validated: Validated<&str, i32> = Validated::from_option(&none_value, &"missing value");
    /// assert_eq!(validated, Validated::invalid("missing value"));
    /// ```
    #[inline]
    pub fn from_option(option: &Option<A>, error: &E) -> Self {
        match option {
            Some(value) => Validated::Valid(value.clone()),
            None => Validated::SingleInvalid(error.clone()),
        }
    }

    /// Converts from `Option<A>` to `Validated<E, A>` with a provided error, taking ownership.
    ///
    /// If the Option is Some, returns a Valid value.
    /// If the Option is None, returns an Invalid with the provided error.
    ///
    /// # Arguments
    ///
    /// * `option` - The Option to convert and consume
    /// * `error` - The error to use if the Option is None
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::validated::Validated;
    ///
    /// let some_value: Option<i32> = Some(42);
    /// let validated: Validated<String, i32> = Validated::from_option_owned(some_value, "missing value".to_string());
    /// assert_eq!(validated, Validated::valid(42));
    ///
    /// let none_value: Option<i32> = None;
    /// let validated: Validated<String, i32> = Validated::from_option_owned(none_value, "missing value".to_string());
    /// assert!(validated.is_invalid());
    /// ```
    #[inline]
    pub fn from_option_owned(option: Option<A>, error: E) -> Self {
        match option {
            Some(value) => Validated::Valid(value),
            None => Validated::SingleInvalid(error),
        }
    }

    /// Converts from `Option<A>` to `Validated<E, A>` with a function to generate the error.
    ///
    /// If the Option is Some, returns a Valid value.
    /// If the Option is None, returns an Invalid with the error from the provided function.
    ///
    /// # Arguments
    ///
    /// * `option` - The Option to convert
    /// * `error_fn` - Function to generate the error if the Option is None
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::validated::Validated;
    ///
    /// let some_value: Option<i32> = Some(42);
    /// let validated: Validated<&str, i32> = Validated::from_option_with(&some_value, &|| "missing value");
    /// assert_eq!(validated, Validated::valid(42));
    ///
    /// let none_value: Option<i32> = None;
    /// let validated: Validated<&str, i32> = Validated::from_option_with(&none_value, &|| "missing value");
    /// assert_eq!(validated, Validated::invalid("missing value"));
    /// ```
    #[inline]
    pub fn from_option_with<F>(option: &Option<A>, error_fn: &F) -> Self
    where
        F: Fn() -> E,
    {
        match option {
            Some(value) => Validated::Valid(value.clone()),
            None => Validated::SingleInvalid(error_fn()),
        }
    }

    /// Converts from `Option<A>` to `Validated<E, A>` with a function to generate the error, taking ownership.
    ///
    /// If the Option is Some, returns a Valid value.
    /// If the Option is None, returns an Invalid with the error from the provided function.
    ///
    /// # Arguments
    ///
    /// * `option` - The Option to convert and consume
    /// * `error_fn` - Function to generate the error if the Option is None
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::validated::Validated;
    ///
    /// let some_value: Option<i32> = Some(42);
    /// let validated: Validated<String, i32> = Validated::from_option_with_owned(some_value, || "missing value".to_string());
    /// assert_eq!(validated, Validated::valid(42));
    ///
    /// let none_value: Option<i32> = None;
    /// let validated: Validated<String, i32> = Validated::from_option_with_owned(none_value, || "missing value".to_string());
    /// assert!(validated.is_invalid());
    /// ```
    #[inline]
    pub fn from_option_with_owned<F>(option: Option<A>, error_fn: F) -> Self
    where
        F: FnOnce() -> E,
    {
        match option {
            Some(value) => Validated::Valid(value),
            None => Validated::SingleInvalid(error_fn()),
        }
    }

    /// Unwraps a valid value or returns a default.
    ///
    /// If this is valid, returns the valid value.
    /// If this is invalid, returns the provided default.
    ///
    /// # Arguments
    ///
    /// * `default` - The default value to return if invalid
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::validated::Validated;
    ///
    /// let valid: Validated<&str, i32> = Validated::valid(42);
    /// assert_eq!(valid.unwrap_or(&0), 42);
    ///
    /// let invalid: Validated<&str, i32> = Validated::invalid("error");
    /// assert_eq!(invalid.unwrap_or(&0), 0);
    /// ```
    #[inline]
    pub fn unwrap_or(&self, default: &A) -> A {
        match self {
            Validated::Valid(x) => x.clone(),
            _ => default.clone(),
        }
    }

    /// Unwraps a valid value or computes a default.
    ///
    /// If this is valid, returns the valid value.
    /// If this is invalid, calls the provided function with the errors to get a default.
    ///
    /// # Arguments
    ///
    /// * `f` - Function to compute a default value from the errors
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::validated::Validated;
    /// use smallvec::SmallVec;
    ///
    /// let valid: Validated<&str, i32> = Validated::valid(42);
    /// let result = valid.unwrap_or_else(&|_: &SmallVec<[&str; 4]>| 0);
    /// assert_eq!(result, 42);
    ///
    /// let invalid: Validated<&str, i32> = Validated::invalid("error");
    /// let result = invalid.unwrap_or_else(&|errors: &SmallVec<[&str; 4]>| {
    ///     assert_eq!(errors.len(), 1);
    ///     assert_eq!(errors[0], "error");
    ///     0
    /// });
    /// assert_eq!(result, 0);
    /// ```
    #[inline]
    pub fn unwrap_or_else<F>(&self, f: &F) -> A
    where
        F: Fn(&SmallVec<[E; 4]>) -> A,
    {
        match self {
            Validated::Valid(x) => x.clone(),
            Validated::SingleInvalid(e) => {
                let mut errors = SmallVec::new();
                errors.push(e.clone());
                f(&errors)
            }
            Validated::MultiInvalid(e) => f(e),
        }
    }

    /// Combines multiple Validated values using a function.
    ///
    /// This is similar to `lift2` but works with a slice of Validated values.
    /// If all values are valid, applies the function to combine them.
    /// If any values are invalid, collects all errors.
    ///
    /// # Type Parameters
    ///
    /// * `B`: The result type of the combining function
    /// * `F`: The type of the combining function
    ///
    /// # Arguments
    ///
    /// * `values` - Slice of Validated values
    /// * `f` - Function to combine valid values
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::validated::Validated;
    ///
    /// let a: Validated<&str, i32> = Validated::valid(1);
    /// let b: Validated<&str, i32> = Validated::valid(2);
    /// let c: Validated<&str, i32> = Validated::valid(3);
    ///
    /// let values = [&a, &b, &c];
    /// let sum = Validated::sequence(&values, &|vs| {
    ///     vs.iter().sum()
    /// });
    ///
    /// assert_eq!(sum, Validated::valid(6));
    /// ```
    #[inline]
    pub fn sequence<B, F>(values: &[&Validated<E, A>], f: &F) -> Validated<E, B>
    where
        F: Fn(&[A]) -> B,
        B: Clone,
    {
        // First check if all values are valid
        let mut all_valid = true;
        let mut error_count = 0;

        for v in values {
            if matches!(v, Validated::SingleInvalid(_) | Validated::MultiInvalid(_)) {
                all_valid = false;
                error_count += match v {
                    Validated::SingleInvalid(_) => 1,
                    Validated::MultiInvalid(es) => es.len(),
                    _ => 0,
                };
            }
        }

        if all_valid {
            // Extract all valid values
            let valid_values: Vec<A> = values
                .iter()
                .filter_map(|v| match v {
                    Validated::Valid(x) => Some(x.clone()),
                    _ => None,
                })
                .collect();

            Validated::Valid(f(&valid_values))
        } else {
            // Collect all errors
            let mut all_errors = SmallVec::<[E; 4]>::with_capacity(error_count);

            for v in values {
                match v {
                    Validated::SingleInvalid(e) => all_errors.push(e.clone()),
                    Validated::MultiInvalid(es) => all_errors.extend(es.iter().cloned()),
                    _ => {}
                }
            }

            if all_errors.len() == 1 {
                Validated::SingleInvalid(all_errors.pop().unwrap())
            } else {
                Validated::MultiInvalid(all_errors)
            }
        }
    }

    /// Collects an iterator of Validated values into a single Validated value.
    ///
    /// If all values in the iterator are valid, returns a Valid value containing a collection of all values.
    /// If any values are invalid, returns an Invalid value containing all errors.
    ///
    /// # Type Parameters
    ///
    /// * `I`: The iterator type
    /// * `C`: The collection type to collect valid values into
    ///
    /// # Arguments
    ///
    /// * `iter` - Iterator of Validated values
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::validated::Validated;
    ///
    /// let values = vec![
    ///     Validated::<&str, i32>::valid(1),
    ///     Validated::<&str, i32>::valid(2),
    ///     Validated::<&str, i32>::valid(3),
    /// ];
    ///
    /// let collected: Validated<&str, Vec<i32>> = Validated::collect::<_, Vec<_>>(values.iter());
    /// assert_eq!(collected, Validated::valid(vec![1, 2, 3]));
    ///
    /// let mixed = vec![
    ///     Validated::<&str, i32>::valid(1),
    ///     Validated::<&str, i32>::invalid("error"),
    ///     Validated::<&str, i32>::valid(3),
    /// ];
    ///
    /// let collected: Validated<&str, Vec<i32>> = Validated::collect::<_, Vec<_>>(mixed.iter());
    /// assert!(collected.is_invalid());
    /// ```
    #[inline]
    pub fn collect<I, C>(iter: I) -> Validated<E, C>
    where
        I: Iterator,
        I::Item: AsRef<Validated<E, A>>,
        C: FromIterator<A>,
    {
        let mut all_valid = true;
        let mut errors = SmallVec::<[E; 4]>::new();
        let mut valid_values = Vec::new();

        for item in iter {
            let validated = item.as_ref();
            match validated {
                Validated::Valid(x) => {
                    valid_values.push(x.clone());
                }
                Validated::SingleInvalid(e) => {
                    all_valid = false;
                    errors.push(e.clone());
                }
                Validated::MultiInvalid(es) => {
                    all_valid = false;
                    errors.extend(es.iter().cloned());
                }
            }
        }

        if all_valid {
            Validated::Valid(valid_values.into_iter().collect())
        } else if errors.len() == 1 {
            Validated::SingleInvalid(errors.pop().unwrap())
        } else {
            Validated::MultiInvalid(errors)
        }
    }

    #[cfg(feature = "async")]
    /// Maps an async function over the valid value.
    ///
    /// If this is valid, applies the async function to transform the value.
    /// If this is invalid, returns the errors unchanged.
    ///
    /// # Type Parameters
    ///
    /// * `B`: The result type of the mapping function
    /// * `F`: The type of the mapping function
    /// * `Fut`: The future type returned by the mapping function
    ///
    /// # Arguments
    ///
    /// * `f` - Async function to apply to the valid value
    ///
    /// # Examples
    ///
    /// ```rust
    /// # #[cfg(feature = "async")]
    /// # async fn example() {
    /// use rustica::datatypes::validated::Validated;
    ///
    /// let valid: Validated<&str, i32> = Validated::valid(42);
    /// let mapped = valid.map_valid_async(|x| async move { x * 2 }).await;
    /// assert_eq!(mapped, Validated::valid(84));
    /// # }
    /// ```
    #[inline]
    pub async fn map_valid_async<B, F, Fut>(&self, f: F) -> Validated<E, B>
    where
        F: Fn(A) -> Fut + Send + 'static,
        Fut: std::future::Future<Output = B> + Send,
        B: Clone + Send + 'static,
    {
        match self {
            Validated::Valid(x) => {
                let result = f(x.clone()).await;
                Validated::Valid(result)
            }
            Validated::SingleInvalid(e) => Validated::SingleInvalid(e.clone()),
            Validated::MultiInvalid(e) => Validated::MultiInvalid(e.clone()),
        }
    }

    #[cfg(feature = "async")]
    /// Maps an async function over the error values.
    ///
    /// If this is invalid, applies the async function to transform each error.
    /// If this is valid, returns the value unchanged.
    ///
    /// # Type Parameters
    ///
    /// * `G`: The result type of the mapping function
    /// * `F`: The type of the mapping function
    /// * `Fut`: The future type returned by the mapping function
    ///
    /// # Arguments
    ///
    /// * `f` - Async function to apply to each error
    ///
    /// # Examples
    ///
    /// ```rust
    /// # #[cfg(feature = "async")]
    /// # async fn example() {
    /// use rustica::datatypes::validated::Validated;
    ///
    /// let invalid: Validated<&str, i32> = Validated::invalid("error");
    /// let mapped = invalid.map_invalid_async(|e| async move { format!("Error: {}", e) }).await;
    /// assert_eq!(mapped, Validated::invalid("Error: error"));
    /// # }
    /// ```
    #[inline]
    pub async fn map_invalid_async<G, F, Fut>(&self, f: F) -> Validated<G, A>
    where
        F: Fn(E) -> Fut + Send + 'static + Clone,
        Fut: std::future::Future<Output = G> + Send,
        G: Clone + Send + 'static,
    {
        match self {
            Validated::Valid(x) => Validated::Valid(x.clone()),
            Validated::SingleInvalid(e) => {
                let result = f(e.clone()).await;
                Validated::SingleInvalid(result)
            }
            Validated::MultiInvalid(es) => {
                let futures = es.iter().map(|e| f(e.clone()));

                // Using futures::future::join_all to run all futures concurrently
                let results = futures::future::join_all(futures).await;
                let transformed: SmallVec<[G; 4]> = results.into_iter().collect();

                Validated::MultiInvalid(transformed)
            }
        }
    }

    #[cfg(feature = "async")]
    /// Chains an async validation operation to this Validated.
    ///
    /// If this is valid, applies the async function to the value to get another Validated.
    /// If this is invalid, returns the errors unchanged.
    ///
    /// # Type Parameters
    ///
    /// * `B`: The result type of the mapping function
    /// * `F`: The type of the mapping function
    /// * `Fut`: The future type returned by the mapping function
    ///
    /// # Arguments
    ///
    /// * `f` - Async function that returns another Validated
    ///
    /// # Examples
    ///
    /// ```rust
    /// # #[cfg(feature = "async")]
    /// # async fn example() {
    /// use rustica::datatypes::validated::Validated;
    ///
    /// let valid: Validated<&str, i32> = Validated::valid(42);
    /// let chained = valid.and_then_async(|x| async move {
    ///     if x > 50 {
    ///         Validated::<&str, String>::valid(x.to_string())
    ///     } else {
    ///         Validated::<&str, String>::invalid("Value too small")
    ///     }
    /// }).await;
    ///
    /// assert_eq!(chained, Validated::<&str, String>::invalid("Value too small"));
    /// # }
    /// ```
    #[inline]
    pub async fn and_then_async<B, F, Fut>(&self, f: F) -> Validated<E, B>
    where
        F: Fn(A) -> Fut + Send + 'static,
        Fut: std::future::Future<Output = Validated<E, B>> + Send,
        B: Clone + Send + 'static,
    {
        match self {
            Validated::Valid(x) => f(x.clone()).await,
            Validated::SingleInvalid(e) => Validated::SingleInvalid(e.clone()),
            Validated::MultiInvalid(e) => Validated::MultiInvalid(e.clone()),
        }
    }
}

impl<E, A> HKT for Validated<E, A> {
    type Source = A;
    type Output<T> = Validated<E, T>;
}

impl<E: Clone, A> Pure for Validated<E, A> {
    #[inline]
    fn pure<T: Clone>(x: &T) -> Self::Output<T> {
        Validated::valid(x.clone())
    }

    #[inline]
    fn pure_owned<T: Clone>(x: T) -> Self::Output<T> {
        Validated::valid(x)
    }
}

impl<E: Clone, A: Clone> Functor for Validated<E, A> {
    #[inline]
    fn fmap<B, F>(&self, f: F) -> Self::Output<B>
    where
        F: Fn(&Self::Source) -> B,
        B: Clone,
    {
        self.map_valid(&f)
    }

    #[inline]
    fn fmap_owned<B, F>(self, f: F) -> Self::Output<B>
    where
        Self: Sized,
        F: FnOnce(Self::Source) -> B,
        B: Clone,
    {
        self.map_valid_owned(f)
    }
}

impl<E: Clone, A: Clone> Applicative for Validated<E, A> {
    /// Apply operation for Validated.
    ///
    /// This defines application of a function within one Validated to a value in another Validated.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::validated::Validated;
    /// use rustica::traits::applicative::Applicative;
    ///
    /// let valid_fn: Validated<&str, fn(i32) -> String> = Validated::valid(|x| x.to_string());
    /// let valid_val: Validated<&str, i32> = Validated::valid(42);
    /// let result = valid_fn.apply(&valid_val);
    /// assert_eq!(result, Validated::valid("42".to_string()));
    /// ```
    #[inline]
    fn apply<B, F>(&self, rf: &Self::Output<F>) -> Self::Output<B>
    where
        F: Fn(&A) -> B,
    {
        match (self, rf) {
            (Validated::Valid(a), Validated::Valid(f)) => Validated::Valid(f(a)),
            (Validated::Valid(_), Validated::SingleInvalid(e)) => {
                Validated::SingleInvalid(e.clone())
            }
            (Validated::Valid(_), Validated::MultiInvalid(e)) => Validated::MultiInvalid(e.clone()),
            (Validated::SingleInvalid(e), Validated::Valid(_)) => {
                Validated::SingleInvalid(e.clone())
            }
            (Validated::SingleInvalid(e1), Validated::SingleInvalid(e2)) => {
                let mut errors = SmallVec::<[E; 4]>::new();
                errors.push(e1.clone());
                errors.push(e2.clone());
                Validated::MultiInvalid(errors)
            }
            (Validated::SingleInvalid(e1), Validated::MultiInvalid(e2)) => {
                let mut errors = SmallVec::<[E; 4]>::with_capacity(1 + e2.len());
                errors.push(e1.clone());
                errors.extend(e2.iter().cloned());
                Validated::MultiInvalid(errors)
            }
            (Validated::MultiInvalid(e), Validated::Valid(_)) => Validated::MultiInvalid(e.clone()),
            (Validated::MultiInvalid(e1), Validated::SingleInvalid(e2)) => {
                let mut errors = SmallVec::<[E; 4]>::with_capacity(e1.len() + 1);
                errors.extend(e1.iter().cloned());
                errors.push(e2.clone());
                Validated::MultiInvalid(errors)
            }
            (Validated::MultiInvalid(e1), Validated::MultiInvalid(e2)) => {
                let mut errors = SmallVec::<[E; 4]>::with_capacity(e1.len() + e2.len());
                errors.extend(e1.iter().cloned());
                errors.extend(e2.iter().cloned());
                Validated::MultiInvalid(errors)
            }
        }
    }

    #[inline]
    fn apply_owned<B, F>(self, rf: Self::Output<F>) -> Self::Output<B>
    where
        Self: Sized,
        F: FnOnce(A) -> B,
    {
        match (self, rf) {
            (Validated::Valid(a), Validated::Valid(f)) => Validated::Valid(f(a)),
            (Validated::Valid(_), Validated::SingleInvalid(e)) => Validated::SingleInvalid(e),
            (Validated::Valid(_), Validated::MultiInvalid(e)) => Validated::MultiInvalid(e),
            (Validated::SingleInvalid(e), Validated::Valid(_)) => Validated::SingleInvalid(e),
            (Validated::SingleInvalid(e1), Validated::SingleInvalid(e2)) => {
                let mut errors = SmallVec::new();
                errors.push(e1);
                errors.push(e2);
                Validated::MultiInvalid(errors)
            }
            (Validated::SingleInvalid(e1), Validated::MultiInvalid(mut e2)) => {
                e2.insert(0, e1);
                Validated::MultiInvalid(e2)
            }
            (Validated::MultiInvalid(e), Validated::Valid(_)) => Validated::MultiInvalid(e),
            (Validated::MultiInvalid(mut e1), Validated::SingleInvalid(e2)) => {
                e1.push(e2);
                Validated::MultiInvalid(e1)
            }
            (Validated::MultiInvalid(mut e1), Validated::MultiInvalid(e2)) => {
                e1.extend(e2);
                Validated::MultiInvalid(e1)
            }
        }
    }

    #[inline]
    fn lift2<B, C, F>(&self, rb: &Self::Output<B>, f: F) -> Self::Output<C>
    where
        F: Fn(&Self::Source, &B) -> C,
        B: Clone,
        C: Clone,
    {
        match (self, rb) {
            (Validated::Valid(a), Validated::Valid(b)) => Validated::Valid(f(a, b)),
            (Validated::Valid(_), Validated::SingleInvalid(e)) => {
                Validated::SingleInvalid(e.clone())
            }
            (Validated::Valid(_), Validated::MultiInvalid(e)) => Validated::MultiInvalid(e.clone()),
            (Validated::SingleInvalid(e), Validated::Valid(_)) => {
                Validated::SingleInvalid(e.clone())
            }
            (Validated::SingleInvalid(e1), Validated::SingleInvalid(e2)) => {
                let mut errors = SmallVec::<[E; 4]>::new();
                errors.push(e1.clone());
                errors.push(e2.clone());
                Validated::MultiInvalid(errors)
            }
            (Validated::SingleInvalid(e1), Validated::MultiInvalid(e2)) => {
                let mut errors = SmallVec::<[E; 4]>::with_capacity(1 + e2.len());
                errors.push(e1.clone());
                errors.extend(e2.iter().cloned());
                Validated::MultiInvalid(errors)
            }
            (Validated::MultiInvalid(e), Validated::Valid(_)) => Validated::MultiInvalid(e.clone()),
            (Validated::MultiInvalid(e1), Validated::SingleInvalid(e2)) => {
                let mut errors = SmallVec::<[E; 4]>::with_capacity(e1.len() + 1);
                errors.extend(e1.iter().cloned());
                errors.push(e2.clone());
                Validated::MultiInvalid(errors)
            }
            (Validated::MultiInvalid(e1), Validated::MultiInvalid(e2)) => {
                let mut errors = SmallVec::<[E; 4]>::with_capacity(e1.len() + e2.len());
                errors.extend(e1.iter().cloned());
                errors.extend(e2.iter().cloned());
                Validated::MultiInvalid(errors)
            }
        }
    }

    #[inline]
    fn lift2_owned<B, C, F>(self, rb: Self::Output<B>, f: F) -> Self::Output<C>
    where
        Self: Sized,
        F: FnOnce(Self::Source, B) -> C,
        B: Clone,
        C: Clone,
    {
        match (self, rb) {
            (Validated::Valid(a), Validated::Valid(b)) => Validated::Valid(f(a, b)),
            (Validated::SingleInvalid(e), Validated::Valid(_)) => Validated::SingleInvalid(e),
            (Validated::Valid(_), Validated::SingleInvalid(e)) => Validated::SingleInvalid(e),
            (Validated::SingleInvalid(e1), Validated::SingleInvalid(e2)) => {
                let mut errors = SmallVec::new();
                errors.push(e1);
                errors.push(e2);
                Validated::MultiInvalid(errors)
            }
            (Validated::SingleInvalid(e1), Validated::MultiInvalid(mut e2)) => {
                e2.insert(0, e1);
                Validated::MultiInvalid(e2)
            }
            (Validated::MultiInvalid(e), Validated::Valid(_)) => Validated::MultiInvalid(e),
            (Validated::MultiInvalid(mut e1), Validated::SingleInvalid(e2)) => {
                e1.push(e2);
                Validated::MultiInvalid(e1)
            }
            (Validated::MultiInvalid(mut e1), Validated::MultiInvalid(e2)) => {
                e1.extend(e2);
                Validated::MultiInvalid(e1)
            }
            (Validated::Valid(_), Validated::MultiInvalid(e)) => Validated::MultiInvalid(e),
        }
    }

    #[inline]
    fn lift3<B, C, D, F>(&self, rb: &Self::Output<B>, rc: &Self::Output<C>, f: F) -> Self::Output<D>
    where
        F: Fn(&Self::Source, &B, &C) -> D,
        B: Clone,
        C: Clone,
        D: Clone,
    {
        match (self, rb, rc) {
            (Validated::Valid(a), Validated::Valid(b), Validated::Valid(c)) => {
                Validated::Valid(f(a, b, c))
            }
            // Cases where at least one value is invalid
            _ => {
                // Collect all errors
                let mut errors = SmallVec::<[E; 4]>::new();
                let mut has_errors = false;

                if let Validated::SingleInvalid(e) = self {
                    has_errors = true;
                    errors.push(e.clone());
                } else if let Validated::MultiInvalid(es) = self {
                    has_errors = true;
                    errors.extend(es.iter().cloned());
                }

                if let Validated::SingleInvalid(e) = rb {
                    has_errors = true;
                    errors.push(e.clone());
                } else if let Validated::MultiInvalid(es) = rb {
                    has_errors = true;
                    errors.extend(es.iter().cloned());
                }

                if let Validated::SingleInvalid(e) = rc {
                    has_errors = true;
                    errors.push(e.clone());
                } else if let Validated::MultiInvalid(es) = rc {
                    has_errors = true;
                    errors.extend(es.iter().cloned());
                }

                if !has_errors {
                    // This shouldn't happen with the match pattern above
                    unreachable!("No errors found in invalid Validated")
                } else if errors.len() == 1 {
                    Validated::SingleInvalid(errors.pop().unwrap())
                } else {
                    Validated::MultiInvalid(errors)
                }
            }
        }
    }

    #[inline]
    fn lift3_owned<B, C, D, F>(
        self,
        rb: Self::Output<B>,
        rc: Self::Output<C>,
        f: F,
    ) -> Self::Output<D>
    where
        Self: Sized,
        F: FnOnce(Self::Source, B, C) -> D,
        B: Clone,
        C: Clone,
        D: Clone,
    {
        // Avoid borrowing moved values by handling each case separately
        match (self, rb, rc) {
            (Validated::Valid(a), Validated::Valid(b), Validated::Valid(c)) => {
                Validated::Valid(f(a, b, c))
            }
            (Validated::SingleInvalid(e), Validated::Valid(_), Validated::Valid(_)) => {
                Validated::SingleInvalid(e)
            }
            (Validated::Valid(_), Validated::SingleInvalid(e), Validated::Valid(_)) => {
                Validated::SingleInvalid(e)
            }
            (Validated::Valid(_), Validated::Valid(_), Validated::SingleInvalid(e)) => {
                Validated::SingleInvalid(e)
            }
            (Validated::MultiInvalid(e1), Validated::Valid(_), Validated::Valid(_)) => {
                Validated::MultiInvalid(e1)
            }
            (Validated::Valid(_), Validated::MultiInvalid(e2), Validated::Valid(_)) => {
                Validated::MultiInvalid(e2)
            }
            (Validated::Valid(_), Validated::Valid(_), Validated::MultiInvalid(e3)) => {
                Validated::MultiInvalid(e3)
            }
            // Combinations with more than one invalid
            (Validated::SingleInvalid(e1), Validated::SingleInvalid(e2), Validated::Valid(_)) => {
                let mut errors = SmallVec::<[E; 4]>::with_capacity(2);
                errors.push(e1);
                errors.push(e2);
                Validated::MultiInvalid(errors)
            }
            (Validated::SingleInvalid(e1), Validated::Valid(_), Validated::SingleInvalid(e2)) => {
                let mut errors = SmallVec::<[E; 4]>::with_capacity(2);
                errors.push(e1);
                errors.push(e2);
                Validated::MultiInvalid(errors)
            }
            (Validated::Valid(_), Validated::SingleInvalid(e1), Validated::SingleInvalid(e2)) => {
                let mut errors = SmallVec::<[E; 4]>::with_capacity(2);
                errors.push(e1);
                errors.push(e2);
                Validated::MultiInvalid(errors)
            }
            // Handle cases with MultiInvalid
            (a, b, c) => {
                let mut errors = SmallVec::<[E; 4]>::new();
                match a {
                    Validated::SingleInvalid(e) => errors.push(e),
                    Validated::MultiInvalid(e) => errors.extend(e),
                    _ => {}
                }
                match b {
                    Validated::SingleInvalid(e) => errors.push(e),
                    Validated::MultiInvalid(e) => errors.extend(e),
                    _ => {}
                }
                match c {
                    Validated::SingleInvalid(e) => errors.push(e),
                    Validated::MultiInvalid(e) => errors.extend(e),
                    _ => {}
                }

                if errors.is_empty() {
                    unreachable!("This should never happen given the pattern matches above")
                } else if errors.len() == 1 {
                    Validated::SingleInvalid(errors.pop().unwrap())
                } else {
                    Validated::MultiInvalid(errors)
                }
            }
        }
    }
}

impl<E: Clone, A: Clone> Monad for Validated<E, A> {
    /// Bind operation for Validated, also known as flatMap.
    ///
    /// This is the Monad's bind operation, which applies a function to a value inside a Validated
    /// and flattens the result.
    ///
    /// # Type Parameters
    ///
    /// * `U`: The result type of the binding function
    /// * `F`: The type of the binding function
    ///
    /// # Arguments
    ///
    /// * `f` - Function to apply to the value inside the Validated
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::validated::Validated;
    /// use rustica::traits::monad::Monad;
    ///
    /// let valid: Validated<&str, i32> = Validated::valid(42);
    /// let result = valid.bind(&|x| Validated::<&str, String>::valid(x.to_string()));
    /// assert_eq!(result, Validated::valid("42".to_string()));
    /// ```
    #[inline]
    fn bind<U, F>(&self, f: F) -> Self::Output<U>
    where
        U: Clone,
        F: Fn(&Self::Source) -> Self::Output<U>,
    {
        match self {
            Validated::Valid(a) => f(a),
            Validated::SingleInvalid(e) => Validated::SingleInvalid(e.clone()),
            Validated::MultiInvalid(e) => Validated::MultiInvalid(e.clone()),
        }
    }

    /// Join operation for nested Validated values.
    ///
    /// This flattens a nested Validated structure.
    ///
    /// # Type Parameters
    ///
    /// * `U`: The inner value type
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::validated::Validated;
    /// use rustica::traits::monad::Monad;
    ///
    /// let nested: Validated<&str, Validated<&str, i32>> = Validated::valid(Validated::valid(42));
    /// let flattened = nested.join();
    /// assert_eq!(flattened, Validated::valid(42));
    /// ```
    #[inline]
    fn join<U>(&self) -> Self::Output<U>
    where
        Self::Source: Clone + Into<Self::Output<U>>,
        U: Clone,
        E: Clone,
    {
        match self {
            Validated::Valid(inner) => inner.clone().into(),
            Validated::SingleInvalid(e) => Validated::SingleInvalid(e.clone()),
            Validated::MultiInvalid(e) => Validated::MultiInvalid(e.clone()),
        }
    }

    /// Bind operation for Validated taking ownership, also known as flatMap.
    ///
    /// This is the owned version of the bind operation, which applies a function to a value inside
    /// a Validated and flattens the result, taking ownership of the original Validated.
    ///
    /// # Performance
    ///
    /// This method avoids cloning error values, making it more efficient than `bind` when you
    /// have ownership of the Validated value.
    ///
    /// # Type Parameters
    ///
    /// * `U`: The result type of the binding function
    /// * `F`: The type of the binding function
    ///
    /// # Arguments
    ///
    /// * `f` - Function to apply to the value inside the Validated
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::validated::Validated;
    /// use rustica::traits::monad::Monad;
    ///
    /// let valid: Validated<String, i32> = Validated::valid(42);
    /// let result = valid.bind_owned(|x| Validated::<String, String>::valid(x.to_string()));
    /// assert_eq!(result, Validated::valid("42".to_string()));
    /// ```
    #[inline]
    fn bind_owned<U, F>(self, f: F) -> Self::Output<U>
    where
        U: Clone,
        F: FnOnce(Self::Source) -> Self::Output<U>,
    {
        match self {
            Validated::Valid(a) => f(a),
            Validated::SingleInvalid(e) => Validated::SingleInvalid(e),
            Validated::MultiInvalid(e) => Validated::MultiInvalid(e),
        }
    }

    /// Join operation for nested Validated values, taking ownership.
    ///
    /// This flattens a nested Validated structure, taking ownership of the original Validated.
    ///
    /// # Performance
    ///
    /// This method avoids cloning error values, making it more efficient than `join` when you
    /// have ownership of the Validated value.
    ///
    /// # Type Parameters
    ///
    /// * `U`: The inner value type
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::validated::Validated;
    /// use rustica::traits::monad::Monad;
    ///
    /// let nested: Validated<String, Validated<String, i32>> =
    ///     Validated::valid(Validated::valid(42));
    /// let flattened = nested.join_owned();
    /// assert_eq!(flattened, Validated::valid(42));
    /// ```
    #[inline]
    fn join_owned<U>(self) -> Self::Output<U>
    where
        Self::Source: Into<Self::Output<U>>,
    {
        match self {
            Validated::Valid(inner) => inner.into(),
            Validated::SingleInvalid(e) => Validated::SingleInvalid(e),
            Validated::MultiInvalid(e) => Validated::MultiInvalid(e),
        }
    }
}

impl<E, A> Identity for Validated<E, A> {
    /// Returns a reference to the inner value.
    ///
    /// # Panics
    ///
    /// Panics if the Validated is invalid.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::validated::Validated;
    /// use rustica::traits::identity::Identity;
    ///
    /// let valid: Validated<&str, i32> = Validated::valid(42);
    /// assert_eq!(*valid.value(), 42);
    /// ```
    #[inline]
    fn value(&self) -> &Self::Source {
        match self {
            Validated::Valid(a) => a,
            _ => panic!("Cannot extract value from invalid Validated"),
        }
    }

    /// Creates a pure value.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::validated::Validated;
    /// use rustica::traits::identity::Identity;
    ///
    /// let valid: Validated<&str, i32> = Validated::pure_identity(42);
    /// assert_eq!(valid, Validated::valid(42));
    /// ```
    #[inline]
    fn pure_identity<B>(value: B) -> Self::Output<B> {
        Validated::Valid(value)
    }

    /// Unwraps the Validated, returning the contained value.
    ///
    /// # Panics
    ///
    /// Panics if the Validated is invalid.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::validated::Validated;
    /// use rustica::traits::identity::Identity;
    ///
    /// let valid: Validated<&str, i32> = Validated::valid(42);
    /// assert_eq!(valid.into_value(), 42);
    /// ```
    #[inline]
    fn into_value(self) -> Self::Source {
        match self {
            Validated::Valid(x) => x,
            _ => panic!("Cannot extract value from invalid Validated"),
        }
    }
}

impl<E, A> Validated<E, A> {
    /// Returns whether this `Validated` is valid.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::validated::Validated;
    ///
    /// let valid: Validated<&str, i32> = Validated::valid(42);
    /// assert!(valid.is_valid());
    ///
    /// let invalid: Validated<&str, i32> = Validated::invalid("error");
    /// assert!(!invalid.is_valid());
    /// ```
    #[inline]
    pub fn is_valid(&self) -> bool {
        matches!(self, Validated::Valid(_))
    }

    /// Returns whether this `Validated` is invalid.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::validated::Validated;
    ///
    /// let valid: Validated<&str, i32> = Validated::valid(42);
    /// assert!(!valid.is_invalid());
    ///
    /// let invalid: Validated<&str, i32> = Validated::invalid("error");
    /// assert!(invalid.is_invalid());
    /// ```
    #[inline]
    pub fn is_invalid(&self) -> bool {
        !self.is_valid()
    }

    /// Returns all errors if this is invalid, or an empty collection if valid.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::validated::Validated;
    /// use smallvec::SmallVec;
    ///
    /// let valid: Validated<&str, i32> = Validated::valid(42);
    /// let errors = valid.errors();
    /// assert!(errors.is_empty());
    ///
    /// let invalid: Validated<&str, i32> = Validated::invalid("error");
    /// let errors = invalid.errors();
    /// assert_eq!(errors.len(), 1);
    /// assert_eq!(errors[0], "error");
    /// ```
    #[inline]
    pub fn errors(&self) -> SmallVec<[E; 4]>
    where
        E: Clone,
    {
        match self {
            Validated::Valid(_) => SmallVec::new(),
            Validated::SingleInvalid(e) => {
                let mut errors = SmallVec::new();
                errors.push(e.clone());
                errors
            }
            Validated::MultiInvalid(e) => e.clone(),
        }
    }
}

impl<E, A> Composable for Validated<E, A> {}

impl<E, A> Foldable for Validated<E, A> {
    #[inline]
    fn fold_left<U, F>(&self, init: &U, f: F) -> U
    where
        F: Fn(&U, &Self::Source) -> U,
        U: Clone,
    {
        match self {
            Validated::Valid(a) => f(init, a),
            _ => init.clone(),
        }
    }

    #[inline]
    fn fold_right<U, F>(&self, init: &U, f: F) -> U
    where
        F: Fn(&Self::Source, &U) -> U,
        U: Clone,
    {
        match self {
            Validated::Valid(a) => f(a, init),
            _ => init.clone(),
        }
    }
}
