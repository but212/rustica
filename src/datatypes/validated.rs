//! # Validated Datatype
//!
//! The `Validated` datatype represents a validation result that can either be valid with a value
//! or invalid with a collection of errors. Unlike `Result`, which fails fast on the first error,
//! `Validated` can accumulate multiple errors during validation.
//!
//! ## Examples
//!
//! ```rust
//! use rustica::datatypes::validated::Validated;
//!
//! let valid: Validated<&str, i32> = Validated::valid(42);
//! assert!(valid.is_valid());
//!
//! let invalid: Validated<&str, i32> = Validated::invalid("error");
//! assert!(invalid.is_invalid());
//! ```
//!
//! ```rust
//! use rustica::datatypes::validated::Validated;
//!
//! let result: Result<i32, &str> = Ok(42);
//! let validated = Validated::from_result(&result);
//! assert_eq!(validated, Validated::valid(42));
//!
//! let error_result: Result<i32, &str> = Err("error");
//! let validated = Validated::from_result(&error_result);
//! assert_eq!(validated, Validated::invalid("error"));
//! ```
//!
//! ```rust
//! use rustica::datatypes::validated::Validated;
//!
//! let some_value: Option<i32> = Some(42);
//! let validated: Validated<&str, i32> = Validated::from_option(&some_value, &"missing value");
//! assert_eq!(validated, Validated::valid(42));
//!
//! let none_value: Option<i32> = None;
//! let validated: Validated<&str, i32> = Validated::from_option(&none_value, &"missing value");
//! assert_eq!(validated, Validated::invalid("missing value"));
//! ```
//!
//! ```rust
//! use rustica::datatypes::validated::Validated;
//!
//! let values = vec![
//!     Validated::<&str, i32>::valid(1),
//!     Validated::<&str, i32>::valid(2),
//!     Validated::<&str, i32>::valid(3),
//! ];
//! let collected: Validated<&str, Vec<i32>> = Validated::collect(values.iter().cloned());
//! assert_eq!(collected, Validated::valid(vec![1, 2, 3]));
//!
//! let mixed = vec![
//!     Validated::<&str, i32>::valid(1),
//!     Validated::<&str, i32>::invalid("error"),
//!     Validated::<&str, i32>::valid(3),
//! ];
//! let collected: Validated<&str, Vec<i32>> = Validated::collect(mixed.iter().cloned());
//! assert!(collected.is_invalid());
//! ```
//!
//! ```rust
//! use rustica::datatypes::validated::Validated;
//!
//! let invalid: Validated<&str, i32> = Validated::invalid("error");
//! let mapped = invalid.fmap_invalid(|e| format!("Error: {}", e));
//! assert_eq!(mapped, Validated::invalid("Error: error".to_string()));
//! ```
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
use crate::traits::alternative::Alternative;
use crate::traits::applicative::Applicative;
use crate::traits::bifunctor::Bifunctor;
use crate::traits::composable::Composable;
use crate::traits::foldable::Foldable;
use crate::traits::functor::Functor;
use crate::traits::hkt::{BinaryHKT, HKT};
use crate::traits::identity::Identity;
use crate::traits::monad::Monad;
use crate::traits::monad_plus::MonadPlus;
use crate::traits::pure::Pure;
use smallvec::{smallvec, SmallVec};

/// A validation type that can accumulate multiple errors.
///
/// Validated<E, A> represents either a valid value of type A or a collection of
/// errors of type E. Unlike Result, which fails fast on the first error,
/// Validated can collect multiple errors during validation.
///
/// # Performance Optimization
///
/// Validated uses SmallVec<[E; 4]> internally to store errors, which optimizes for
/// the common case of having 1-4 validation errors without requiring heap allocation.
#[derive(Clone, PartialEq, PartialOrd, Eq, Ord, Debug, Hash)]
pub enum Validated<E, A> {
    /// Represents a valid value of type A.
    Valid(A),
    /// Represents an invalid state with multiple errors of type E.
    /// Uses SmallVec for better performance with small error counts.
    Invalid(SmallVec<[E; 4]>),
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
    pub fn errors(&self) -> Vec<E>
    where
        E: Clone,
    {
        match self {
            Validated::Valid(_) => Vec::new(),
            Validated::Invalid(e) => e.clone().to_vec(),
        }
    }
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
        Validated::Invalid(smallvec![e])
    }

    /// Creates a new invalid instance with multiple errors from a collection.
    ///
    /// Unlike `invalid_vec`, this method always creates an `Invalid` variant,
    /// even if there are zero or one errors in the collection.
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
    /// let invalid: Validated<&str, ()> = Validated::invalid_many(vec!["error1", "error2"]);
    /// ```
    #[inline]
    pub fn invalid_many<I>(errors: I) -> Self
    where
        I: IntoIterator<Item = E>,
    {
        Validated::Invalid(errors.into_iter().collect())
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
        let mut errors = errors.into_iter();
        if let Some(first) = errors.next() {
            let mut vec = smallvec![first];
            vec.extend(errors);
            Validated::Invalid(vec)
        } else {
            panic!("Validated::invalid_vec requires at least one error")
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
    /// let mapped = invalid.fmap_invalid(|e| format!("Error: {}", e));
    /// assert_eq!(mapped, Validated::invalid("Error: error".to_string()));
    /// ```
    #[inline]
    pub fn fmap_invalid<G, F>(&self, f: F) -> Validated<G, A>
    where
        F: Fn(&E) -> G,
        G: Clone,
    {
        match self {
            Validated::Valid(x) => Validated::Valid(x.clone()),
            Validated::Invalid(es) => {
                let transformed = es.iter().map(f).collect();
                Validated::Invalid(transformed)
            },
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
    /// let mapped = invalid.fmap_invalid_owned(|e| format!("Error: {}", e));
    /// assert_eq!(mapped, Validated::invalid("Error: error".to_string()));
    /// ```
    #[inline]
    pub fn fmap_invalid_owned<G, F>(self, f: F) -> Validated<G, A>
    where
        F: Fn(E) -> G,
        G: Clone,
    {
        match self {
            Validated::Valid(x) => Validated::Valid(x),
            Validated::Invalid(es) => {
                let transformed = es.into_iter().map(f).collect();
                Validated::Invalid(transformed)
            },
        }
    }

    /// Combines errors from two Validated values.
    ///
    /// This is used internally to combine errors when both values are invalid.
    /// The function assumes at least one of the values is invalid.
    ///
    /// # Arguments
    ///
    /// * `other` - Another Validated instance to combine errors with
    ///
    /// # Panics
    ///
    /// Panics if both values are valid, as this function should only be called when
    /// at least one value is invalid.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::validated::Validated;
    ///
    /// let v1: Validated<&str, i32> = Validated::invalid("error 1");
    /// let v2: Validated<&str, i32> = Validated::invalid("error 2");
    /// let combined = v1.combine_errors(&v2);
    ///
    /// // The result contains both errors
    /// let errors = combined.errors();
    /// assert_eq!(errors.len(), 2);
    /// assert!(errors.contains(&"error 1"));
    /// assert!(errors.contains(&"error 2"));
    /// ```
    pub fn combine_errors(&self, other: &Self) -> Self {
        match (self, other) {
            (Validated::Valid(_), Validated::Valid(_)) => unreachable!(),
            (Validated::Valid(_), invalid) => invalid.clone(),
            (invalid, Validated::Valid(_)) => invalid.clone(),
            (Validated::Invalid(es1), Validated::Invalid(es2)) => {
                let errors = es1.iter().chain(es2.iter()).cloned().collect::<SmallVec<[E; 4]>>();
                Validated::Invalid(errors)
            },
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
    pub fn from_result(result: &Result<A, E>) -> Validated<E, A>
    where
        A: Clone,
        E: Clone,
    {
        use crate::utils::error_utils::ResultExt;
        result.clone().to_validated()
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
        use crate::utils::error_utils::ResultExt;
        result.to_validated()
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
    pub fn to_result(&self) -> Result<A, E>
    where
        A: Clone,
        E: Clone,
    {
        use crate::utils::error_utils::WithError;
        self.clone().to_result()
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
    pub fn to_result_owned(self) -> Result<A, E> {
        use crate::utils::error_utils::WithError;
        self.to_result()
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
            None => Validated::Invalid(smallvec![error.clone()]),
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
            None => Validated::Invalid(smallvec![error]),
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
            None => Validated::Invalid(smallvec![error_fn()]),
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
            None => Validated::Invalid(smallvec![error_fn()]),
        }
    }

    /// Unwraps a valid value or panics.
    ///
    /// If this is valid, returns the valid value.
    /// If this is invalid, panics.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::validated::Validated;
    ///
    /// let valid: Validated<&str, i32> = Validated::valid(42);
    /// assert_eq!(valid.unwrap(), 42);
    /// ```
    ///
    /// # Panics
    ///
    /// Panics if this is invalid.
    #[inline]
    pub fn unwrap(&self) -> A {
        match self {
            Validated::Valid(value) => value.clone(),
            _ => panic!("Cannot unwrap invalid value"),
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

    /// Unwraps a valid value or panics.
    ///
    /// If this is valid, returns the valid value.
    /// If this is invalid, panics with a message.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::validated::Validated;
    ///
    /// let invalid: Validated<&str, i32> = Validated::invalid("error");
    /// assert_eq!(invalid.unwrap_invalid() , vec!["error"]);
    /// ```
    ///
    /// # Panics
    ///
    /// Panics if this is invalid.
    #[inline]
    pub fn unwrap_invalid(&self) -> Vec<E> {
        match self {
            Validated::Invalid(es) => es.to_vec(),
            _ => panic!("Cannot unwrap invalid value"),
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
        // Early check for empty slice
        if values.is_empty() {
            return Validated::Valid(f(&[]));
        }

        // First pass to check if all are valid (fast path)
        if values.iter().all(|v| matches!(v, Validated::Valid(_))) {
            let valid_values: Vec<A> = values
                .iter()
                .filter_map(|v| match v {
                    Validated::Valid(x) => Some(x.clone()),
                    _ => None,
                })
                .collect();
            return Validated::Valid(f(&valid_values));
        }

        // Collect errors
        let mut errors = SmallVec::<[E; 4]>::new();
        for v in values {
            if let Validated::Invalid(es) = v {
                errors.extend(es.iter().cloned());
            }
        }

        Validated::Invalid(errors)
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
    /// let collected: Validated<&str, Vec<i32>> = Validated::collect(values.iter().cloned());
    /// assert_eq!(collected, Validated::valid(vec![1, 2, 3]));
    ///
    /// let mixed = vec![
    ///     Validated::<&str, i32>::valid(1),
    ///     Validated::<&str, i32>::invalid("error"),
    ///     Validated::<&str, i32>::valid(3),
    /// ];
    ///
    /// let collected: Validated<&str, Vec<i32>> = Validated::collect(mixed.iter().cloned());
    /// assert!(collected.is_invalid());
    /// ```
    #[inline]
    pub fn collect<I, C>(iter: I) -> Validated<E, C>
    where
        I: Iterator<Item = Validated<E, A>>,
        C: FromIterator<A> + Clone,
        A: Clone,
        E: Clone,
    {
        let mut values = Vec::new();
        let mut errors = smallvec![];
        for v in iter {
            match v {
                Validated::Valid(a) => values.push(a),
                Validated::Invalid(es) => errors.extend(es),
            }
        }
        if errors.is_empty() {
            Validated::Valid(C::from_iter(values))
        } else {
            Validated::Invalid(errors)
        }
    }

    #[inline]
    pub fn to_option(&self) -> Option<A> {
        match self {
            Validated::Valid(x) => Some(x.clone()),
            _ => None,
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
    /// let mapped = valid.fmap_valid_async(|x| async move { x * 2 }).await;
    /// assert_eq!(mapped, Validated::valid(84));
    /// # }
    /// ```
    #[inline]
    pub async fn fmap_valid_async<B, F, Fut>(&self, f: F) -> Validated<E, B>
    where
        F: Fn(A) -> Fut + Send + 'static,
        Fut: std::future::Future<Output = B> + Send,
        B: Clone + Send + 'static,
    {
        match self {
            Validated::Valid(x) => {
                let result = f(x.clone()).await;
                Validated::Valid(result)
            },
            Validated::Invalid(e) => Validated::Invalid(e.clone()),
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
    /// let mapped = invalid.fmap_invalid_async(|e| async move { format!("Error: {}", e) }).await;
    /// assert_eq!(mapped, Validated::invalid("Error: error".to_string()));
    /// # }
    /// ```
    #[inline]
    pub async fn fmap_invalid_async<G, F, Fut>(&self, f: F) -> Validated<G, A>
    where
        F: Fn(E) -> Fut + Send + 'static + Clone,
        Fut: std::future::Future<Output = G> + Send,
        G: Clone + Send + 'static,
    {
        match self {
            Validated::Valid(x) => Validated::Valid(x.clone()),
            Validated::Invalid(es) => {
                // Using futures::future::join_all to run all futures concurrently
                let futures = es.iter().map(|e| f(e.clone()));
                let results = futures::future::join_all(futures).await;
                let transformed: SmallVec<[G; 4]> = results.into_iter().collect();

                Validated::Invalid(transformed)
            },
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
            Validated::Invalid(e) => Validated::Invalid(e.clone()),
        }
    }

    /// Returns an iterator over the valid value (0 or 1 item).
    pub fn iter(&self) -> Iter<'_, A> {
        match self {
            Validated::Valid(ref a) => Iter { inner: Some(a) },
            _ => Iter { inner: None },
        }
    }

    /// Returns a mutable iterator over the valid value (0 or 1 item).
    pub fn iter_mut(&mut self) -> IterMut<'_, A> {
        match self {
            Validated::Valid(ref mut a) => IterMut { inner: Some(a) },
            _ => IterMut { inner: None },
        }
    }

    /// Returns an iterator over the error(s) (0 or many).
    pub fn iter_errors(&self) -> ErrorsIter<'_, E> {
        match self {
            Validated::Invalid(ref es) => ErrorsIter::Multi(es.iter()),
            _ => ErrorsIter::Empty,
        }
    }

    /// Returns a mutable iterator over the error(s) (0 or many).
    pub fn iter_errors_mut(&mut self) -> ErrorsIterMut<'_, E> {
        match self {
            Validated::Invalid(ref mut es) => ErrorsIterMut::Multi(es.iter_mut()),
            _ => ErrorsIterMut::Empty,
        }
    }
}

/// Iterator over a Validated value (0 or 1 item)
pub struct Iter<'a, A> {
    inner: Option<&'a A>,
}

impl<'a, A> Iterator for Iter<'a, A> {
    type Item = &'a A;

    fn next(&mut self) -> Option<Self::Item> {
        self.inner.take()
    }
}

/// Mutable iterator over a Validated value (0 or 1 item)
pub struct IterMut<'a, A> {
    inner: Option<&'a mut A>,
}

impl<'a, A> Iterator for IterMut<'a, A> {
    type Item = &'a mut A;

    fn next(&mut self) -> Option<Self::Item> {
        self.inner.take()
    }
}

/// Iterator over errors in a Validated
pub enum ErrorsIter<'a, E> {
    Empty,
    Multi(smallvec::alloc::slice::Iter<'a, E>),
}

impl<'a, E> Iterator for ErrorsIter<'a, E> {
    type Item = &'a E;

    fn next(&mut self) -> Option<Self::Item> {
        match self {
            ErrorsIter::Empty => None,
            ErrorsIter::Multi(ref mut it) => it.next(),
        }
    }
}

/// Mutable iterator over errors in a Validated
pub enum ErrorsIterMut<'a, E> {
    Empty,
    Multi(smallvec::alloc::slice::IterMut<'a, E>),
}

impl<'a, E> Iterator for ErrorsIterMut<'a, E> {
    type Item = &'a mut E;

    fn next(&mut self) -> Option<Self::Item> {
        match self {
            ErrorsIterMut::Empty => None,
            ErrorsIterMut::Multi(ref mut it) => it.next(),
        }
    }
}

impl<E, A> IntoIterator for Validated<E, A> {
    type Item = A;
    type IntoIter = IntoIter<A>;

    fn into_iter(self) -> Self::IntoIter {
        match self {
            Validated::Valid(a) => IntoIter { inner: Some(a) },
            _ => IntoIter { inner: None },
        }
    }
}

pub struct IntoIter<A> {
    inner: Option<A>,
}

impl<A> Iterator for IntoIter<A> {
    type Item = A;

    fn next(&mut self) -> Option<Self::Item> {
        self.inner.take()
    }
}

impl<'a, E: Clone, A: Clone> IntoIterator for &'a Validated<E, A> {
    type Item = &'a A;
    type IntoIter = Iter<'a, A>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<'a, E: Clone, A: Clone> IntoIterator for &'a mut Validated<E, A> {
    type Item = &'a mut A;
    type IntoIter = IterMut<'a, A>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter_mut()
    }
}

impl<E, A> HKT for Validated<E, A> {
    type Source = A;
    type Output<T> = Validated<E, T>;
}

impl<E: Clone, A> Pure for Validated<E, A> {
    #[inline]
    fn pure<T: Clone>(x: &T) -> Self::Output<T> {
        Validated::Valid(x.clone())
    }

    #[inline]
    fn pure_owned<T: Clone>(x: T) -> Self::Output<T> {
        Validated::Valid(x)
    }
}

impl<E: Clone, A: Clone> Functor for Validated<E, A> {
    #[inline]
    fn fmap<B, F>(&self, f: F) -> Self::Output<B>
    where
        F: Fn(&Self::Source) -> B,
        B: Clone,
    {
        match self {
            Validated::Valid(x) => Validated::Valid(f(x)),
            Validated::Invalid(e) => Validated::Invalid(e.clone()),
        }
    }

    #[inline]
    fn fmap_owned<B, F>(self, f: F) -> Self::Output<B>
    where
        Self: Sized,
        F: FnOnce(Self::Source) -> B,
    {
        match self {
            Validated::Valid(x) => Validated::Valid(f(x)),
            Validated::Invalid(e) => Validated::Invalid(e),
        }
    }
}

impl<E, A> BinaryHKT for Validated<E, A> {
    type Source2 = E;
    type BinaryOutput<U, V> = Validated<V, U>;

    fn map_second<F, C>(&self, f: F) -> Self::BinaryOutput<A, C>
    where
        F: Fn(&Self::Source2) -> C,
        Self::Source: Clone,
        Self::Source2: Clone,
        C: Clone,
    {
        match self {
            Validated::Valid(x) => Validated::Valid(x.clone()),
            Validated::Invalid(es) => {
                let transformed: SmallVec<[C; 4]> = es.iter().map(f).collect();
                Validated::Invalid(transformed)
            },
        }
    }

    fn map_second_owned<F, C>(self, f: F) -> Self::BinaryOutput<A, C>
    where
        F: Fn(Self::Source2) -> C,
        C: Clone,
    {
        match self {
            Validated::Valid(x) => Validated::Valid(x),
            Validated::Invalid(es) => {
                let transformed: SmallVec<[C; 4]> = es.into_iter().map(f).collect();
                Validated::Invalid(transformed)
            },
        }
    }
}

impl<E: Clone, A: Clone> Bifunctor for Validated<E, A> {
    fn bimap<C, D, F, G>(&self, f: F, g: G) -> Self::BinaryOutput<C, D>
    where
        F: Fn(&Self::Source) -> C,
        G: Fn(&Self::Source2) -> D,
        C: Clone,
        D: Clone,
    {
        match self {
            Validated::Valid(x) => Validated::Valid(f(x)),
            Validated::Invalid(es) => {
                let transformed: SmallVec<[D; 4]> = es.iter().map(g).collect();
                Validated::Invalid(transformed)
            },
        }
    }

    fn first<C, F>(&self, f: F) -> Self::BinaryOutput<C, Self::Source2>
    where
        F: Fn(&Self::Source) -> C,
        C: Clone,
    {
        match self {
            Validated::Valid(x) => Validated::Valid(f(x)),
            Validated::Invalid(e) => Validated::Invalid(e.clone()),
        }
    }

    fn second<D, G>(&self, g: G) -> Self::BinaryOutput<Self::Source, D>
    where
        G: Fn(&Self::Source2) -> D,
        D: Clone,
    {
        match self {
            Validated::Valid(x) => Validated::Valid(x.clone()),
            Validated::Invalid(es) => {
                let transformed: SmallVec<[D; 4]> = es.iter().map(g).collect();
                Validated::Invalid(transformed)
            },
        }
    }
}

impl<E: Clone, A: Clone> Applicative for Validated<E, A> {
    fn apply<B, F>(&self, rf: &Self::Output<F>) -> Self::Output<B>
    where
        F: Fn(&Self::Source) -> B,
        B: Clone,
    {
        match (self, rf) {
            (Validated::Valid(a), Validated::Valid(f)) => Validated::Valid(f(a)),
            (Validated::Valid(_), Validated::Invalid(e)) => Validated::Invalid(e.clone()),
            (Validated::Invalid(e), Validated::Valid(_)) => Validated::Invalid(e.clone()),
            (Validated::Invalid(e1), Validated::Invalid(e2)) => {
                let mut errors = SmallVec::<[E; 4]>::with_capacity(e1.len() + e2.len());
                errors.extend(e1.iter().cloned().chain(e2.iter().cloned()));
                Validated::Invalid(errors)
            },
        }
    }

    fn apply_owned<B, F>(self, rf: Self::Output<F>) -> Self::Output<B>
    where
        Self: Sized,
        F: FnOnce(Self::Source) -> B,
        B: Clone,
    {
        match (self, rf) {
            (Validated::Valid(a), Validated::Valid(f)) => Validated::Valid(f(a)),
            (a, b) => {
                let mut errors = SmallVec::<[E; 4]>::new();

                if let Validated::Invalid(e) = a {
                    errors.extend(e);
                }
                if let Validated::Invalid(e) = b {
                    errors.extend(e);
                }

                Validated::Invalid(errors)
            },
        }
    }

    fn lift2<B, C, F>(&self, rb: &Self::Output<B>, f: F) -> Self::Output<C>
    where
        F: Fn(&Self::Source, &B) -> C,
        B: Clone,
        C: Clone,
    {
        match (self, rb) {
            (Validated::Valid(a), Validated::Valid(b)) => Validated::Valid(f(a, b)),
            _ => {
                let mut errors = SmallVec::<[E; 4]>::new();

                if let Validated::Invalid(es) = self {
                    errors.extend(es.iter().cloned());
                }

                if let Validated::Invalid(es) = rb {
                    errors.extend(es.iter().cloned());
                }

                Validated::Invalid(errors)
            },
        }
    }

    fn lift2_owned<B, C, F>(self, rb: Self::Output<B>, f: F) -> Self::Output<C>
    where
        Self: Sized,
        F: FnOnce(Self::Source, B) -> C,
        B: Clone,
        C: Clone,
    {
        match (self, rb) {
            (Validated::Valid(a), Validated::Valid(b)) => Validated::Valid(f(a, b)),
            (a, b) => {
                let mut errors = SmallVec::<[E; 4]>::new();

                if let Validated::Invalid(e) = a {
                    errors.extend(e);
                }
                if let Validated::Invalid(e) = b {
                    errors.extend(e);
                }

                Validated::Invalid(errors)
            },
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
            },
            _ => {
                let mut errors = SmallVec::<[E; 4]>::new();

                if let Validated::Invalid(es) = self {
                    errors.extend(es.iter().cloned());
                }
                if let Validated::Invalid(es) = rb {
                    errors.extend(es.iter().cloned());
                }
                if let Validated::Invalid(es) = rc {
                    errors.extend(es.iter().cloned());
                }

                Validated::Invalid(errors)
            },
        }
    }

    fn lift3_owned<B, C, D, F>(
        self, b: Self::Output<B>, c: Self::Output<C>, f: F,
    ) -> Self::Output<D>
    where
        Self: Sized,
        F: FnOnce(Self::Source, B, C) -> D,
        B: Clone,
        C: Clone,
        D: Clone,
    {
        match (self, b, c) {
            (Validated::Valid(a), Validated::Valid(b_val), Validated::Valid(c_val)) => {
                Validated::Valid(f(a, b_val, c_val))
            },
            (Validated::Invalid(e1), Validated::Invalid(e2), Validated::Invalid(e3)) => {
                let mut errors = SmallVec::<[E; 4]>::with_capacity(e1.len() + e2.len() + e3.len());
                errors.extend(e1);
                errors.extend(e2);
                errors.extend(e3);
                Validated::Invalid(errors)
            },
            (a, b, c) => {
                let mut errors = SmallVec::<[E; 4]>::new();

                if let Validated::Invalid(e) = a {
                    errors.extend(e);
                }
                if let Validated::Invalid(e) = b {
                    errors.extend(e);
                }
                if let Validated::Invalid(e) = c {
                    errors.extend(e);
                }

                Validated::Invalid(errors)
            },
        }
    }
}

impl<E: Clone, A: Clone> Monad for Validated<E, A> {
    #[inline]
    fn bind<U, F>(&self, f: F) -> Self::Output<U>
    where
        U: Clone,
        F: Fn(&Self::Source) -> Self::Output<U>,
    {
        match self {
            Validated::Valid(a) => f(a),
            Validated::Invalid(e) => Validated::Invalid(e.clone()),
        }
    }

    #[inline]
    fn join<U>(&self) -> Self::Output<U>
    where
        Self::Source: Clone + Into<Self::Output<U>>,
        U: Clone,
        E: Clone,
    {
        match self {
            Validated::Valid(inner) => inner.clone().into(),
            Validated::Invalid(e) => Validated::Invalid(e.clone()),
        }
    }

    #[inline]
    fn bind_owned<U, F>(self, f: F) -> Self::Output<U>
    where
        U: Clone,
        F: FnOnce(Self::Source) -> Self::Output<U>,
    {
        match self {
            Validated::Valid(a) => f(a),
            Validated::Invalid(e) => Validated::Invalid(e),
        }
    }

    #[inline]
    fn join_owned<U>(self) -> Self::Output<U>
    where
        Self::Source: Into<Self::Output<U>>,
    {
        match self {
            Validated::Valid(inner) => inner.into(),
            Validated::Invalid(e) => Validated::Invalid(e),
        }
    }
}

impl<E, A> Identity for Validated<E, A> {
    #[inline]
    fn value(&self) -> &Self::Source {
        match self {
            Validated::Valid(a) => a,
            _ => panic!("Cannot extract value from invalid Validated"),
        }
    }

    #[inline]
    fn pure_identity<B>(value: B) -> Self::Output<B> {
        Validated::Valid(value)
    }

    #[inline]
    fn into_value(self) -> Self::Source {
        match self {
            Validated::Valid(x) => x,
            _ => panic!("Cannot extract value from invalid Validated"),
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

impl<E: Clone + Default, A: Clone> Alternative for Validated<E, A> {
    fn empty_alt<B: Clone>() -> Self::Output<B> {
        Validated::invalid(E::default())
    }

    fn alt(&self, other: &Self) -> Self {
        match self {
            Validated::Valid(_) => self.clone(),
            Validated::Invalid(_) => other.clone(),
        }
    }

    fn guard(condition: bool) -> Self::Output<()> {
        if condition {
            Validated::valid(())
        } else {
            Validated::invalid(E::default())
        }
    }

    fn many(&self) -> Self::Output<Vec<Self::Source>>
    where
        Self::Source: Clone,
    {
        match self {
            Validated::Valid(x) => Validated::valid(vec![x.clone()]),
            Validated::Invalid(_) => Validated::invalid(E::default()),
        }
    }
}

impl<E: Clone, A: Clone> MonadPlus for Validated<E, A> {
    fn mzero<U: Clone>() -> Self::Output<U> {
        Validated::invalid_vec(Vec::new())
    }

    fn mplus(&self, other: &Self) -> Self {
        match (self, other) {
            (Validated::Valid(_), _) => self.clone(),
            (Validated::Invalid(_), Validated::Valid(_)) => other.clone(),
            (Validated::Invalid(e1), Validated::Invalid(e2)) => {
                let mut errors = SmallVec::<[E; 4]>::with_capacity(e1.len() + e2.len());
                errors.extend(e1.iter().cloned());
                errors.extend(e2.iter().cloned());
                Validated::Invalid(errors)
            },
        }
    }

    fn mplus_owned(self, other: Self) -> Self
    where
        Self: Sized,
    {
        match (&self, &other) {
            (Validated::Valid(_), _) => self,
            (Validated::Invalid(_), Validated::Valid(_)) => other,
            (Validated::Invalid(e1), Validated::Invalid(e2)) => {
                let mut errors = SmallVec::<[E; 4]>::with_capacity(e1.len() + e2.len());
                errors.extend(e1.iter().cloned());
                errors.extend(e2.iter().cloned());
                Validated::Invalid(errors)
            },
        }
    }
}
