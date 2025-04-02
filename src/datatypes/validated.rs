//! # Validated Datatype - PersistentVector Optimized
//!
//! The `Validated<E, A>` datatype represents a validation result that can either be:
//! - `Valid(A)`: Contains a valid value of type A
//! - `Invalid(PersistentVector<E>)`: Contains a collection of errors of type E
//!
//! Unlike `Result`, which fails fast on the first error, `Validated` can accumulate multiple errors
//! during validation, making it ideal for form validation and data processing pipelines.
//!
//! ## Features
//!
//! - **Error Accumulation**: Collects multiple validation errors rather than stopping at the first
//! - **Applicative Interface**: Apply functions to valid values while collecting errors
//! - **Monadic Operations**: Chain dependent validations with appropriate error handling
//! - **Efficient PersistentVector Backend**: Optimized for memory usage and performance
//!
//! ## Implementation Details
//!
//! This implementation leverages `PersistentVector` for efficient error collection:
//! - Structural sharing minimizes memory usage when combining error collections
//! - Specialized methods for owned vs borrowed data to reduce unnecessary cloning
//! - Optimized operations for transforming and combining validation results
//! - Full support for Rustica's functional programming traits
//!
//! ## Usage
//!
//! ```rust
//! use rustica::datatypes::validated::Validated;
//! use rustica::traits::applicative::Applicative;
//!
//! // Create valid and invalid instances
//! let valid = Validated::<&str, i32>::valid(42);
//! let invalid = Validated::<&str, i32>::invalid("Invalid input");
//! let multiple_errors = Validated::<&str, i32>::invalid_many(&["Missing field", "Invalid format"]);
//!
//! // Combine validations using applicative interface
//! let validate_name = |name: &str| -> Validated<&str, String> {
//!     if name.is_empty() {
//!         Validated::invalid("Name cannot be empty")
//!     } else {
//!         Validated::valid(name.to_string())
//!     }
//! };
//!
//! let validate_age = |age: i32| -> Validated<&str, i32> {
//!     if age < 0 || age > 150 {
//!         Validated::invalid("Age must be between 0 and 150")
//!     } else {
//!         Validated::valid(age)
//!     }
//! };
//!
//! // Combine validations to create a Person using a different approach
//! let person = Validated::lift2(
//!     &validate_name("Alice"),
//!     &validate_age(30),
//!     |name, age| format!("{} is {} years old", name, age)
//! );
//!
//! assert!(person.is_valid());
//! ```

use crate::pvec::PersistentVector;
use crate::traits::applicative::Applicative;
use crate::traits::composable::Composable;
use crate::traits::foldable::Foldable;
use crate::traits::functor::Functor;
use crate::traits::hkt::HKT;
use crate::traits::identity::Identity;
use crate::traits::monad::Monad;
use crate::traits::pure::Pure;
use std::borrow::Borrow;

/// A validation type that can accumulate multiple errors.
///
/// `Validated<E, A>` represents either a valid value of type `A` or a collection of
/// errors of type `E`. Unlike `Result`, which fails fast on the first error,
/// `Validated` can collect multiple errors during validation.
///
/// # PersistentVector Optimization
///
/// This implementation uses `PersistentVector<E>` internally to store errors, which provides:
/// - Efficient structural sharing for error accumulation
/// - O(1) append operations
/// - Minimal memory overhead for small error collections
/// - Efficient concatenation through the PersistentVector's optimized implementation
///
/// # Type Parameters
///
/// * `E` - The error type
/// * `A` - The value type
#[derive(Clone, Debug)]
pub enum Validated<E: Clone, A> {
    /// Represents a valid value of type `A`.
    Valid(A),
    /// Represents an invalid state with errors of type `E`.
    /// Uses PersistentVector for efficient error accumulation through structural sharing.
    Invalid(PersistentVector<E>),
}

impl<E: Clone, A> PartialEq for Validated<E, A>
where
    A: PartialEq,
    E: PartialEq,
{
    fn eq(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Valid(a), Self::Valid(b)) => a == b,
            (Self::Invalid(a), Self::Invalid(b)) => {
                // Use iterators to compare elements, avoiding unnecessary cloning
                if a.len() != b.len() {
                    return false;
                }

                a.iter()
                    .zip(b.iter())
                    .all(|(a_elem, b_elem)| a_elem == b_elem)
            }
            _ => false,
        }
    }
}

impl<E: Clone, A> Validated<E, A> {
    /// Returns `true` if this `Validated` is in the `Valid` state, otherwise returns `false`.
    ///
    /// This is useful for conditional logic based on validation state without
    /// extracting the underlying value.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::datatypes::validated::Validated;
    ///
    /// let valid = Validated::<String, i32>::valid(42);
    /// assert!(valid.is_valid());
    ///
    /// let invalid = Validated::<String, i32>::invalid("error".to_string());
    /// assert!(!invalid.is_valid());
    /// ```
    #[inline]
    pub const fn is_valid(&self) -> bool {
        matches!(self, Validated::Valid(_))
    }

    /// Returns `true` if this `Validated` is in the `Invalid` state, otherwise returns `false`.
    ///
    /// This is useful for conditional logic based on validation state without
    /// extracting the underlying error collection.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::datatypes::validated::Validated;
    ///
    /// let valid = Validated::<String, i32>::valid(42);
    /// assert!(!valid.is_invalid());
    ///
    /// let invalid = Validated::<String, i32>::invalid("error".to_string());
    /// assert!(invalid.is_invalid());
    /// ```
    #[inline]
    pub const fn is_invalid(&self) -> bool {
        matches!(self, Validated::Invalid(_))
    }

    /// Returns all errors if this is invalid, or an empty collection if valid.
    ///
    /// Note: This method clones the error values into a Vec. For more efficient
    /// error handling, consider working with the PersistentVector directly
    /// using methods like `with_errors` or `map_errors`.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::datatypes::validated::Validated;
    ///
    /// let valid = Validated::<String, i32>::valid(42);
    /// assert!(valid.errors().is_empty());
    ///
    /// let invalid = Validated::<String, i32>::invalid("error1".to_string());
    /// assert_eq!(invalid.errors(), vec!["error1".to_string()]);
    ///
    /// let invalid = Validated::<String, i32>::invalid_vec(Vec::from(["error1".to_string(), "error2".to_string()]));
    /// assert_eq!(invalid.errors(), vec!["error1".to_string(), "error2".to_string()]);
    /// ```
    #[inline]
    pub fn errors(&self) -> Vec<E>
    where
        E: Clone,
    {
        match self {
            Validated::Valid(_) => Vec::new(),
            Validated::Invalid(e) => e.clone().into(),
        }
    }

    /// Access the underlying PersistentVector of errors if invalid
    ///
    /// This method provides direct access to the error vector without cloning.
    /// Returns None if this Validated is valid.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::datatypes::validated::Validated;
    ///
    /// let valid = Validated::<String, i32>::valid(42);
    /// assert!(valid.error_vector().is_none());
    ///
    /// let invalid = Validated::<String, i32>::invalid("error1".to_string());
    /// assert_eq!(invalid.error_vector(), Some(vec!["error1".to_string()]));
    /// ```
    #[inline]
    pub fn error_vector(&self) -> Option<Vec<E>> {
        match self {
            Validated::Valid(_) => None,
            Validated::Invalid(e) => Some(e.clone().into()),
        }
    }

    /// Returns the number of errors if invalid, or 0 if valid
    ///
    /// This is more efficient than calling `errors().len()` as it doesn't
    /// require cloning the errors into a Vec.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::datatypes::validated::Validated;
    ///
    /// let valid = Validated::<String, i32>::valid(42);
    /// assert_eq!(valid.error_count(), 0);
    ///
    /// let invalid = Validated::<String, i32>::invalid("error1".to_string());
    /// assert_eq!(invalid.error_count(), 1);
    ///
    /// let invalid = Validated::<String, i32>::invalid_vec(vec!["error1".to_string(), "error2".to_string()]);
    /// assert_eq!(invalid.error_count(), 2);
    /// ```
    #[inline]
    pub const fn error_count(&self) -> usize {
        match self {
            Validated::Valid(_) => 0,
            Validated::Invalid(e) => e.len(),
        }
    }

    /// Apply a function to the underlying error vector if invalid
    ///
    /// This method is useful for transforming or processing errors without
    /// extracting them into a new collection.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::datatypes::validated::Validated;
    /// use rustica::pvec::PersistentVector;
    ///
    /// let valid = Validated::<String, i32>::valid(42);
    /// assert_eq!(valid.with_errors(|e| e.is_some()), false);
    ///
    /// let invalid = Validated::<String, i32>::invalid("error1".to_string());
    /// assert_eq!(invalid.with_errors(|e| e.is_some()), true);
    ///
    /// let invalid = Validated::<String, i32>::invalid_vec(vec!["error1".to_string(), "error2".to_string()]);
    /// assert_eq!(invalid.with_errors(|e| e.is_some()), true);
    /// ```
    #[inline]
    pub fn with_errors<F, R>(&self, f: F) -> R
    where
        F: FnOnce(Option<&PersistentVector<E>>) -> R,
    {
        match self {
            Validated::Valid(_) => f(None),
            Validated::Invalid(e) => f(Some(e)),
        }
    }

    /// Creates a new valid instance.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::datatypes::validated::Validated;
    ///
    /// let valid = Validated::<String, i32>::valid(42);
    /// assert!(valid.is_valid());
    /// ```
    #[inline]
    pub const fn valid(x: A) -> Self {
        Validated::Valid(x)
    }

    /// Creates a new invalid instance with a single error.
    ///
    /// This is optimized to create a PersistentVector with just one element,
    /// avoiding unnecessary allocations and copies.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::datatypes::validated::Validated;
    ///
    /// let invalid = Validated::<String, i32>::invalid("error1".to_string());
    /// assert!(invalid.is_invalid());
    /// ```
    #[inline]
    pub fn invalid(e: E) -> Self
    where
        E: Clone,
    {
        let vec = PersistentVector::unit(e);
        Validated::Invalid(vec)
    }

    /// Creates a new invalid instance with multiple errors.
    ///
    /// Uses PersistentVector::from_slice for efficient initialization.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::datatypes::validated::Validated;
    ///
    /// let invalid = Validated::<String, i32>::invalid_many(&["error1".to_string(), "error2".to_string()]);
    /// assert!(invalid.is_invalid());
    /// ```
    #[inline]
    pub fn invalid_many(errors: &[E]) -> Self
    where
        E: Clone,
    {
        Validated::Invalid(PersistentVector::from_slice(errors))
    }

    /// Creates a new invalid instance with a pre-existing PersistentVector of errors.
    ///
    /// This is more efficient than `invalid_many` when you already have a PersistentVector,
    /// as it avoids creating a new vector and copying elements.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::datatypes::validated::Validated;
    ///
    /// let vec = vec!["error1".to_string(), "error2".to_string()];
    /// let invalid = Validated::<String, i32>::invalid_vec(vec);
    /// assert!(invalid.is_invalid());
    /// ```
    #[inline]
    pub fn invalid_vec(errors: Vec<E>) -> Self {
        Validated::Invalid(PersistentVector::from(errors))
    }

    /// Creates a new invalid instance containing errors from multiple Validated instances.
    ///
    /// This efficiently combines errors from multiple sources using PersistentVector's
    /// optimized concatenation.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::datatypes::validated::Validated;
    ///
    /// let valid1 = Validated::<String, i32>::valid(42);
    /// let valid2 = Validated::<String, i32>::valid(43);
    /// let invalid1 = Validated::<String, i32>::invalid("error1".to_string());
    /// let invalid2 = Validated::<String, i32>::invalid("error2".to_string());
    ///
    /// let invalid = Validated::invalid_combine(vec![valid1, valid2, invalid1, invalid2]);
    /// assert!(invalid.is_invalid());
    /// assert_eq!(invalid.error_count(), 2);
    /// ```
    #[inline]
    pub fn invalid_combine<I>(validators: I) -> Self
    where
        I: IntoIterator<Item = Self>,
        E: Clone,
        A: Clone,
    {
        let mut combined_errors = PersistentVector::new();
        let mut any_invalid = false;

        for validator in validators {
            if let Validated::Invalid(errors) = validator {
                combined_errors = combined_errors.concat(&errors);
                any_invalid = true;
            }
        }

        if any_invalid {
            Validated::Invalid(combined_errors)
        } else {
            // If no validators were invalid, we can't create a valid instance
            // since we don't have an A value. This function is primarily for
            // combining errors.
            Validated::Invalid(combined_errors)
        }
    }
}

impl<E: Clone, A: Clone> Validated<E, A> {
    /// Maps a function over the error values.
    ///
    /// If this is invalid, applies the function to transform each error.
    /// If this is valid, returns the value unchanged.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::datatypes::validated::Validated;
    ///
    /// let invalid = Validated::<String, i32>::invalid("error".to_string());
    /// let transformed = invalid.fmap_invalid(|e| e.len());
    /// assert_eq!(transformed.errors(), vec![5]);
    /// ```
    #[inline]
    pub fn fmap_invalid<G, F>(&self, f: F) -> Validated<G, A>
    where
        F: Fn(&E) -> G,
        G: Clone,
    {
        match self {
            Validated::Valid(x) => Validated::Valid(x.clone()),
            Validated::Invalid(e) => {
                // Use PersistentVector's map method for efficient transformation
                let transformed = e.map(&f);
                Validated::Invalid(transformed)
            }
        }
    }

    /// Maps a function over the error values, taking ownership of the Validated.
    ///
    /// This is more efficient than `fmap_invalid` when you have ownership of the Validated
    /// as it avoids cloning the value in the Valid case.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::datatypes::validated::Validated;
    ///
    /// let invalid = Validated::<String, i32>::invalid("error".to_string());
    /// let transformed = invalid.fmap_invalid_owned(|e| e.len());
    /// assert_eq!(transformed.errors(), vec![5]);
    /// ```
    #[inline]
    pub fn fmap_invalid_owned<G, F>(self, f: F) -> Validated<G, A>
    where
        F: FnMut(E) -> G,
        G: Clone,
    {
        match self {
            Validated::Valid(x) => Validated::Valid(x),
            Validated::Invalid(e) => {
                // Use into_iter to avoid cloning when transforming
                let transformed: PersistentVector<G> = e.into_iter().map(f).collect();
                Validated::Invalid(transformed)
            }
        }
    }

    /// Converts from `Result<A, E>` to `Validated<E, A>`.
    ///
    /// This method converts a borrowed `Result` to a `Validated`, cloning both
    /// the success value and error as needed.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::datatypes::validated::Validated;
    ///
    /// let ok_result: Result<i32, &str> = Ok(42);
    /// let valid = Validated::from_result(&ok_result);
    /// assert!(valid.is_valid());
    ///
    /// let err_result: Result<i32, &str> = Err("error");
    /// let invalid = Validated::from_result(&err_result);
    /// assert!(invalid.is_invalid());
    /// ```
    #[inline]
    pub fn from_result(result: &Result<A, E>) -> Validated<E, A> {
        match result {
            Ok(value) => Validated::Valid(value.clone()),
            Err(err) => Validated::invalid(err.clone()),
        }
    }

    /// Converts from `Result<A, E>` to `Validated<E, A>`, taking ownership of the Result.
    ///
    /// This method is more efficient than `from_result` when you have ownership of the Result
    /// as it avoids cloning the success value.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::datatypes::validated::Validated;
    ///
    /// let ok_result: Result<i32, &str> = Ok(42);
    /// let valid = Validated::from_result_owned(ok_result);
    /// assert!(valid.is_valid());
    ///
    /// let err_result: Result<i32, &str> = Err("error");
    /// let invalid = Validated::from_result_owned(err_result);
    /// assert!(invalid.is_invalid());
    /// ```
    #[inline]
    pub fn from_result_owned(result: Result<A, E>) -> Validated<E, A>
    where
        E: Clone,
    {
        match result {
            Ok(value) => Validated::Valid(value),
            Err(err) => Validated::invalid(err),
        }
    }

    /// Converts this `Validated` into a `Result`.
    ///
    /// This method converts a `Validated` into a `Result`, cloning both
    /// the success value and error as needed.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::datatypes::validated::Validated;
    ///
    /// let valid: Validated<String, i32> = Validated::Valid(42);
    /// let ok_result = valid.to_result();
    /// assert!(ok_result.is_ok());
    ///
    /// let invalid: Validated<String, i32> = Validated::Invalid(vec!["error".to_string()].into());
    /// let err_result = invalid.to_result();
    /// assert!(err_result.is_err());
    /// ```
    #[inline]
    pub fn to_result(&self) -> Result<A, PersistentVector<E>> {
        match self {
            Validated::Valid(a) => Ok(a.clone()),
            Validated::Invalid(e) => Err(e.clone()),
        }
    }

    /// Converts this `Validated` into a `Result`, taking ownership of the Validated.
    ///
    /// This method converts a `Validated` into a `Result`, moving the success value and error
    /// without cloning.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::datatypes::validated::Validated;
    ///
    /// let valid: Validated<String, i32> = Validated::Valid(42);
    /// let ok_result = valid.to_result_owned();
    /// assert!(ok_result.is_ok());
    ///
    /// let invalid: Validated<String, i32> = Validated::Invalid(vec!["error".to_string()].into());
    /// let err_result = invalid.to_result_owned();
    /// assert!(err_result.is_err());
    /// ```
    #[inline]
    pub fn to_result_owned(self) -> Result<A, PersistentVector<E>> {
        match self {
            Validated::Valid(a) => Ok(a),
            Validated::Invalid(e) => Err(e),
        }
    }

    /// Converts from `Option<A>` to `Validated<E, A>` with a provided error.
    ///
    /// This method converts a borrowed `Option` to a `Validated`, cloning both
    /// the success value and error as needed.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::datatypes::validated::Validated;
    ///
    /// let some_value = Some(42);
    /// let valid = Validated::from_option(&some_value, &"error");
    /// assert!(valid.is_valid());
    ///
    /// let none_value: Option<i32> = None;
    /// let invalid = Validated::from_option(&none_value, &"error");
    /// assert!(invalid.is_invalid());
    /// ```
    #[inline]
    pub fn from_option(option: &Option<A>, error: &E) -> Self {
        match option {
            Some(value) => Validated::Valid(value.clone()),
            None => Validated::invalid(error.clone()),
        }
    }

    /// Converts from `Option<A>` to `Validated<E, A>` with a provided error, taking ownership.
    ///
    /// This method converts a `Option` to a `Validated`, moving the success value and error
    /// without cloning.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::datatypes::validated::Validated;
    ///
    /// let some_value = Some(42);
    /// let valid = Validated::from_option_owned(some_value, "error".to_string());
    /// assert!(valid.is_valid());
    ///
    /// let none_value = None;
    /// let invalid: Validated<String, i32> = Validated::from_option_owned(none_value, "error".to_string());
    /// assert!(invalid.is_invalid());
    /// ```
    #[inline]
    pub fn from_option_owned(option: Option<A>, error: E) -> Self {
        match option {
            Some(value) => Validated::Valid(value),
            None => Validated::invalid(error),
        }
    }

    /// Converts from `Option<A>` to `Validated<E, A>` with a function to generate the error.
    ///
    /// This method converts a borrowed `Option` to a `Validated`, cloning both
    /// the success value and error as needed.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::datatypes::validated::Validated;
    ///
    /// let some_value = Some(42);
    /// let valid = Validated::from_option_with(&some_value, || "error");
    /// assert!(valid.is_valid());
    ///
    /// let none_value: Option<i32> = None;
    /// let invalid = Validated::from_option_with(&none_value, || "error");
    /// assert!(invalid.is_invalid());
    /// ```
    #[inline]
    pub fn from_option_with<F>(option: &Option<A>, error_fn: F) -> Self
    where
        F: Fn() -> E,
    {
        match option {
            Some(value) => Validated::Valid(value.clone()),
            None => Validated::invalid(error_fn()),
        }
    }

    /// Converts from `Option<A>` to `Validated<E, A>` with a function to generate the error, taking ownership.
    ///
    /// This method converts a `Option` to a `Validated`, moving the success value and error
    /// without cloning.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::datatypes::validated::Validated;
    ///
    /// let some_value = Some(42);
    /// let valid = Validated::from_option_with_owned(some_value, || "error");
    /// assert!(valid.is_valid());
    ///
    /// let none_value: Option<i32> = None;
    /// let invalid = Validated::from_option_with_owned(none_value, || "error");
    /// assert!(invalid.is_invalid());
    /// ```
    #[inline]
    pub fn from_option_with_owned<F>(option: Option<A>, error_fn: F) -> Self
    where
        F: FnOnce() -> E,
    {
        match option {
            Some(value) => Validated::Valid(value),
            None => Validated::invalid(error_fn()),
        }
    }

    /// Unwraps a valid value, panicking if the value is invalid.
    ///
    /// # Panics
    ///
    /// Panics if the value is invalid.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::datatypes::validated::Validated;
    ///
    /// let valid: Validated<&str, i32> = Validated::Valid(42);
    /// assert_eq!(valid.unwrap(), 42);
    ///
    /// // This would panic:
    /// // let invalid: Validated<&str, i32> = Validated::Invalid(vec!["error"].into());
    /// // invalid.unwrap();
    /// ```
    #[inline]
    pub fn unwrap(&self) -> A {
        match self {
            Validated::Valid(x) => x.clone(),
            _ => panic!("called `unwrap()` on an `Invalid` value"),
        }
    }

    /// Unwraps a valid value or returns a default.
    ///
    /// This method returns the valid value if the `Validated` is valid, otherwise returns the provided default value.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::datatypes::validated::Validated;
    ///
    /// let valid: Validated<&str, i32> = Validated::Valid(42);
    /// assert_eq!(valid.unwrap_or(&0), 42);
    ///
    /// let invalid: Validated<&str, i32> = Validated::Invalid(vec!["error"].into());
    /// assert_eq!(invalid.unwrap_or(&0), 0);
    /// ```
    #[inline]
    pub fn unwrap_or(&self, default: &A) -> A {
        match self {
            Validated::Valid(x) => x.clone(),
            _ => default.clone(),
        }
    }

    /// Combines multiple Validated values using a function.
    ///
    /// This method is optimized to efficiently accumulate errors using
    /// PersistentVector's structural sharing capabilities.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::datatypes::validated::Validated;
    /// use rustica::pvec::PersistentVector;
    ///
    /// let valid1 = Validated::Valid(1);
    /// let valid2 = Validated::Valid(2);
    /// let invalid1: Validated<String, i32> = Validated::Invalid(PersistentVector::from_slice(&["error1".to_string()]));
    /// let invalid2: Validated<String, i32> = Validated::Invalid(PersistentVector::from_slice(&["error2".to_string()]));
    ///
    /// let combined = Validated::sequence(&[&valid1, &valid2], |values: &[i32]| values.iter().sum());
    /// assert!(combined.is_valid());
    /// assert_eq!(combined.unwrap_or(&0), 3);
    ///
    /// let combined = Validated::sequence(&[&valid1, &invalid1], |values: &[i32]| values.iter().sum::<i32>());
    /// assert!(combined.is_invalid());
    /// assert_eq!(combined.error_count(), 1);
    /// ```
    #[inline]
    pub fn sequence<B, F>(values: &[&Validated<E, A>], f: F) -> Validated<E, B>
    where
        F: Fn(&[A]) -> B,
        B: Clone,
    {
        let mut all_valid = true;
        let mut errors = PersistentVector::new();
        let mut valid_values = Vec::with_capacity(values.len());

        for v in values {
            match v {
                Validated::Valid(x) => {
                    if all_valid {
                        valid_values.push(x.clone());
                    }
                }
                Validated::Invalid(e) => {
                    all_valid = false;
                    // Efficiently concatenate error vectors using PersistentVector's optimized concat
                    errors = errors.concat(e);
                }
            }
        }

        if all_valid {
            Validated::Valid(f(&valid_values))
        } else {
            Validated::Invalid(errors)
        }
    }

    /// Collects an iterator of Validated values into a single Validated value.
    ///
    /// This method efficiently processes an iterator of Validated values:
    /// - If all values are Valid, it collects them into a collection of type C
    /// - If any value is Invalid, it accumulates all errors using PersistentVector's optimized
    ///   structural sharing capabilities
    ///
    /// The implementation takes advantage of PersistentVector's efficient structural sharing
    /// for error accumulation with O(1) concatenation operations.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::datatypes::validated::Validated;
    /// use std::collections::HashSet;
    ///
    /// let valid1 = Validated::<String, i32>::valid(1);
    /// let valid2 = Validated::<String, i32>::valid(2);
    /// let invalid = Validated::<String, i32>::invalid("Invalid value".to_string());
    ///
    /// // Collect valid values into a Vec
    /// let result: Validated<String, Vec<i32>> =
    ///     Validated::collect(vec![valid1.clone(), valid2.clone()].into_iter());
    /// assert!(result.is_valid());
    /// assert_eq!(*result.unwrap_or(&vec![]), vec![1, 2]);
    ///
    /// // Collect with some invalid values - accumulates errors
    /// let result: Validated<String, Vec<i32>> =
    ///     Validated::collect(vec![valid1, invalid.clone(), valid2, invalid].into_iter());
    /// assert!(result.is_invalid());
    /// assert_eq!(result.error_count(), 2);
    /// ```
    #[inline]
    pub fn collect<I, C>(iter: I) -> Validated<E, C>
    where
        I: Iterator,
        I::Item: Borrow<Validated<E, A>>,
        C: FromIterator<A>,
    {
        let mut all_valid = true;
        let mut errors = PersistentVector::new();
        let mut valid_values = Vec::new();

        for item in iter {
            let validated = item.borrow();
            match validated {
                Validated::Valid(x) => {
                    // Always collect valid values, even if we've found errors
                    // This allows us to support partial validation scenarios
                    valid_values.push(x.clone());
                }
                Validated::Invalid(e) => {
                    all_valid = false;
                    // Efficiently concatenate error vectors using PersistentVector's optimized concat
                    errors = errors.concat(e);
                }
            }
        }

        if all_valid {
            Validated::Valid(valid_values.into_iter().collect())
        } else {
            Validated::Invalid(errors)
        }
    }

    /// Converts the `Validated` to an `Option`.
    ///
    /// This method returns `Some` if the `Validated` is valid, otherwise returns `None`.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::datatypes::validated::Validated;
    ///
    /// let valid: Validated<String, i32> = Validated::Valid(42);
    /// assert_eq!(valid.to_option(), Some(42));
    ///
    /// let invalid: Validated<String, i32> = Validated::Invalid(vec!["error".to_string()].into());
    /// assert_eq!(invalid.to_option(), None);
    /// ```
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
    /// This method applies the provided async function to the valid value if the `Validated` is valid,
    /// otherwise returns the original `Validated`.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::datatypes::validated::Validated;
    ///
    /// async fn async_add_one(x: i32) -> i32 {
    ///     x + 1
    /// }
    ///
    /// # #[tokio::main]
    /// # async fn main() {
    /// let valid: Validated<String, i32> = Validated::Valid(42);
    /// assert_eq!(valid.fmap_valid_async(async_add_one).await, Validated::Valid(43));
    ///
    /// let invalid: Validated<String, i32> = Validated::Invalid(vec!["error".to_string()].into());
    /// assert_eq!(invalid.fmap_valid_async(async_add_one).await, invalid);
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
            }
            Validated::Invalid(e) => Validated::Invalid(e.clone()),
        }
    }

    #[cfg(feature = "async")]
    /// Maps an async function over the error values.
    ///
    /// This method applies the provided async function to each error value if the `Validated` is invalid,
    /// otherwise returns the original `Validated`.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::datatypes::validated::Validated;
    ///
    /// async fn async_add_one(x: String) -> i32 {
    ///     x.len() as i32 + 1
    /// }
    ///
    /// # #[tokio::main]
    /// # async fn main() {
    /// let valid: Validated<String, i32> = Validated::Valid(42);
    /// let result = valid.fmap_invalid_async(async_add_one).await;
    /// assert_eq!(result, Validated::Valid(42));
    ///
    /// let invalid: Validated<String, i32> = Validated::Invalid(vec!["a".to_string(), "bb".to_string(), "ccc".to_string()].into());
    /// assert_eq!(invalid.fmap_invalid_async(async_add_one).await, Validated::Invalid(vec![2, 3, 4].into()));
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
            Validated::Invalid(e) => {
                let futures = e.iter().map(|e| f(e.clone()));

                // Using futures::future::join_all to run all futures concurrently
                let results = futures::future::join_all(futures).await;
                let transformed = results.into_iter().collect::<PersistentVector<_>>();

                Validated::Invalid(transformed)
            }
        }
    }

    #[cfg(feature = "async")]
    /// Chains an async validation operation to this Validated.
    ///
    /// This method applies the provided async function to the valid value if the `Validated` is valid,
    /// otherwise returns the original `Validated`.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::datatypes::validated::Validated;
    ///
    /// async fn async_add_one(x: i32) -> Validated<String, i32> {
    ///     Validated::Valid(x + 1)
    /// }
    ///
    /// # #[tokio::main]
    /// # async fn main() {
    /// let valid = Validated::Valid(42);
    /// assert_eq!(valid.bind_async(async_add_one).await, Validated::Valid(43));
    ///
    /// let invalid = Validated::Invalid(vec!["error".to_string()].into());
    /// assert_eq!(invalid.bind_async(async_add_one).await, invalid);
    /// # }
    /// ```
    #[inline]
    pub async fn bind_async<B, F, Fut>(&self, f: F) -> Validated<E, B>
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
}

impl<E: Clone, A> HKT for Validated<E, A> {
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

impl<E: Clone, A: Clone> Applicative for Validated<E, A> {
    #[inline]
    fn apply<B, F>(&self, rf: &Self::Output<F>) -> Self::Output<B>
    where
        F: Fn(&Self::Source) -> B,
        B: Clone,
    {
        match (self, rf) {
            (Validated::Valid(a), Validated::Valid(f)) => Validated::Valid(f(a)),
            (Validated::Valid(_), Validated::Invalid(e)) => Validated::Invalid(e.clone()),
            (Validated::Invalid(e), Validated::Valid(_)) => Validated::Invalid(e.clone()),
            // Optimized error combination using PersistentVector's efficient concat
            (Validated::Invalid(e1), Validated::Invalid(e2)) => Validated::Invalid(e1.concat(e2)),
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
            (Validated::Valid(_), Validated::Invalid(e)) => Validated::Invalid(e),
            (Validated::Invalid(e), Validated::Valid(_)) => Validated::Invalid(e),
            (Validated::Invalid(e1), Validated::Invalid(e2)) => Validated::Invalid(e1.concat(&e2)),
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
            // Cases where at least one value is invalid
            (Validated::Valid(_), Validated::Invalid(e)) => Validated::Invalid(e.clone()),
            (Validated::Invalid(e), Validated::Valid(_)) => Validated::Invalid(e.clone()),
            (Validated::Invalid(e1), Validated::Invalid(e2)) => Validated::Invalid(e1.concat(e2)),
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
            (Validated::Valid(_), Validated::Invalid(e)) => Validated::Invalid(e),
            (Validated::Invalid(e), Validated::Valid(_)) => Validated::Invalid(e),
            (Validated::Invalid(e1), Validated::Invalid(e2)) => Validated::Invalid(e1.concat(&e2)),
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
        // Optimize for the case where all three are valid
        if let (Validated::Valid(a), Validated::Valid(b), Validated::Valid(c)) = (self, rb, rc) {
            return Validated::Valid(f(a, b, c));
        }

        // For invalid cases, collect all errors
        let mut errors = PersistentVector::new();
        let mut valid = true;

        if let Validated::Invalid(e) = self {
            errors = errors.concat(e);
            valid = false;
        }

        if let Validated::Invalid(e) = rb {
            errors = errors.concat(e);
            valid = false;
        }

        if let Validated::Invalid(e) = rc {
            errors = errors.concat(e);
            valid = false;
        }

        if valid {
            // This case should not occur given the first check
            unreachable!("All inputs are valid, but we didn't return in the first check");
        } else {
            Validated::Invalid(errors)
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
        match (self, rb, rc) {
            // Optimize for the case where all three are valid
            (Validated::Valid(a), Validated::Valid(b), Validated::Valid(c)) => {
                Validated::Valid(f(a, b, c))
            }
            // Optimize for the case where the first input is invalid - avoid unnecessary processing
            (Validated::Invalid(e), _, _) => Validated::Invalid(e),
            // For other invalid combinations, collect all errors
            (Validated::Valid(_), rb, rc) => {
                let mut errors = PersistentVector::new();

                if let Validated::Invalid(e) = rb {
                    errors = errors.concat(&e);
                }

                if let Validated::Invalid(e) = rc {
                    errors = errors.concat(&e);
                }

                Validated::Invalid(errors)
            }
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

impl<E: Clone, A> Identity for Validated<E, A> {
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

impl<E: Clone, A> Composable for Validated<E, A> {}

impl<E: Clone, A> Foldable for Validated<E, A> {
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

impl<E: Clone, A> IntoIterator for Validated<E, A> {
    type Item = A;
    type IntoIter = std::option::IntoIter<Self::Item>;

    fn into_iter(self) -> Self::IntoIter {
        match self {
            Validated::Valid(a) => Some(a).into_iter(),
            _ => None.into_iter(),
        }
    }
}
