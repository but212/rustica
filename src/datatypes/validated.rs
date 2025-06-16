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
//! The `Applicative` instance for `Validated` is particularly powerful for accumulating errors from multiple independent validation steps. This is often used in scenarios like form validation.
//!
//! ### Example: User Registration Form Validation
//!
//! ```rust
//! use rustica::datatypes::validated::Validated;
//! use rustica::traits::applicative::Applicative;
//!
//! #[derive(Debug, PartialEq, Clone)]
//! struct User {
//!     username: String,
//!     email: String,
//!     age: u32,
//! }
//!
//! fn validate_username(username: &str) -> Validated<String, String> {
//!     if username.len() >= 3 {
//!         Validated::valid(username.to_string())
//!     } else {
//!         Validated::invalid("Username must be at least 3 characters".to_string())
//!     }
//! }
//!
//! fn validate_email(email: &str) -> Validated<String, String> {
//!     if email.contains('@') {
//!         Validated::valid(email.to_string())
//!     } else {
//!         Validated::invalid("Email must contain @ symbol".to_string())
//!     }
//! }
//!
//! fn validate_age(age: u32) -> Validated<String, u32> {
//!     if age >= 18 {
//!         Validated::valid(age)
//!     } else {
//!         Validated::invalid("Must be at least 18 years old".to_string())
//!     }
//! }
//!
//! // Combine all validations
//! let username_validation = validate_username("jo");
//! let email_validation = validate_email("invalid-email");
//! let age_validation = validate_age(16);
//!
//! let user_validation = username_validation
//!     .lift2(&email_validation, |username, email| {
//!         (username.clone(), email.clone())
//!     })
//!     .lift2(&age_validation, |(username, email), age| User {
//!         username: username.clone(),
//!         email: email.clone(),
//!         age: *age,
//!     });
//!
//! assert!(user_validation.is_invalid());
//! let errors = user_validation.unwrap_invalid();
//! assert_eq!(errors.len(), 3); // All three validation errors are collected
//! ```
//!
//! One of the most powerful aspects of `Validated` is its applicative instance, which allows
//! combining multiple validations while accumulating errors. This is particularly useful for
//! form validation, configuration validation, or any scenario where you want to report all
//! errors at once rather than one at a time.
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
#[cfg(feature = "develop")]
use quickcheck::{Arbitrary, Gen};
use smallvec::{smallvec, SmallVec};

/// A validation type that can accumulate multiple errors.
///
/// Validated<E, A> represents either a valid value of type A or a collection of
/// errors of type E. Unlike Result, which fails fast on the first error,
/// Validated can collect multiple errors during validation.
///
/// # Performance
///
/// The performance of `Validated` methods depends on the variant (`Valid` or `Invalid`)
/// and the operation being performed.
///
/// - **`Functor` (`fmap`) and `Monad` (`bind`)**: These operations are constant time, O(1),
///   as they only operate on the `Valid` variant and pass the `Invalid` variant through
///   without modification. This makes them efficient for fail-fast validation pipelines.
///
/// - **`Applicative` (`apply`) and `Alternative` (`alt`)**: When combining two `Invalid`
///   instances, these operations have a time complexity of O(n + m), where `n` and `m`
///   are the number of errors in each instance. This is because they concatenate the
///   underlying error collections (`SmallVec`). This is the trade-off for accumulating
///   all errors.
///
/// - **`Bifunctor` (`bimap`, `fmap_invalid`)**: When operating on an `Invalid` variant,
///   these methods are linear time, O(n), where `n` is the number of errors, as they
///   must iterate over the error collection to apply the mapping function.
///
/// `Validated` uses `SmallVec<[E; 4]>` internally to store errors, which optimizes for
/// the common case of having 1-4 validation errors by avoiding heap allocation.
///
/// ## Type Parameter Constraints
///
/// - **`E: Clone`**: The error type `E` often requires a `Clone` bound. This is because:
///   - Operations that accumulate errors from multiple `Validated` instances (e.g., in `Applicative::apply` when both are `Invalid`) may need to combine and thus clone error collections.
///   - Methods providing access to errors (e.g., `errors()`, which returns `Vec<E>`) typically clone the internal errors to avoid lifetime issues or to provide owned data.
///   If your error type `E` is expensive to clone, consider wrapping it in an `Arc<E>` or ensure that operations that trigger cloning are used judiciously.
///
/// - **`A: Clone`**: The value type `A` also often requires a `Clone` bound for similar reasons, especially for methods that operate on `&self` but need to return an owned `Validated` or extract the value (e.g., `unwrap()`, `fmap_invalid` when `self` is `Valid`). Ownership-taking variants of methods (e.g., `fmap_owned`, `unwrap_owned` if it existed) can sometimes alleviate this requirement for `A`.
///
/// ## Notes on Trait Implementations
///
/// - **`Alternative::empty()`**: The `empty()` method from the `Alternative` trait, when implemented for `Validated<E, A>`, returns `Validated::Invalid` containing an empty collection of errors (i.e., `SmallVec::new()`). It does **not** require the error type `E` to implement `Default` to produce a default error. The "empty" state refers to an absence of accumulated errors.

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
        self.iter_errors().cloned().collect()
    }

    /// Returns an iterator over all errors if this is invalid, or an empty iterator if valid.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::validated::Validated;
    ///
    /// let valid: Validated<&str, i32> = Validated::valid(42);
    /// let mut errors = valid.iter_errors();
    /// assert!(errors.next().is_none());
    ///
    /// let invalid: Validated<&str, i32> = Validated::invalid("error");
    /// let mut errors = invalid.iter_errors();
    /// assert_eq!(errors.next().unwrap(), &"error");
    /// assert!(errors.next().is_none());
    /// ```
    #[inline]
    pub fn iter_errors(&self) -> std::slice::Iter<'_, E> {
        match self {
            Validated::Valid(_) => [].iter(),
            Validated::Invalid(es) => es.iter(),
        }
    }

    /// Returns a reference to the valid value if this is `Valid`, otherwise `None`.
    ///
    /// This method provides a way to safely access the contained value without cloning or panicking.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::validated::Validated;
    ///
    /// let valid: Validated<&str, i32> = Validated::valid(42);
    /// assert_eq!(valid.value(), Some(&42));
    ///
    /// let invalid: Validated<&str, i32> = Validated::invalid("error");
    /// assert_eq!(invalid.value(), None);
    /// ```
    #[inline]
    pub fn value(&self) -> Option<&A> {
        match self {
            Validated::Valid(a) => Some(a),
            Validated::Invalid(_) => None,
        }
    }

    /// Returns a reference to the internal `SmallVec` of errors if this is `Invalid`, otherwise `None`.
    ///
    /// This provides direct, non-cloning access to the error collection.
    /// If you need an owned `Vec<E>` (which clones), see the `errors()` method.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::validated::Validated;
    /// use smallvec::smallvec;
    ///
    /// let valid: Validated<&str, i32> = Validated::valid(42);
    /// assert_eq!(valid.error_payload(), None);
    ///
    /// let invalid: Validated<&str, i32> = Validated::invalid("error");
    /// assert_eq!(invalid.error_payload(), Some(&smallvec!["error"]));
    ///
    /// let invalid_many: Validated<String, i32> = Validated::invalid_many(vec!["err1".to_string(), "err2".to_string()]);
    /// assert_eq!(invalid_many.error_payload(), Some(&smallvec!["err1".to_string(), "err2".to_string()]));
    /// ```
    #[inline]
    pub fn error_payload(&self) -> Option<&SmallVec<[E; 4]>> {
        match self {
            Validated::Valid(_) => None,
            Validated::Invalid(es) => Some(es),
        }
    }

    /// Returns the contained `Valid` value, consuming the `self` value.
    ///
    /// Because this function consumes `self`, it does not require `A` to be `Clone`.
    /// This is more efficient than `unwrap()` if `A` is `Clone` but cloning is expensive,
    /// or if `A` is not `Clone`.
    ///
    /// # Panics
    ///
    /// Panics if `self` is `Invalid`, with a panic message including the errors.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::validated::Validated;
    ///
    /// let valid: Validated<&str, i32> = Validated::valid(42);
    /// assert_eq!(valid.unwrap_owned(), 42);
    /// ```
    ///
    /// ```rust,should_panic
    /// use rustica::datatypes::validated::Validated;
    ///
    /// let invalid: Validated<&str, i32> = Validated::invalid("error message");
    /// // This will panic with: "Called Validated::unwrap_owned() on an Invalid value: [\"error message\"]"
    /// invalid.unwrap_owned();
    /// ```
    #[inline]
    pub fn unwrap_owned(self) -> A
    where
        E: std::fmt::Debug,
    {
        match self {
            Validated::Valid(a) => a,
            Validated::Invalid(e) => panic!(
                "Called Validated::unwrap_owned() on an Invalid value: {:?}",
                e
            ),
        }
    }

    /// Returns the contained `Invalid` error collection, consuming the `self` value.
    ///
    /// This method moves the `SmallVec` out of the `Validated` instance.
    ///
    /// # Panics
    ///
    /// Panics if `self` is `Valid`, with a panic message including the valid value.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::validated::Validated;
    /// use smallvec::SmallVec;
    ///
    /// let invalid: Validated<&str, i32> = Validated::invalid("error");
    /// assert_eq!(invalid.unwrap_invalid_owned(), SmallVec::<[&str; 4]>::from_slice(&["error"]));
    /// ```
    ///
    /// ```rust,should_panic
    /// use rustica::datatypes::validated::Validated;
    ///
    /// let valid: Validated<&str, i32> = Validated::valid(42);
    /// // This will panic with: "Called Validated::unwrap_invalid_owned() on a Valid value: 42"
    /// valid.unwrap_invalid_owned();
    /// ```
    #[inline]
    pub fn unwrap_invalid_owned(self) -> SmallVec<[E; 4]>
    where
        A: std::fmt::Debug,
    {
        match self {
            Validated::Valid(a) => panic!(
                "Called Validated::unwrap_invalid_owned() on a Valid value: {:?}",
                a
            ),
            Validated::Invalid(e) => e,
        }
    }

    /// Consumes `self` and returns `Ok(A)` if `Valid(A)`, or `Err(SmallVec<[E; 4]>)` if `Invalid(errors)`.
    ///
    /// This method is useful for safely extracting the valid value or the complete collection of errors,
    /// transferring ownership without cloning the contained value or errors.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::validated::Validated;
    /// use smallvec::smallvec;
    ///
    /// let valid: Validated<&str, i32> = Validated::valid(42);
    /// assert_eq!(valid.into_value(), Ok(42));
    ///
    /// let invalid: Validated<&str, i32> = Validated::invalid_many(vec!["err1", "err2"]);
    /// assert_eq!(invalid.into_value(), Err(smallvec!["err1", "err2"]));
    ///
    /// // Example with non-Clone types
    /// #[derive(Debug, PartialEq)]
    /// struct NonCloneValue(String);
    /// #[derive(Debug, PartialEq)]
    /// struct NonCloneError(String);
    ///
    /// let valid_nc: Validated<NonCloneError, NonCloneValue> = Validated::Valid(NonCloneValue("data".to_string()));
    /// assert_eq!(valid_nc.into_value(), Ok(NonCloneValue("data".to_string())));
    ///
    /// let invalid_nc: Validated<NonCloneError, NonCloneValue> = Validated::Invalid(smallvec![NonCloneError("fail".to_string())]);
    /// assert_eq!(invalid_nc.into_value(), Err(smallvec![NonCloneError("fail".to_string())]));
    /// ```
    #[inline]
    pub fn into_value(self) -> Result<A, SmallVec<[E; 4]>> {
        match self {
            Validated::Valid(a) => Ok(a),
            Validated::Invalid(es) => Err(es),
        }
    }

    /// Consumes `self` and returns `Ok(SmallVec<[E; 4]>)` if `Invalid(errors)`, or `Err(A)` if `Valid(A)`.
    ///
    /// This method is useful for safely extracting the complete error collection or the valid value,
    /// transferring ownership without cloning the contained value or errors.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::validated::Validated;
    /// use smallvec::smallvec;
    ///
    /// let valid: Validated<&str, i32> = Validated::valid(42);
    /// assert_eq!(valid.into_error_payload(), Err(42));
    ///
    /// let invalid: Validated<&str, i32> = Validated::invalid_many(vec!["err1", "err2"]);
    /// assert_eq!(invalid.into_error_payload(), Ok(smallvec!["err1", "err2"]));
    ///
    /// // Example with non-Clone types
    /// #[derive(Debug, PartialEq)]
    /// struct NonCloneValue(String);
    /// #[derive(Debug, PartialEq)]
    /// struct NonCloneError(String);
    ///
    /// let valid_nc: Validated<NonCloneError, NonCloneValue> = Validated::Valid(NonCloneValue("data".to_string()));
    /// assert_eq!(valid_nc.into_error_payload(), Err(NonCloneValue("data".to_string())));
    ///
    /// let invalid_nc: Validated<NonCloneError, NonCloneValue> = Validated::Invalid(smallvec![NonCloneError("fail".to_string())]);
    /// assert_eq!(invalid_nc.into_error_payload(), Ok(smallvec![NonCloneError("fail".to_string())]));
    /// ```
    #[inline]
    pub fn into_error_payload(self) -> Result<SmallVec<[E; 4]>, A> {
        match self {
            Validated::Valid(a) => Err(a),
            Validated::Invalid(es) => Ok(es),
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
    /// Unlike `invalid_vec`, this method **does not panic** if the input `errors` collection is empty.
    /// If `errors` is empty, this function will produce `Validated::Invalid` containing an empty list of errors
    /// (e.g., `Validated::Invalid([])`).
    /// This makes `invalid_many` suitable for scenarios where an invalid state might legitimately have no specific
    /// error items, or where the input collection's emptiness is not considered a panic-worthy condition.
    ///
    /// If you specifically require that an `Invalid` instance must contain at least one error and wish for a panic
    /// if the input is empty, see `invalid_vec`.
    ///
    /// # Arguments
    ///
    /// * `errors` - A collection of error values that can be converted into a SmallVec
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::validated::Validated;
    /// use smallvec::smallvec;
    ///
    /// let errors_list = vec!["error1", "error2"];
    /// let invalid: Validated<&str, ()> = Validated::invalid_many(errors_list.clone());
    /// assert!(invalid.is_invalid());
    /// assert_eq!(invalid.errors(), errors_list);
    /// ```
    ///
    /// ```rust
    /// use rustica::datatypes::validated::Validated;
    ///
    /// // Creating an invalid Validated from an empty Vec using invalid_many
    /// // results in Invalid with an empty list of errors.
    /// let invalid_empty: Validated<&str, ()> = Validated::invalid_many(Vec::<&str>::new());
    /// assert!(invalid_empty.is_invalid());
    /// assert!(invalid_empty.errors().is_empty());
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
    /// **Important:** This function requires the input collection to contain at least one error.
    /// If the provided `errors` collection is empty, this function will **panic**.
    /// If you need to create an `Invalid` instance that can represent an empty set of errors
    /// (e.g., `Validated::Invalid([])`), use `invalid_many` instead. `invalid_many` will produce
    /// `Validated::Invalid` with an empty error list if given an empty input collection, without panicking.
    ///
    /// The rationale for this panicking behavior is to ensure that an `Invalid` state constructed via
    /// `invalid_vec` is guaranteed to be non-empty, which might be a specific requirement in certain contexts.
    /// However, for general use, `invalid_many` is often more flexible.
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
    /// let errors_list = vec!["error1", "error2"];
    /// let invalid: Validated<&str, ()> = Validated::invalid_vec(errors_list.clone());
    /// assert!(invalid.is_invalid());
    /// assert_eq!(invalid.errors(), errors_list);
    /// ```
    ///
    /// ```rust,should_panic
    /// use rustica::datatypes::validated::Validated;
    ///
    /// // Attempting to create an invalid Validated from an empty Vec using invalid_vec should panic.
    /// let _invalid_empty: Validated<&str, ()> = Validated::invalid_vec(Vec::<&str>::new());
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

    /// Maps a function over the error values if `Invalid`, or returns the `Valid` value (cloned).
    ///
    /// If this `Validated` is `Invalid`, applies the function `f` to transform each error.
    /// If `Valid`, the original valid value `A` is cloned and returned in a new `Validated::Valid`.
    /// This method is suitable when you only have a reference (`&self`) to the `Validated` value.
    ///
    /// # Performance
    ///
    /// When `self` is `Valid`, the contained value `A` is cloned. If `self` is `Invalid`, errors are iterated.
    /// For an ownership-based version that avoids cloning `A` when `self` is `Valid`, see `fmap_invalid_owned`.
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
    pub fn fmap_invalid<G, F>(&self, f: F) -> Validated<G, A>
    where
        F: Fn(&E) -> G,
        G: Clone,
    {
        match self {
            Validated::Valid(x) => Validated::Valid(x.clone()),
            Validated::Invalid(_) => {
                let transformed = self.iter_errors().map(f).collect();
                Validated::Invalid(transformed)
            },
        }
    }

    /// Maps a function over the error values if `Invalid` (taking ownership), or returns the `Valid` value (moved).
    ///
    /// If this `Validated` is `Invalid`, applies the function `f` to transform each error (errors `E` are moved into `f`).
    /// If `Valid`, the original valid value `A` is moved and returned in a new `Validated::Valid`.
    /// This method takes `self` by ownership, which can be more efficient as it avoids cloning the value `A` if it's `Valid`.
    ///
    /// # Performance
    ///
    /// When `self` is `Valid`, the contained value `A` is moved. If `self` is `Invalid`, errors are moved and iterated.
    /// This is generally more efficient than `fmap_invalid` if you have ownership of the `Validated` instance.
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
    pub fn fmap_invalid_owned<G, F>(self, f: F) -> Validated<G, A>
    where
        F: Fn(E) -> G,
        G: Clone,
    {
        match self {
            Validated::Valid(x) => Validated::Valid(x),
            Validated::Invalid(es) => {
                let transformed: SmallVec<[G; 4]> = es.into_iter().map(f).collect();
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
    /// use smallvec::smallvec;
    ///
    /// let invalid1: Validated<&str, i32> = Validated::invalid("error1");
    /// let invalid2: Validated<&str, i32> = Validated::invalid_many(["error2", "error3"]);
    ///
    /// // Case 1: self is Invalid, other is Invalid
    /// let combined1 = invalid1.clone().combine_errors(&invalid2);
    /// assert!(combined1.is_invalid());
    /// if let Validated::Invalid(errors) = combined1 {
    ///     assert_eq!(errors.as_slice(), &["error1", "error2", "error3"]);
    /// }
    ///
    /// // Case 2: self is Valid, other is Invalid
    /// let valid1: Validated<&str, i32> = Validated::valid(1);
    /// let combined2 = valid1.clone().combine_errors(&invalid2);
    /// assert!(combined2.is_invalid());
    /// if let Validated::Invalid(errors) = combined2 {
    ///     assert_eq!(errors.as_slice(), &["error2", "error3"]);
    /// }
    ///
    /// // Case 3: self is Invalid, other is Valid
    /// let combined3 = invalid1.clone().combine_errors(&valid1);
    /// assert!(combined3.is_invalid());
    /// if let Validated::Invalid(errors) = combined3 {
    ///     assert_eq!(errors.as_slice(), &["error1"]);
    /// }
    /// ```
    ///
    /// ```rust,should_panic
    /// use rustica::datatypes::validated::Validated;
    ///
    /// // Panics if both are Valid
    /// let valid1: Validated<&str, i32> = Validated::valid(1);
    /// let valid2: Validated<&str, i32> = Validated::valid(2);
    /// let _combined_panic = valid1.combine_errors(&valid2);
    /// ```
    pub fn combine_errors(&self, other: &Self) -> Self {
        match (self, other) {
            (Validated::Valid(_), Validated::Valid(_)) => unreachable!(),
            (Validated::Valid(_), invalid) => invalid.clone(),
            (invalid, Validated::Valid(_)) => invalid.clone(),
            (Validated::Invalid(_), Validated::Invalid(_)) => {
                let errors = self
                    .iter_errors()
                    .chain(other.iter_errors())
                    .cloned()
                    .collect();
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
    /// ```rust,should_panic
    /// use rustica::datatypes::validated::Validated;
    ///
    /// let invalid: Validated<&str, i32> = Validated::invalid("error");
    /// invalid.unwrap(); // Panics
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

    /// Unwraps a valid value or panics with a message.
    ///
    /// If this is valid, returns the valid value.
    /// If this is invalid, panics with a message.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::validated::Validated;
    /// use smallvec::smallvec;
    ///
    /// let invalid: Validated<&str, i32> = Validated::invalid_many(["e1", "e2"]);
    /// assert_eq!(invalid.unwrap_invalid(), vec!["e1", "e2"]);
    /// ```
    ///
    /// ```rust,should_panic
    /// use rustica::datatypes::validated::Validated;
    ///
    /// let valid: Validated<&str, i32> = Validated::valid(42);
    /// valid.unwrap_invalid(); // Panics
    /// ```
    ///
    /// # Panics
    ///
    /// Panics if this is `Valid`.
    #[inline]
    pub fn unwrap_invalid(&self) -> Vec<E>
    where
        E: Clone,
    {
        match self {
            Validated::Invalid(_) => self.iter_errors().cloned().collect(),
            _ => panic!("Cannot unwrap valid value"),
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
    /// let sum = Validated::sequence(&values, &|vs: &[i32]| {
    ///     vs.iter().sum()
    /// });
    /// assert_eq!(sum, Validated::valid(6));
    ///
    /// // Example with invalid inputs
    /// let d: Validated<&str, i32> = Validated::invalid("error1");
    /// let e: Validated<&str, i32> = Validated::valid(5);
    /// let f: Validated<&str, i32> = Validated::invalid("error2");
    /// let mixed_values = [&d, &e, &f];
    /// let mixed_result = Validated::sequence(&mixed_values, &|vs: &[i32]| vs.iter().sum::<i32>());
    /// assert!(mixed_result.is_invalid());
    /// if let Validated::Invalid(errors) = mixed_result {
    ///     assert_eq!(errors.as_slice(), &["error1", "error2"]);
    /// }
    ///
    /// // Example with empty input
    /// let empty_values: &[&Validated<&str, i32>; 0] = &[];
    /// let empty_result = Validated::sequence(empty_values, &|vs: &[i32]| vs.iter().sum::<i32>());
    /// assert_eq!(empty_result, Validated::valid(0));
    /// ```
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

        // Collect all errors using iterator methods
        let errors = values
            .iter()
            .filter_map(|v| match v {
                Validated::Invalid(es) => Some(es.iter().cloned()),
                _ => None,
            })
            .flatten()
            .collect::<SmallVec<[E; 4]>>();

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
    /// if let Validated::Invalid(errors) = collected {
    ///     assert_eq!(errors.as_slice(), &["error"]);
    /// }
    ///
    /// // Example with all invalid inputs
    /// let all_invalid = vec![
    ///     Validated::<&str, i32>::invalid("err1"),
    ///     Validated::<&str, i32>::invalid("err2"),
    /// ];
    /// let collected_all_invalid: Validated<&str, Vec<i32>> = Validated::collect(all_invalid.iter().cloned());
    /// assert!(collected_all_invalid.is_invalid());
    /// if let Validated::Invalid(errors) = collected_all_invalid {
    ///     assert_eq!(errors.as_slice(), &["err1", "err2"]);
    /// }
    ///
    /// // Example with an empty iterator
    /// let empty_iter: std::vec::IntoIter<Validated<&str, i32>> = vec![].into_iter();
    /// let collected_empty: Validated<&str, Vec<i32>> = Validated::collect(empty_iter);
    /// assert_eq!(collected_empty, Validated::valid(Vec::<i32>::new()));
    /// ```
    pub fn collect<I, C>(iter: I) -> Validated<E, C>
    where
        I: Iterator<Item = Validated<E, A>>,
        C: FromIterator<A> + Clone,
        A: Clone,
        E: Clone,
    {
        let (values, errors): (Vec<_>, SmallVec<[E; 4]>) = iter.fold(
            (Vec::new(), SmallVec::<[E; 4]>::new()),
            |(mut values, mut errors), item| {
                match item {
                    Validated::Valid(a) => values.push(a),
                    Validated::Invalid(es) => errors.extend(es),
                }
                (values, errors)
            },
        );

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

/// # Examples for `Pure` on `Validated`
///
/// `Pure` provides a way to lift a simple value into the `Validated` context, always resulting
/// in a `Valid` instance.
///
/// # Performance
///
/// The `pure` operation is constant time, O(1).
///
/// ## `pure`
///
/// ```rust
/// use rustica::datatypes::validated::Validated;
/// use rustica::traits::pure::Pure;
///
/// let valid: Validated<&str, i32> = <Validated<&str, i32> as Pure>::pure(&10);
/// assert_eq!(valid, Validated::valid(10));
/// ```
///
/// ## `pure_owned`
///
/// ```rust
/// use rustica::datatypes::validated::Validated;
/// use rustica::traits::pure::Pure;
///
/// let valid: Validated<String, i32> = <Validated<String, i32> as Pure>::pure_owned(10);
/// assert_eq!(valid, Validated::valid(10));
/// ```
impl<E: Clone, A: Clone> Pure for Validated<E, A> {
    #[inline]
    fn pure<T: Clone>(x: &T) -> Self::Output<T> {
        Validated::Valid(x.clone())
    }

    #[inline]
    fn pure_owned<T: Clone>(x: T) -> Self::Output<T> {
        Validated::Valid(x)
    }
}

/// # Examples for `Functor` on `Validated`
///
/// ## `fmap`
///
/// Mapping over a `Valid` value:
/// ```rust
/// use rustica::datatypes::validated::Validated;
/// use rustica::traits::functor::Functor;
///
/// let valid: Validated<&str, i32> = Validated::valid(10);
/// let mapped = valid.fmap(|x: &i32| x * 2);
/// assert_eq!(mapped, Validated::valid(20));
/// ```
///
/// Mapping over an `Invalid` value:
/// ```rust
/// use rustica::datatypes::validated::Validated;
/// use rustica::traits::functor::Functor;
///
/// let invalid: Validated<&str, i32> = Validated::invalid("error");
/// let mapped = invalid.fmap(|x: &i32| x * 2);
/// assert_eq!(mapped, Validated::invalid("error"));
/// ```
///
/// # Performance
///
/// The `fmap` operation is constant time, O(1), as it only affects the `Valid` variant.
///
/// ## `fmap_owned`
///
/// Mapping over a `Valid` value with ownership:
/// ```rust
/// use rustica::datatypes::validated::Validated;
/// use rustica::traits::functor::Functor;
///
/// let valid: Validated<String, i32> = Validated::valid(10);
/// let mapped = valid.fmap_owned(|x: i32| x * 2);
/// assert_eq!(mapped, Validated::valid(20));
/// ```
///
/// Mapping over an `Invalid` value with ownership:
/// ```rust
/// use rustica::datatypes::validated::Validated;
/// use rustica::traits::functor::Functor;
///
/// let invalid: Validated<String, i32> = Validated::invalid("error".to_string());
/// let mapped = invalid.fmap_owned(|x: i32| x * 2);
/// assert_eq!(mapped, Validated::invalid("error".to_string()));
/// ```
///
/// ## Functor Laws
///
/// ### Identity Law: `v.fmap(|x| x.clone()) == v`
/// ```rust
/// use rustica::datatypes::validated::Validated;
/// use rustica::traits::functor::Functor;
///
/// let valid: Validated<&str, i32> = Validated::valid(10);
/// assert_eq!(valid.fmap(|x: &i32| *x), valid);
///
/// let invalid: Validated<&str, i32> = Validated::invalid("error");
/// assert_eq!(invalid.fmap(|x: &i32| *x), invalid);
/// ```
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

/// # Examples for `Bifunctor` on `Validated`
///
/// `Bifunctor` allows mapping over either the `Invalid` (left) or `Valid` (right) side.
///
/// ## `bimap`
///
/// ### Mapping over a `Valid` value (applies the right function)
/// ```rust
/// use rustica::datatypes::validated::Validated;
/// use rustica::traits::bifunctor::Bifunctor;
///
/// let valid: Validated<&str, i32> = Validated::valid(10);
/// let result = valid.bimap(|v: &i32| v * 2, |e: &&str| format!("Error: {}", e));
/// assert_eq!(result, Validated::valid(20));
/// ```
///
/// ### Mapping over an `Invalid` value (applies the left function)
/// ```rust
/// use rustica::datatypes::validated::Validated;
/// use rustica::traits::bifunctor::Bifunctor;
/// use smallvec::smallvec;
///
/// let invalid: Validated<&str, i32> = Validated::invalid_many(vec!["e1", "e2"]);
/// let result = invalid.bimap(|v: &i32| v * 2, |e: &&str| format!("New-{}", e));
/// assert_eq!(result, Validated::invalid_many(vec!["New-e1".to_string(), "New-e2".to_string()]));
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

/// # Examples for `Applicative` on `Validated`
///
/// `Validated`'s `Applicative` instance accumulates errors.
///
/// ## `apply`
///
/// ### Valid function, Valid value
/// ```rust
/// use rustica::datatypes::validated::Validated;
/// use rustica::traits::applicative::Applicative;
/// use rustica::traits::pure::Pure;
///
/// let valid_fn: Validated<&str, fn(&i32) -> i32> = Validated::valid(|x: &i32| x * 2);
/// let valid_val: Validated<&str, i32> = Validated::valid(10);
/// assert_eq!(valid_val.apply(&valid_fn), Validated::valid(20));
/// ```
///
/// ### Invalid function, Valid value
/// ```rust
/// use rustica::datatypes::validated::Validated;
/// use rustica::traits::applicative::Applicative;
/// use rustica::traits::pure::Pure;
///
/// let invalid_fn: Validated<&str, fn(&i32) -> i32> = Validated::invalid("fn_error");
/// let valid_val: Validated<&str, i32> = Validated::valid(10);
/// assert_eq!(valid_val.apply(&invalid_fn), Validated::invalid("fn_error"));
/// ```
///
/// ### Valid function, Invalid value
/// ```rust
/// use rustica::datatypes::validated::Validated;
/// use rustica::traits::applicative::Applicative;
/// use rustica::traits::pure::Pure;
///
/// let valid_fn: Validated<&str, fn(&i32) -> i32> = Validated::valid(|x: &i32| x * 2);
/// let invalid_val: Validated<&str, i32> = Validated::invalid("val_error");
/// assert_eq!(invalid_val.apply(&valid_fn), Validated::invalid("val_error"));
/// ```
///
/// ### Invalid function, Invalid value (error accumulation)
/// ```rust
/// use rustica::datatypes::validated::Validated;
/// use rustica::traits::applicative::Applicative;
/// use rustica::traits::pure::Pure;
/// use smallvec::smallvec;
///
/// let invalid_fn: Validated<String, fn(&i32) -> i32> = Validated::invalid("fn_error".to_string());
/// let invalid_val: Validated<String, i32> = Validated::invalid("val_error".to_string());
/// // The apply implementation for Validated accumulates errors in a specific order:
/// // first the errors from the function, then the errors from the value
/// let expected_errors = smallvec!["val_error".to_string(), "fn_error".to_string()];
/// assert_eq!(invalid_val.apply(&invalid_fn), Validated::Invalid(expected_errors));
/// ```
///
/// # Performance
///
/// The `apply` and `lift2` operations exhibit the following performance characteristics:
/// - `Valid` + `Valid` -> `Valid`: Constant time, O(1).
/// - `Valid` + `Invalid` -> `Invalid`: Constant time, O(1).
/// - `Invalid` + `Valid` -> `Invalid`: Constant time, O(1).
/// - `Invalid` + `Invalid` -> `Invalid`: Linear time, O(n + m), where `n` and `m` are the
///   number of errors in the respective instances. This is due to the concatenation of error lists.
///
/// ## `lift2`
///
/// Combining two `Valid` values:
/// ```rust
/// use rustica::datatypes::validated::Validated;
/// use rustica::traits::applicative::Applicative;
///
/// let v1: Validated<&str, i32> = Validated::valid(10);
/// let v2: Validated<&str, i32> = Validated::valid(20);
/// let result = v1.lift2(&v2, |a: &i32, b: &i32| a + b);
/// assert_eq!(result, Validated::valid(30));
/// ```
///
/// Combining `Valid` and `Invalid` (error accumulation):
/// ```rust
/// use rustica::datatypes::validated::Validated;
/// use rustica::traits::applicative::Applicative;
/// use smallvec::smallvec;
///
/// let v1: Validated<&str, i32> = Validated::valid(10);
/// let v2: Validated<&str, i32> = Validated::invalid("error_b");
/// let result = v1.lift2(&v2, |a: &i32, b: &i32| a + b);
/// assert_eq!(result, Validated::Invalid(smallvec!["error_b"]));
///
/// let v3: Validated<&str, i32> = Validated::invalid("error_a");
/// let v4: Validated<&str, i32> = Validated::valid(20);
/// let result2 = v3.lift2(&v4, |a: &i32, b: &i32| a + b);
/// assert_eq!(result2, Validated::Invalid(smallvec!["error_a"]));
/// ```
///
/// Combining two `Invalid` values (error accumulation):
/// ```rust
/// use rustica::datatypes::validated::Validated;
/// use rustica::traits::applicative::Applicative;
/// use smallvec::smallvec;
///
/// let v1: Validated<&str, i32> = Validated::invalid("error1");
/// let v2: Validated<&str, i32> = Validated::invalid("error2");
/// let result = v1.lift2(&v2, |a: &i32, b: &i32| a + b);
/// // The order of errors in lift2 is self's errors then rb's errors.
/// assert_eq!(result, Validated::Invalid(smallvec!["error1", "error2"]));
/// ```
///
/// ## Applicative Laws
///
/// ### Homomorphism: `Pure::pure_owned(f).apply_owned(Pure::pure_owned(x)) == Pure::pure_owned(f(x))`
/// ```rust
/// use rustica::datatypes::validated::Validated;
/// use rustica::traits::applicative::Applicative;
/// use rustica::traits::pure::Pure;
///
/// let f = |x: &i32| *x * 2;
/// let x = 10;
///
/// // Wrap the function in Validated first
/// let pure_f: Validated<String, fn(&i32) -> i32> = Validated::<String, fn(&i32) -> i32>::pure_owned(f);
/// // Wrap the value in Validated
/// let pure_x: Validated<String, i32> = Validated::<String, i32>::pure_owned(x);
///
/// // Now apply properly (function first, then value)
/// let lhs = pure_x.apply(&pure_f);
/// let rhs: Validated<String, i32> = Validated::<String, i32>::pure_owned(f(&x));
///
/// assert_eq!(lhs, rhs);
/// assert_eq!(lhs, Validated::valid(20));
/// ```
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

/// # Examples for `Monad` on `Validated`
///
/// Unlike `Applicative`, the `Monad` instance for `Validated` is fail-fast. It does not
/// accumulate errors. It's useful for sequencing operations where any failure should
/// halt the entire chain.
///
/// ## `bind`
///
/// ### Chaining `Valid` computations
/// ```rust
/// use rustica::datatypes::validated::Validated;
/// use rustica::traits::monad::Monad;
///
/// let v: Validated<&str, i32> = Validated::valid(10);
/// let result = v.bind(|x: &i32| Validated::valid(*x + 5));
/// assert_eq!(result, Validated::valid(15));
/// ```
///
/// ### A `Valid` value bound with a function that returns `Invalid`
/// ```rust
/// use rustica::datatypes::validated::Validated;
/// use rustica::traits::monad::Monad;
///
/// let v: Validated<&str, i32> = Validated::valid(10);
/// let result = v.bind(|_x: &i32| Validated::<&str, i32>::invalid("computation_failed"));
/// assert_eq!(result, Validated::invalid("computation_failed"));
/// ```
///
/// ### An `Invalid` value (short-circuiting)
/// ```rust
/// use rustica::datatypes::validated::Validated;
/// use rustica::traits::monad::Monad;
///
/// let v: Validated<&str, i32> = Validated::invalid("original_error");
/// // The closure is never executed because `v` is Invalid.
/// let result = v.bind(|x: &i32| Validated::valid(*x + 5));
/// assert_eq!(result, Validated::invalid("original_error"));
/// ```
///
/// # Performance
///
/// The `bind` operation is constant time, O(1), as it only affects the `Valid` variant.
///
/// ## Monad Laws
///
/// ### Left Identity: `Pure::pure_owned(a).bind_owned(f) == f(a)`
/// ```rust
/// use rustica::datatypes::validated::Validated;
/// use rustica::traits::monad::Monad;
/// use rustica::traits::pure::Pure;
///
/// let f = |x: i32| -> Validated<String, i32> { Validated::valid(x * 2) };
/// let x = 21;
///
/// let lhs = <Validated<String, i32> as Pure>::pure_owned(x).bind_owned(f);
/// let rhs = f(x);
///
/// assert_eq!(lhs, rhs);
/// assert_eq!(lhs, Validated::valid(42));
/// ```
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

/// # Examples for `Foldable` on `Validated`
///
/// ```rust
/// use rustica::datatypes::validated::Validated;
/// use rustica::traits::foldable::Foldable;
///
/// // Folding a Valid value with fold_left
/// let valid = Validated::<&str, i32>::valid(42);
/// let doubled = valid.fold_left(&0, |_, x| *x * 2);
/// assert_eq!(doubled, 84);
///
/// // Folding an Invalid value with fold_left returns the initial value
/// let invalid = Validated::<&str, i32>::invalid("error");
/// let result = invalid.fold_left(&100, |_, x| *x + 1);
/// assert_eq!(result, 100);
///
/// // Folding a Valid value with fold_right
/// let valid = Validated::<&str, i32>::valid(42);
/// let doubled = valid.fold_right(&0, |x, _| *x * 2);
/// assert_eq!(doubled, 84);
///
/// // Folding an Invalid value with fold_right returns the initial value
/// let invalid = Validated::<&str, i32>::invalid("error");
/// let result = invalid.fold_right(&100, |x, _| *x + 1);
/// assert_eq!(result, 100);
/// ```
///
/// # Performance
///
/// The `fold_left` and `fold_right` operations are constant time, O(1), as they only affect the `Valid` variant.
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

/// # Examples for `Alternative` on `Validated`
///
/// `Alternative` provides a way to express choice and failure. For `Validated`, it
/// provides a fallback mechanism. The error type `E` must implement `Default`.
///
/// ## `alt`
///
/// `alt` returns the first `Valid` instance, otherwise it returns the second argument.
///
/// ### First value is `Valid`
/// ```rust
/// use rustica::datatypes::validated::Validated;
/// use rustica::traits::alternative::Alternative;
///
/// let v1: Validated<String, i32> = Validated::valid(1);
/// let v2: Validated<String, i32> = Validated::valid(2);
/// assert_eq!(v1.alt(&v2), Validated::valid(1));
/// ```
///
/// ### First value is `Invalid`, second is `Valid`
/// ```rust
/// use rustica::datatypes::validated::Validated;
/// use rustica::traits::alternative::Alternative;
///
/// let v1: Validated<String, i32> = Validated::invalid("error".to_string());
/// let v2: Validated<String, i32> = Validated::valid(2);
/// assert_eq!(v1.alt(&v2), Validated::valid(2));
/// ```
///
/// ### Both values are `Invalid`
/// ```rust
/// use rustica::datatypes::validated::Validated;
/// use rustica::traits::alternative::Alternative;
///
/// let v1: Validated<String, i32> = Validated::invalid("error1".to_string());
/// let v2: Validated<String, i32> = Validated::invalid("error2".to_string());
/// assert_eq!(v1.alt(&v2), Validated::invalid("error2".to_string()));
/// ```
///
/// # Performance
///
/// The `alt` operation is constant time, O(1), as it only checks the first variant.
///
/// ## `empty_alt`
///
/// `empty_alt` creates an `Invalid` instance with a default error.
///
/// ```rust
/// use rustica::datatypes::validated::Validated;
/// use rustica::traits::alternative::Alternative;
/// use smallvec::smallvec;
///
/// let empty: Validated<String, i32> = <Validated<String, i32> as Alternative>::empty_alt();
/// assert!(empty.is_invalid());
/// // It contains a single, default error.
/// assert_eq!(empty.errors().as_slice(), &[String::default()]);
/// ```
///
/// ## `guard`
///
/// `guard` creates a `Valid(())` if the condition is true, otherwise an `Invalid`
/// instance with a default error.
///
/// ### Condition is true
/// ```rust
/// use rustica::datatypes::validated::Validated;
/// use rustica::traits::alternative::Alternative;
///
/// let result: Validated<String, ()> = <Validated<String, ()> as Alternative>::guard(true);
/// assert_eq!(result, Validated::valid(()));
/// ```
///
/// ### Condition is false
/// ```rust
/// use rustica::datatypes::validated::Validated;
/// use rustica::traits::alternative::Alternative;
///
/// let result: Validated<String, ()> = <Validated<String, ()> as Alternative>::guard(false);
/// assert!(result.is_invalid());
/// assert_eq!(result.errors().as_slice(), &[String::default()]);
/// ```
///
/// ## `many`
///
/// `many` collects one or more occurrences. For `Validated`, this means if the value is
/// `Valid`, it returns a `Valid` `Vec` with one element. If it's `Invalid`, it
/// returns an `Invalid` with a default error, discarding original errors.
///
/// ### On a `Valid` value
/// ```rust
/// use rustica::datatypes::validated::Validated;
/// use rustica::traits::alternative::Alternative;
///
/// let v: Validated<String, i32> = Validated::valid(42);
/// assert_eq!(v.many(), Validated::valid(vec![42]));
/// ```
///
/// ### On an `Invalid` value
/// ```rust
/// use rustica::datatypes::validated::Validated;
/// use rustica::traits::alternative::Alternative;
///
/// let v: Validated<String, i32> = Validated::invalid("original error".to_string());
/// let result = v.many();
/// assert!(result.is_invalid());
/// // Note: original errors are discarded.
/// assert_eq!(result.errors().as_slice(), &[String::default()]);
/// ```
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

/// # Examples for `MonadPlus` on `Validated`
///
/// `MonadPlus` extends `Monad` with additional operations for combining values.
///
/// ## `mzero`
///
/// ```rust
/// use rustica::datatypes::validated::Validated;
/// use rustica::traits::monad_plus::MonadPlus;
///
/// // Create a zero value using mzero
/// let zero: Validated<&str, i32> = Validated::<&str, i32>::mzero();
/// assert!(zero.is_invalid());
///
/// // Check that it's invalid with empty errors
/// assert_eq!(zero.errors().len(), 0);
///
/// // mzero is the identity element for mplus
/// let valid = Validated::valid(42);
/// assert_eq!(zero.mplus(&valid), valid);
/// assert_eq!(valid.mplus(&zero), valid);
/// ```
///
/// # Performance
///
/// The `mplus` operation has the same performance characteristics as `Applicative::apply`.
/// It is O(n + m) when combining two `Invalid` instances.
///
/// ## `mplus`
///
/// `mplus` returns the first `Valid` instance, or combines errors if both are `Invalid`.
///
/// ### Combining with first value valid
/// ```rust
/// use rustica::datatypes::validated::Validated;
/// use rustica::traits::monad_plus::MonadPlus;
///
/// let a: Validated<&str, i32> = Validated::valid(42);
/// let b: Validated<&str, i32> = Validated::invalid("error");
/// let result = a.mplus(&b);
/// assert_eq!(result, Validated::valid(42));
/// ```
///
/// ### Combining with second value valid
/// ```rust
/// use rustica::datatypes::validated::Validated;
/// use rustica::traits::monad_plus::MonadPlus;
///
/// let a: Validated<&str, i32> = Validated::invalid("error1");
/// let b: Validated<&str, i32> = Validated::valid(42);
/// let result = a.mplus(&b);
/// assert_eq!(result, Validated::valid(42));
/// ```
///
/// ### Combining with both values invalid
/// ```rust
/// use rustica::datatypes::validated::Validated;
/// use rustica::traits::monad_plus::MonadPlus;
///
/// let a: Validated<&str, i32> = Validated::invalid("error1");
/// let b: Validated<&str, i32> = Validated::invalid("error2");
/// let result = a.mplus(&b);
/// assert!(result.is_invalid());
/// assert_eq!(result.iter_errors().collect::<Vec<_>>(), vec![&"error1", &"error2"]);
/// ```
impl<E: Clone, A: Clone> MonadPlus for Validated<E, A> {
    fn mzero<U: Clone>() -> Self::Output<U> {
        Validated::invalid_many(Vec::new())
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

#[cfg(feature = "develop")]
impl<E, A> Arbitrary for Validated<E, A>
where
    E: Arbitrary,
    A: Arbitrary,
{
    fn arbitrary(g: &mut Gen) -> Self {
        let x = A::arbitrary(g);
        let y = E::arbitrary(g);
        if bool::arbitrary(g) {
            Validated::valid(x)
        } else {
            Validated::invalid(y)
        }
    }
}
