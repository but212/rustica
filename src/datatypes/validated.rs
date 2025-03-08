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
//! assert!(matches!(combined, Validated::Invalid(_)));
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

use crate::traits::hkt::HKT;
use crate::traits::applicative::Applicative;
use crate::traits::monad::Monad;
use crate::traits::pure::Pure;
use crate::traits::functor::Functor;
use crate::traits::identity::Identity;
use crate::traits::composable::Composable;
use crate::traits::transform::Transform;

/// A validation type that can accumulate multiple errors.
///
/// `Validated<E, A>` represents either a valid value of type `A` or a collection of
/// errors of type `E`. Unlike `Result`, which fails fast on the first error,
/// `Validated` can collect multiple errors during validation.
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
#[derive(Clone)]
pub enum Validated<E, A> {
    /// Represents a valid value of type `A`.
    Valid(A),
    /// Represents an invalid state with a vector of errors of type `E`.
    Invalid(Vec<E>),
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
    pub fn invalid(e: E) -> Self {
        Validated::Invalid(vec![e])
    }

    /// Creates a new invalid instance with multiple errors.
    ///
    /// # Arguments
    ///
    /// * `errors` - A vector of error values
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::validated::Validated;
    ///
    /// let invalid: Validated<&str, ()> = Validated::invalid_vec(vec!["error1", "error2"]);
    /// ```
    pub fn invalid_vec(errors: Vec<E>) -> Self {
        Validated::Invalid(errors)
    }

    /// Maps a function over the valid value.
    ///
    /// If this is a valid value, applies the function to transform the value.
    /// If this is invalid, returns the errors unchanged.
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
    /// let valid: Validated<(), i32> = Validated::valid(42);
    /// let doubled = valid.map_valid(&|x| x * 2);
    /// assert!(matches!(doubled, Validated::Valid(84)));
    /// ```
    pub fn map_valid<B: Clone>(&self, f: &dyn Fn(&A) -> B) -> Validated<E, B> {
        match self {
            Validated::Valid(x) => Validated::Valid(f(x)),
            Validated::Invalid(e) => Validated::Invalid(e.clone()),
        }
    }

    /// Maps a function over the error values.
    ///
    /// If this is invalid, applies the function to transform each error.
    /// If this is valid, returns the value unchanged.
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
    /// let invalid: Validated<&str, ()> = Validated::invalid("error");
    /// let mapped = invalid.map_invalid(&|e| format!("Error: {}", e));
    /// ```
    pub fn map_invalid<G: Clone>(&self, f: &dyn Fn(&E) -> G) -> Validated<G, A> {
        match self {
            Validated::Valid(x) => Validated::Valid(x.clone()),
            Validated::Invalid(es) => Validated::Invalid(es.iter().map(f).collect()),
        }
    }

    /// Converts from `Result<A, E>` to `Validated<E, A>`.
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
    /// ```
    pub fn from_result(result: &Result<A, E>) -> Validated<E, A>
    where
        A: Clone,
        E: Clone,
    {
        match result {
            Ok(x) => Validated::Valid(x.clone()),
            Err(e) => Validated::Invalid(vec![e.clone()]),
        }
    }

    /// Converts this `Validated` into a `Result`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::validated::Validated;
    ///
    /// let valid: Validated<(), i32> = Validated::valid(42);
    /// let result = valid.to_result();
    /// assert_eq!(result, Ok(42));
    /// ```
    pub fn to_result(&self) -> Result<A, Vec<E>> {
        match self {
            Validated::Valid(x) => Ok(x.clone()),
            Validated::Invalid(e) => Err(e.clone()),
        }
    }
}

impl<E, A> HKT for Validated<E, A> {
    type Source = A;
    type Output<T> = Validated<E, T>;
}

impl<E, A> Pure for Validated<E, A> {
    fn pure<T>(x: &T) -> Self::Output<T>
    where
        T: Clone,
    {
        Validated::Valid(x.clone())
    }
}

impl<E: Clone, A> Transform for Validated<E, A> {
    fn transform<F, B>(&self, f: F) -> Self::Output<B>
    where
        F: Fn(&Self::Source) -> B
    {
        match self {
            Validated::Valid(x) => Validated::Valid(f(x)),
            Validated::Invalid(e) => Validated::Invalid(e.clone()),
        }
    }

    fn transform_owned<F, NewType>(self, f: F) -> Self::Output<NewType>
    where
        F: Fn(Self::Source) -> NewType,
    {
        match self {
            Validated::Valid(x) => Validated::Valid(f(x)),
            Validated::Invalid(e) => Validated::Invalid(e.clone()),
        }
    }
}

impl<E: Clone, A> Functor for Validated<E, A> {}

impl<E: Clone, A> Applicative for Validated<E, A> {
    fn apply<B, F>(&self, rf: &Self::Output<F>) -> Self::Output<B>
    where
        F: Fn(&Self::Source) -> B,
    {
        match (self, rf) {
            (Validated::Valid(x), Validated::Valid(f)) => Validated::Valid(f(x)),
            (Validated::Invalid(e1), _) => Validated::Invalid(e1.clone()),
            (_, Validated::Invalid(e2)) => Validated::Invalid(e2.clone()),
        }
    }

    fn lift2<B, C, F>(&self, rb: &Self::Output<B>, f: F) -> Self::Output<C>
    where
        F: Fn(&Self::Source, &B) -> C,
    {
        match (self, rb) {
            (Validated::Valid(a), Validated::Valid(b)) => Validated::Valid(f(a, b)),
            (Validated::Invalid(e1), Validated::Invalid(e2)) => {
                let mut errors = e1.clone();
                errors.extend(e2.clone());
                Validated::Invalid(errors)
            }
            (Validated::Invalid(e), _) => Validated::Invalid(e.clone()),
            (_, Validated::Invalid(e)) => Validated::Invalid(e.clone()),
        }
    }

    fn lift3<B, C, D, F>(
        &self,
        rb: &Self::Output<B>,
        rc: &Self::Output<C>,
        f: F,
    ) -> Self::Output<D>
    where
        F: Fn(&Self::Source, &B, &C) -> D,
    {
        match (self, rb, rc) {
            (Validated::Valid(a), Validated::Valid(b), Validated::Valid(c)) => Validated::Valid(f(a, b, c)),
            (Validated::Invalid(e1), Validated::Invalid(e2), Validated::Invalid(e3)) => {
                let mut errors = e1.clone();
                errors.extend(e2.clone());
                errors.extend(e3.clone());
                Validated::Invalid(errors)
            }
            (Validated::Invalid(e), _, _) => Validated::Invalid(e.clone()),
            (_, Validated::Invalid(e), _) => Validated::Invalid(e.clone()),
            (_, _, Validated::Invalid(e)) => Validated::Invalid(e.clone()),
        }
    }

    fn apply_owned<B, F>(self, f: Self::Output<F>) -> Self::Output<B>
        where
            F: Fn(Self::Source) -> B,
            Self: Sized {
        match (self, f) {
            (Validated::Valid(x), Validated::Valid(f)) => Validated::Valid(f(x)),
            (Validated::Invalid(e1), _) => Validated::Invalid(e1.clone()),
            (_, Validated::Invalid(e2)) => Validated::Invalid(e2.clone()),
        }
    }

    fn lift2_owned<B, C, F>(
            self,
            b: Self::Output<B>,
            f: F,
        ) -> Self::Output<C>
        where
            F: Fn(Self::Source, B) -> C,
            Self: Sized,
            B: Clone {
        match (self, b) {
            (Validated::Valid(a), Validated::Valid(b)) => Validated::Valid(f(a, b)),
            (Validated::Invalid(e1), Validated::Invalid(e2)) => {
                let mut errors = e1.clone();
                errors.extend(e2.clone());
                Validated::Invalid(errors)
            }
            (Validated::Invalid(e), _) => Validated::Invalid(e.clone()),
            (_, Validated::Invalid(e)) => Validated::Invalid(e.clone()),
        }
    }

    fn lift3_owned<B, C, D, F>(
            self,
            b: Self::Output<B>,
            c: Self::Output<C>,
            f: F,
        ) -> Self::Output<D>
        where
            F: Fn(Self::Source, B, C) -> D,
            Self: Sized,
            B: Clone,
            C: Clone {
        match (self, b, c) {
            (Validated::Valid(a), Validated::Valid(b), Validated::Valid(c)) => Validated::Valid(f(a, b, c)),
            (Validated::Invalid(e1), Validated::Invalid(e2), Validated::Invalid(e3)) => {
                let mut errors = e1.clone();
                errors.extend(e2.clone());
                errors.extend(e3.clone());
                Validated::Invalid(errors)
            }
            (Validated::Invalid(e), _, _) => Validated::Invalid(e.clone()),
            (_, Validated::Invalid(e), _) => Validated::Invalid(e.clone()),
            (_, _, Validated::Invalid(e)) => Validated::Invalid(e.clone()),
        }
    }
}

impl<E: Clone, A> Monad for Validated<E, A> {
    fn bind<U, F>(&self, f: F) -> Self::Output<U>
    where
        F: Fn(&Self::Source) -> Self::Output<U>,
    {
        match self {
            Validated::Valid(x) => f(x),
            Validated::Invalid(e) => Validated::Invalid(e.clone()),
        }
    }

    fn join<U>(&self) -> Self::Output<U>
    where
        Self::Source: Clone + Into<Self::Output<U>>,
    {
        match self {
            Validated::Valid(x) => x.clone().into(),
            Validated::Invalid(e) => Validated::Invalid(e.clone()),
        }
    }

    fn bind_owned<U, F>(self, f: F) -> Self::Output<U>
        where
            F: Fn(Self::Source) -> Self::Output<U>,
            U: Clone,
            Self: Sized {
        match self {
            Validated::Valid(x) => f(x),
            Validated::Invalid(e) => Validated::Invalid(e.clone()),
        }
    }

    fn join_owned<U>(self) -> Self::Output<U>
        where
            Self::Source: Into<Self::Output<U>>,
            U: Clone,
            Self: Sized {
        match self {
            Validated::Valid(x) => x.into(),
            Validated::Invalid(e) => Validated::Invalid(e.clone()),
        }
    }
}

impl<E, A> Identity for Validated<E, A> {
    fn value(&self) -> &Self::Source {
        match self {
            Validated::Valid(x) => x,
            Validated::Invalid(_) => unreachable!(),
        }
    }

    fn pure_identity<B>(value: B) -> Self::Output<B>
    where
        Self::Output<B>: Identity,
    {
        Validated::Valid(value)
    }

    fn into_value(self) -> Self::Source {
        match self {
            Validated::Valid(x) => x,
            Validated::Invalid(_) => unreachable!(),
        }
    }
}

impl<E, A> Composable for Validated<E, A> {
    fn compose<T, U, F, G>(f: F, g: G) -> impl Fn(Self::Source) -> U
    where
        F: Fn(Self::Source) -> T,
        G: Fn(T) -> U,
    {
        move |x| g(f(x))
    }
}