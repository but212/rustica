//! # Core Error Category Theory Abstractions
//!
//! This module extends the existing `WithError` trait and introduces the `ErrorCategory`
//! trait for category-theoretic error handling. It provides the foundational abstractions
//! for composable, type-safe error management.

use crate::datatypes::either::Either;
use crate::datatypes::validated::Validated;
use crate::traits::hkt::HKT;
use smallvec::SmallVec;

pub trait WithError<E>: HKT {
    type Success;
    type ErrorOutput<G>;

    fn fmap_error<F, G>(self, f: F) -> Self::ErrorOutput<G>
    where
        F: Fn(E) -> G,
        G: Clone;

    fn to_result(self) -> Result<Self::Success, E>;
}

#[inline]
pub fn sequence<A, E>(collection: Vec<Result<A, E>>) -> Result<Vec<A>, E> {
    sequence_result(collection)
}

#[inline]
pub fn traverse<A, B, E, F>(collection: impl IntoIterator<Item = A>, f: F) -> Result<Vec<B>, E>
where
    F: FnMut(A) -> Result<B, E>,
{
    traverse_result(collection, f)
}

pub fn traverse_validated<A, B, E, F>(
    collection: impl IntoIterator<Item = A>, mut f: F,
) -> Validated<E, Vec<B>>
where
    F: FnMut(A) -> Result<B, E>,
    E: Clone,
{
    let mut values = Vec::new();
    let mut errors = SmallVec::<[E; 4]>::new();
    let mut had_error = false;

    for item in collection {
        match f(item) {
            Ok(value) => values.push(value),
            Err(error) => {
                had_error = true;
                errors.push(error);
            },
        }
    }

    if had_error {
        Validated::Invalid(errors)
    } else {
        Validated::Valid(values)
    }
}

#[inline]
pub fn sequence_with_error<C, T, E>(collection: Vec<C>) -> Result<Vec<T>, E>
where
    C: WithError<E>,
    C::Success: Clone + Into<T>,
    E: Clone,
{
    let mut values = Vec::with_capacity(collection.len());

    for item in collection {
        match item.to_result() {
            Ok(value) => values.push(value.into()),
            Err(error) => return Err(error),
        }
    }

    Ok(values)
}

#[inline]
fn sequence_result<A, E>(collection: Vec<Result<A, E>>) -> Result<Vec<A>, E> {
    let mut values = Vec::with_capacity(collection.len());

    for item in collection {
        match item {
            Ok(value) => values.push(value),
            Err(error) => return Err(error),
        }
    }

    Ok(values)
}

#[inline]
fn traverse_result<A, B, E, F>(
    collection: impl IntoIterator<Item = A>, mut f: F,
) -> Result<Vec<B>, E>
where
    F: FnMut(A) -> Result<B, E>,
{
    let mut values = Vec::new();

    for item in collection {
        match f(item) {
            Ok(value) => values.push(value),
            Err(error) => return Err(error),
        }
    }

    Ok(values)
}

impl<T, E: Clone> WithError<E> for Result<T, E> {
    type Success = T;
    type ErrorOutput<G> = Result<T, G>;

    fn fmap_error<F, G>(self, f: F) -> Self::ErrorOutput<G>
    where
        F: Fn(E) -> G,
    {
        match self {
            Ok(t) => Ok(t),
            Err(e) => Err(f(e)),
        }
    }

    fn to_result(self) -> Result<Self::Success, E> {
        self
    }
}

impl<T, E> WithError<E> for Either<E, T> {
    type Success = T;
    type ErrorOutput<G> = Either<G, T>;

    fn fmap_error<F, G>(self, f: F) -> Self::ErrorOutput<G>
    where
        F: Fn(E) -> G,
    {
        match self {
            Either::Left(e) => Either::Left(f(e)),
            Either::Right(t) => Either::Right(t),
        }
    }

    fn to_result(self) -> Result<Self::Success, E> {
        match self {
            Either::Left(e) => Err(e),
            Either::Right(t) => Ok(t),
        }
    }
}

impl<T: Clone, E: Clone> WithError<E> for Validated<E, T> {
    type Success = T;
    type ErrorOutput<G> = Validated<G, T>;

    fn fmap_error<F, G>(self, f: F) -> Self::ErrorOutput<G>
    where
        F: Fn(E) -> G,
        G: Clone,
        T: Clone,
    {
        match self {
            Validated::Valid(t) => Validated::Valid(t),
            Validated::Invalid(e) => Validated::Invalid(e.into_iter().map(f).collect()),
        }
    }

    fn to_result(self) -> Result<Self::Success, E> {
        match self {
            Validated::Valid(t) => Ok(t),
            Validated::Invalid(e) => Err(e.into_iter().next().unwrap()),
        }
    }
}

pub trait ResultExt<T, E> {
    #[deprecated(note = "Use `crate::error::result_to_validated` instead")]
    fn to_validated(self) -> Validated<E, T>;

    #[deprecated(note = "Use `crate::error::result_to_either` instead")]
    fn to_either(self) -> Either<E, T>;

    fn unwrap_or_default(self) -> T
    where
        T: Default;

    #[deprecated(note = "Use `crate::error::ErrorOps::bimap_result` instead")]
    fn bimap<F, G, U, E2>(self, success_map: F, error_map: G) -> Result<U, E2>
    where
        F: FnOnce(T) -> U,
        G: FnOnce(E) -> E2;
}

impl<T, E> ResultExt<T, E> for Result<T, E> {
    fn to_validated(self) -> Validated<E, T> {
        use smallvec::smallvec;

        match self {
            Ok(value) => Validated::Valid(value),
            Err(error) => Validated::Invalid(smallvec![error]),
        }
    }

    fn to_either(self) -> Either<E, T> {
        crate::error::result_to_either(self)
    }

    fn unwrap_or_default(self) -> T
    where
        T: Default,
    {
        self.unwrap_or_else(|_| T::default())
    }

    fn bimap<F, G, U, E2>(self, success_map: F, error_map: G) -> Result<U, E2>
    where
        F: FnOnce(T) -> U,
        G: FnOnce(E) -> E2,
    {
        match self {
            Ok(value) => Ok(success_map(value)),
            Err(error) => Err(error_map(error)),
        }
    }
}

/// A category-theoretic abstraction for error handling types.
///
/// `ErrorCategory` provides a unified interface for different error handling patterns,
/// ensuring that all error transformations follow categorical laws and maintain
/// functional purity.
///
/// # Type Parameters
///
/// * `E`: The error type that this category handles
///
/// # Laws
///
/// Implementations must satisfy the following categorical laws:
///
/// ## Identity Law
/// ```text
/// lift(x) is always a success value (never an error)
/// handle_error(e) is always an error value (never a success)
/// ```
///
/// ## Composition Law (Functor Law)
/// ```text
/// fmap_error(f . g) == fmap_error(f) . fmap_error(g)
/// ```
///
/// # Examples
///
/// ```rust
/// use rustica::error::ErrorCategory;
///
/// // Result implements ErrorCategory
/// let success = <Result<(), String> as ErrorCategory<String>>::lift(42);
/// assert_eq!(success, Ok(42));
///
/// let error: Result<i32, String> = <Result<(), String> as ErrorCategory<String>>::handle_error("failed".to_string());
/// assert_eq!(error, Err("failed".to_string()));
/// ```
pub trait ErrorCategory<E> {
    /// The error functor type that wraps values and errors
    type ErrorFunctor<T: Clone>: WithError<E>;

    /// Lifts a pure value into the error context.
    ///
    /// This operation represents the "success" case and should never fail.
    /// It's the categorical identity for successful computations.
    ///
    /// # Arguments
    ///
    /// * `value`: The value to lift into the error context
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::error::ErrorCategory;
    ///
    /// let lifted: Result<i32, String> = <Result<(), String> as ErrorCategory<String>>::lift(42);
    /// assert_eq!(lifted, Ok(42));
    /// ```
    fn lift<T: Clone>(value: T) -> Self::ErrorFunctor<T>;

    /// Creates an error instance in the error context.
    ///
    /// This operation represents the "failure" case and encapsulates
    /// the error according to the specific error handling strategy.
    ///
    /// # Arguments
    ///
    /// * `error`: The error to wrap in the error context
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::error::ErrorCategory;
    ///
    /// let error: Result<i32, String> = <Result<(), String> as ErrorCategory<String>>::handle_error("failed".to_string());
    /// assert_eq!(error, Err("failed".to_string()));
    /// ```
    fn handle_error<T: Clone>(error: E) -> Self::ErrorFunctor<T>;
}

/// Implementation of ErrorCategory for Result<T, E>
///
/// Result represents the most common error handling pattern in Rust,
/// providing fail-fast semantics where the first error stops computation.
impl<E: Clone> ErrorCategory<E> for Result<(), E> {
    type ErrorFunctor<T: Clone> = Result<T, E>;

    #[inline]
    fn lift<T>(value: T) -> Result<T, E> {
        Ok(value)
    }

    #[inline]
    fn handle_error<T>(error: E) -> Result<T, E> {
        Err(error)
    }
}

/// Implementation of ErrorCategory for Either<E, T>
///
/// Either provides a more general two-possibility type without the
/// semantic baggage of success/failure, making it suitable for
/// representing alternative computations.
impl<E: Clone> ErrorCategory<E> for Either<E, ()> {
    type ErrorFunctor<T: Clone> = Either<E, T>;

    #[inline]
    fn lift<T: Clone>(value: T) -> Either<E, T> {
        Either::Right(value)
    }

    #[inline]
    fn handle_error<T: Clone>(error: E) -> Either<E, T> {
        Either::Left(error)
    }
}

/// Implementation of ErrorCategory for Validated<E, T>
///
/// Validated provides error accumulation semantics, collecting all
/// errors rather than failing fast. This is particularly useful
/// for form validation and data parsing scenarios.
impl<E: Clone> ErrorCategory<E> for Validated<E, ()> {
    type ErrorFunctor<T: Clone> = Validated<E, T>;

    #[inline]
    fn lift<T: Clone>(value: T) -> Validated<E, T> {
        Validated::Valid(value)
    }

    #[inline]
    fn handle_error<T: Clone>(error: E) -> Validated<E, T> {
        Validated::invalid(error)
    }
}

/// Extended error handling operations for enhanced composability.
///
/// This trait provides additional operations that build upon `WithError`
/// to enable more sophisticated error handling patterns while maintaining
/// categorical properties.
pub trait ErrorOps<E>: WithError<E> {
    /// Applies a recovery function if this contains an error.
    ///
    /// This is the error-handling equivalent of `Option::or_else` or
    /// `Result::or_else`, allowing for error recovery and alternative
    /// computation paths.
    ///
    /// # Type Parameters
    ///
    /// * `F`: The recovery function type
    ///
    /// # Arguments
    ///
    /// * `recovery`: Function to apply if an error is present
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::error::ErrorOps;
    ///
    /// let error_result: Result<i32, &str> = Err("failed");
    /// let recovered = error_result.recover(|_| Ok(42));
    /// assert_eq!(recovered, Ok(42));
    /// ```
    fn recover<F>(self, recovery: F) -> Self
    where
        F: FnOnce(E) -> Self,
        Self: Sized;

    /// Maps over both success and error cases simultaneously.
    ///
    /// This provides a way to transform both the success value and error
    /// in a single operation, which is useful for type conversions and
    /// context transformations.
    ///
    /// # Type Parameters
    ///
    /// * `B`: The new success type
    /// * `F`: The new error type  
    /// * `SuccessF`: The success transformation function type
    /// * `ErrorF`: The error transformation function type
    ///
    /// # Arguments
    ///
    /// * `success_f`: Function to apply to success values
    /// * `error_f`: Function to apply to error values
    fn bimap_result<B, F, SuccessF, ErrorF>(
        self, success_f: SuccessF, error_f: ErrorF,
    ) -> Result<B, F>
    where
        SuccessF: FnOnce(Self::Success) -> B,
        ErrorF: FnOnce(E) -> F,
        Self: Sized;
}

/// Implementation of ErrorOps for Result<T, E>
impl<T: Clone, E: Clone> ErrorOps<E> for Result<T, E> {
    #[inline]
    fn recover<F>(self, recovery: F) -> Self
    where
        F: FnOnce(E) -> Self,
    {
        match self {
            Ok(value) => Ok(value),
            Err(error) => recovery(error),
        }
    }

    #[inline]
    fn bimap_result<B, F, SuccessF, ErrorF>(
        self, success_f: SuccessF, error_f: ErrorF,
    ) -> Result<B, F>
    where
        SuccessF: FnOnce(T) -> B,
        ErrorF: FnOnce(E) -> F,
    {
        match self {
            Ok(value) => Ok(success_f(value)),
            Err(error) => Err(error_f(error)),
        }
    }
}

/// Implementation of ErrorOps for Either<E, T>
impl<E: Clone, T: Clone> ErrorOps<E> for Either<E, T> {
    #[inline]
    fn recover<F>(self, recovery: F) -> Self
    where
        F: FnOnce(E) -> Self,
    {
        match self {
            Either::Right(value) => Either::Right(value),
            Either::Left(error) => recovery(error),
        }
    }

    fn bimap_result<B, F, SuccessF, ErrorF>(
        self, success_f: SuccessF, error_f: ErrorF,
    ) -> Result<B, F>
    where
        SuccessF: FnOnce(Self::Success) -> B,
        ErrorF: FnOnce(E) -> F,
        Self: Sized,
    {
        match self {
            Either::Right(value) => Ok(success_f(value)),
            Either::Left(error) => Err(error_f(error)),
        }
    }
}
