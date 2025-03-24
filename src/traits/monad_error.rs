//! # MonadError
//!
//! The `MonadError` module provides trait definitions for error handling in a monadic context.
//! It extends the `Monad` trait with error-specific operations.
//!
//! MonadError is particularly useful for implementing error handling strategies that follow
//! functional programming principles. It allows for catching, handling, and throwing errors
//! within a monadic context without breaking the computation chain.
//!
//! # Relationship to other traits
//!
//! MonadError is an extension of the Monad trait, providing specialized operations for error handling:
//!
//! ```text
//! Functor -> Applicative -> Monad -> MonadError
//! ```
//!
//! # Mathematical Definition
//!
//! A MonadError is a monad with additional error handling structure:
//! - `throw`: E -> M A
//! - `catch`: M A -> (E -> M A) -> M A
//!
//! # Laws
//!
//! For a valid MonadError implementation, the following laws must hold:
//!
//! 1. Left Catch Law:
//!    ```text
//!    throw(e).catch(h) == h(e)
//!    ```
//!    Catching an error that was just thrown should be equivalent to just handling that error.
//!
//! 2. Right Catch Law:
//!    ```text
//!    m.catch(throw) == m
//!    ```
//!    Catching with throw as the handler should be a no-op.
//!
//! 3. Associativity Catch Law:
//!    ```text
//!    m.catch(h1).catch(h2) == m.catch(e -> h1(e).catch(h2))
//!    ```
//!    Nested catches can be rewritten as a single catch with a composed handler.
//!
//! # Examples
//!
//! ```rust
//! use rustica::traits::monad_error::{MonadError, ErrorMapper};
//! use rustica::traits::monad::Monad;
//! use rustica::traits::pure::Pure;
//! use rustica::traits::functor::Functor;
//!
//! // Define a simple custom error that implements Clone
//! #[derive(Debug, Clone, PartialEq)]
//! struct AppError {
//!     message: String,
//!     code: i32,
//! }
//!
//! // Using Result as a MonadError to handle errors
//! let success_result: Result<i32, AppError> = Result::<i32, AppError>::pure(&42);
//! let error_result: Result<i32, AppError> = Result::<i32, AppError>::throw(AppError {
//!     message: "Item not found".to_string(),
//!     code: 404,
//! });
//!
//! // Catching errors
//! let handled = error_result.catch(|e| {
//!     if e.code == 404 {
//!         Ok(0)  // Default value for not found
//!     } else {
//!         Err(e.clone()) // Pass through other errors
//!     }
//! });
//!
//! assert_eq!(handled, Ok(0));
//!
//! // Transforming between error types using ErrorMapper
//! let string_error = success_result.map_error_to::<String, _>(|e| format!("Error {}: {}", e.code, e.message));
//!
//! assert_eq!(string_error, Ok(42));
//! ```
use crate::traits::monad::Monad;
use std::fmt::Debug;

/// A trait for monads that can handle errors, extending the basic Monad trait.
///
/// MonadError provides operations for throwing errors and catching errors within
/// a monadic context. It allows for robust error handling while maintaining the
/// benefits of monadic computation chains.
///
/// # Type Parameters
/// * `E`: The error type that can be thrown and caught
///
/// # Laws
/// For a valid MonadError implementation, the following laws must hold:
///
/// 1. Left Catch Law:
///    throw(e).catch(h) == h(e)
///    Catching an error that was just thrown should be equivalent to just handling that error.
///
/// 2. Right Catch Law:
///    m.catch(throw) == m
///    Catching with throw as the handler should be a no-op.
///
/// 3. Associativity Catch Law:
///    m.catch(h1).catch(h2) == m.catch(e -> h1(e).catch(h2))
///    Nested catches can be rewritten as a single catch with a composed handler.
pub trait MonadError<E>: Monad
where
    E: Clone + Debug,
{
    /// Creates a new instance in an error state.
    ///
    /// This is the equivalent of throwing an exception in languages with exceptions.
    ///
    /// # Type Parameters
    /// * `T`: The type of value that would be contained in a successful result
    ///
    /// # Parameters
    /// * `error`: The error value to throw
    ///
    /// # Returns
    /// A new monadic value in an error state
    fn throw<T: Clone>(error: E) -> Self::Output<T>;

    /// Handles an error by applying a function that can recover from the error.
    ///
    /// If this monadic value is in an error state, applies the given function to
    /// recover. Otherwise, returns the current successful value.
    ///
    /// # Type Parameters
    /// * `F`: The type of the error-handling function
    ///
    /// # Parameters
    /// * `f`: A function that takes an error and returns a new monadic value
    ///
    /// # Returns
    /// Either the original successful value or the result of applying the
    /// recovery function to the error
    fn catch<F>(&self, f: F) -> Self::Output<Self::Source>
    where
        F: Fn(&E) -> Self::Output<Self::Source>,
        Self::Source: Clone;

    /// Handles an error by applying a function that can recover from the error, consuming self.
    ///
    /// This variant of `catch` takes ownership of `self`, allowing for more efficient
    /// implementations when the original monad is no longer needed.
    ///
    /// # Type Parameters
    /// * `F`: The type of the error-handling function
    ///
    /// # Parameters
    /// * `f`: A function that takes an error and returns a new monadic value
    ///
    /// # Returns
    /// Either the original successful value or the result of applying the
    /// recovery function to the error
    fn catch_owned<F>(self, f: F) -> Self::Output<Self::Source>
    where
        F: Fn(E) -> Self::Output<Self::Source>,
        Self::Source: Clone,
        Self: Sized;
}

/// A trait for types that can map their error type to a different error type.
///
/// This trait is separate from MonadError to allow for more flexible error handling
/// where the error type can be transformed.
///
/// # Type Parameters
/// * `E`: The original error type
///
/// # Examples
///
/// ```rust
/// use rustica::traits::monad_error::ErrorMapper;
///
/// // Use a simple String as our error type, which implements Clone
/// let result: Result<i32, String> = Ok(42);
/// let string_result = result.map_error_to::<String, _>(|e| format!("Error: {}", e));
/// assert_eq!(string_result, Ok(42));
/// ```
pub trait ErrorMapper<E>
where
    E: Clone + Debug,
{
    /// The source type contained in the monad
    type Source;

    /// Transforms the error type using the given function.
    ///
    /// This allows for adapting between different error types while preserving
    /// the successful value.
    ///
    /// # Type Parameters
    /// * `NewE`: The new error type
    /// * `F`: The type of the error-mapping function
    ///
    /// # Parameters
    /// * `f`: A function that transforms the error type
    ///
    /// # Returns
    /// A new monadic value with the same success type but a different error type
    fn map_error_to<NewE, F>(&self, f: F) -> Result<Self::Source, NewE>
    where
        F: Fn(&E) -> NewE,
        NewE: Clone + Debug,
        Self::Source: Clone;

    /// Transforms the error type using the given function, consuming self.
    ///
    /// This variant of `map_error_to` takes ownership of `self`, allowing for more
    /// efficient implementations when the original monad is no longer needed.
    ///
    /// # Type Parameters
    /// * `NewE`: The new error type
    /// * `F`: The type of the error-mapping function
    ///
    /// # Parameters
    /// * `f`: A function that transforms the error type
    ///
    /// # Returns
    /// A new monadic value with the same success type but a different error type
    fn map_error_to_owned<NewE, F>(self, f: F) -> Result<Self::Source, NewE>
    where
        F: Fn(E) -> NewE,
        NewE: Clone + Debug,
        Self::Source: Clone,
        Self: Sized;
}

// Implementation for Result
impl<T: Clone, E: Clone + Debug> MonadError<E> for Result<T, E> {
    #[inline]
    fn throw<U: Clone>(error: E) -> Self::Output<U> {
        Err(error)
    }

    #[inline]
    fn catch<F>(&self, f: F) -> Self::Output<Self::Source>
    where
        F: Fn(&E) -> Self::Output<Self::Source>,
        Self::Source: Clone,
    {
        match self {
            Ok(value) => Ok(value.clone()),
            Err(error) => f(error),
        }
    }

    #[inline]
    fn catch_owned<F>(self, f: F) -> Self::Output<Self::Source>
    where
        F: Fn(E) -> Self::Output<Self::Source>,
        Self::Source: Clone,
        Self: Sized,
    {
        match self {
            Ok(value) => Ok(value),
            Err(error) => f(error),
        }
    }
}

// Implementation of ErrorMapper for Result
impl<T: Clone, E: Clone + Debug> ErrorMapper<E> for Result<T, E> {
    type Source = T;

    #[inline]
    fn map_error_to<NewE, F>(&self, f: F) -> Result<Self::Source, NewE>
    where
        F: Fn(&E) -> NewE,
        NewE: Clone + Debug,
        Self::Source: Clone,
    {
        match self {
            Ok(value) => Ok(value.clone()),
            Err(error) => Err(f(error)),
        }
    }

    #[inline]
    fn map_error_to_owned<NewE, F>(self, f: F) -> Result<Self::Source, NewE>
    where
        F: Fn(E) -> NewE,
        NewE: Clone + Debug,
        Self::Source: Clone,
        Self: Sized,
    {
        match self {
            Ok(value) => Ok(value),
            Err(error) => Err(f(error)),
        }
    }
}

// Add implementations for Option, treating None as an error
// Option doesn't have an explicit error type, so we use () as a placeholder
impl<T: Clone> MonadError<()> for Option<T> {
    #[inline]
    fn throw<U: Clone>(_error: ()) -> Self::Output<U> {
        None
    }

    #[inline]
    fn catch<F>(&self, f: F) -> Self::Output<Self::Source>
    where
        F: Fn(&()) -> Self::Output<Self::Source>,
        Self::Source: Clone,
    {
        match self {
            Some(value) => Some(value.clone()),
            None => f(&()),
        }
    }

    #[inline]
    fn catch_owned<F>(self, f: F) -> Self::Output<Self::Source>
    where
        F: Fn(()) -> Self::Output<Self::Source>,
        Self::Source: Clone,
        Self: Sized,
    {
        match self {
            Some(value) => Some(value),
            None => f(()),
        }
    }
}

// Option can map its "error" type by converting None to a specific error
impl<T: Clone> ErrorMapper<()> for Option<T> {
    type Source = T;

    #[inline]
    fn map_error_to<NewE, F>(&self, f: F) -> Result<Self::Source, NewE>
    where
        F: Fn(&()) -> NewE,
        NewE: Clone + Debug,
        Self::Source: Clone,
    {
        match self {
            Some(value) => Ok(value.clone()),
            None => Err(f(&())),
        }
    }

    #[inline]
    fn map_error_to_owned<NewE, F>(self, f: F) -> Result<Self::Source, NewE>
    where
        F: Fn(()) -> NewE,
        NewE: Clone + Debug,
        Self::Source: Clone,
        Self: Sized,
    {
        match self {
            Some(value) => Ok(value),
            None => Err(f(())),
        }
    }
}
