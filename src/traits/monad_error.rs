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
//!    m.catch(|e| throw(e)) == m
//!    ```
//!    Catching with re-throw as the handler should be a no-op.
//!
//! 3. Associativity Catch Law:
//!    ```text
//!    m.catch(h1).catch(h2) == m.catch(|e| h1(e).catch(h2))
//!    ```
//!    Nested catches can be rewritten as a single catch with a composed handler.
//!
//! # Examples
//!
//! ```rust
//! use rustica::traits::monad_error::MonadError;
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
//! let success_result: Result<i32, AppError> = Result::<i32, AppError>::pure(42);
//! let error_result: Result<i32, AppError> = Result::<i32, AppError>::throw::<i32>(AppError {
//!     message: "Item not found".to_string(),
//!     code: 404,
//! });
//!
//! // Catching errors
//! let handled = error_result.catch(|e| {
//!     if e.code == 404 {
//!         Ok(0)  // Default value for not found
//!     } else {
//!         Err(e) // Pass through other errors
//!     }
//! });
//!
//! assert_eq!(handled, Ok(0));
//! ```
use crate::traits::monad::Monad;

/// A trait for monads that can handle errors, extending the basic Monad trait.
///
/// MonadError provides operations for throwing errors and catching errors within
/// a monadic context. It allows for robust error handling while maintaining the
/// benefits of monadic computation chains.
///
/// # Type Parameters
/// * `E`: The error type that can be thrown and caught (no additional constraints required)
///
/// # Category Theory
///
/// In category theory, MonadError represents a monad with additional structure for error handling.
/// The error type `E` doesn't need to satisfy any particular constraints beyond what's required
/// for the specific operations being performed.
///
/// # Laws
/// For a valid MonadError implementation, the following laws must hold:
///
/// 1. Left Catch Law:
///    throw(e).catch(h) == h(&e)
///    Catching an error that was just thrown should be equivalent to just handling that error.
///
/// 2. Right Catch Law:
///    m.catch(|e| throw(e)) == m
///    Catching with re-throw as the handler should be a no-op.
///
/// 3. Associativity Catch Law:
///    m.catch(h1).catch(h2) == m.catch(e -> h1(e).catch(h2))
///    Nested catches can be rewritten as a single catch with a composed handler.
pub trait MonadError<E>: Monad {
    /// Creates a new instance in an error state.
    ///
    /// This is the equivalent of throwing an exception in languages with exceptions.
    /// In category theory, this corresponds to the η (eta) transformation for the error case.
    ///
    /// # Type Parameters
    /// * `T`: The type of value that would be contained in a successful result
    ///
    /// # Parameters
    /// * `error`: The error value to throw
    ///
    /// # Returns
    /// A new monadic value in an error state
    fn throw<T>(error: E) -> Self::Output<T>;

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
    fn catch<F>(self, f: F) -> Self::Output<Self::Source>
    where
        F: FnOnce(E) -> Self::Output<Self::Source>;
}

// Implementation for Result
impl<T, E: Clone + std::fmt::Debug> MonadError<E> for Result<T, E> {
    #[inline]
    fn throw<U>(error: E) -> Self::Output<U> {
        Err(error)
    }

    #[inline]
    fn catch<F>(self, f: F) -> Self::Output<Self::Source>
    where
        F: FnOnce(E) -> Self::Output<Self::Source>,
    {
        match self {
            Ok(value) => Ok(value),
            Err(error) => f(error),
        }
    }
}

// Add implementations for Option, treating None as an error
impl<T> MonadError<()> for Option<T> {
    #[inline]
    fn throw<U>(_error: ()) -> Self::Output<U> {
        None
    }

    #[inline]
    fn catch<F>(self, f: F) -> Self::Output<Self::Source>
    where
        F: FnOnce(()) -> Self::Output<Self::Source>,
    {
        match self {
            Some(value) => Some(value),
            None => f(()),
        }
    }
}

#[cfg(test)]
mod unit_tests {
    use super::MonadError;

    #[test]
    fn monad_error_laws_hold() {
        let thrown: Result<i32, String> = Result::<i32, String>::throw("err".to_string());
        assert_eq!(
            thrown.catch(|e| if e == "err" { Ok(42) } else { Err(e) }),
            Ok(42)
        );
        let value: Result<i32, String> = Ok(10);
        assert_eq!(
            value.clone().catch(|e| Result::<i32, String>::throw(e)),
            value
        );
        let thrown_none: Option<i32> = Option::<i32>::throw::<i32>(());
        assert_eq!(thrown_none, None);
        assert_eq!(None::<i32>.catch(|_| Some(0)), Some(0));
    }
}
