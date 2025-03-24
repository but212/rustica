//! # ErrorMapper
//!
//! This module provides the ErrorMapper trait, which allows for mapping between different
//! error types in a monadic context. This is particularly useful for adapting error types
//! when working with different error-handling mechanisms.
//!
//! The ErrorMapper trait complements the MonadError trait by focusing specifically on
//! error type transformation, while MonadError handles the core error management operations.
//!
//! # Examples
//!
//! ```rust
//! use rustica::traits::error_mapper::ErrorMapper;
//! use rustica::traits::monad_error::ErrorMapper as MonadErrorMapper;
//!
//! // String implements Clone so it can be used with ErrorMapper
//! let result: Result<i32, String> = Ok(42);
//! let new_result = result.map_error_to::<String, _>(|e| format!("Error: {}", e));
//! assert_eq!(new_result, Ok(42));
//! ```

use std::fmt::Debug;

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
/// use rustica::traits::error_mapper::ErrorMapper;
/// use rustica::traits::monad_error::ErrorMapper as MonadErrorMapper;
///
/// // String implements Clone so it can be used with ErrorMapper
/// let result: Result<i32, String> = Ok(42);
/// let new_result = result.map_error_to::<String, _>(|e| format!("Error: {}", e));
/// assert_eq!(new_result, Ok(42));
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
