//! Error handling utilities for working with functional programming patterns.
//!
//! This module provides standardized error handling functions that work with
//! the functional programming abstractions in Rustica. It builds on the 
//! functionality in `hkt_utils.rs` but with a focus on error handling patterns.

use crate::datatypes::either::Either;
use crate::datatypes::validated::Validated;
use crate::prelude::HKT;
use std::fmt::Debug;
use smallvec::SmallVec;

/// Error handling trait for types that can fail with a specific error type.
pub trait WithError<E>: HKT {
    /// The successful type
    type Success;
    type ErrorOutput<G>;
    
    /// Maps a function over the error, transforming the error type
    fn fmap_error<F, G>(self, f: F) -> Self::ErrorOutput<G>
    where
        F: Fn(E) -> G,
        G: Clone;

        
    /// Converts this type to a Result
    fn to_result(self) -> Result<Self::Success, E>;
}

impl<T, E: Clone> WithError<E> for Result<T, E> {
    type Success = T;
    type ErrorOutput<G> = Result<T, G>;
    
    fn fmap_error<F, G>(self, f: F) -> Self::ErrorOutput<G>
    where 
        F: FnOnce(E) -> G,
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
        F: FnOnce(E) -> G,
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
    
    fn fmap_error<F, G>(self, mut f: F) -> Self::ErrorOutput<G>
    where 
        F: FnMut(E) -> G,
        G: Clone,
        T: Clone,
    {
        match self {
            Validated::Valid(t) => Validated::Valid(t),
            Validated::SingleInvalid(e) => Validated::SingleInvalid(f(e)),
            Validated::MultiInvalid(es) => {
                let mapped: SmallVec<[G; 4]> = es.into_iter().map(f).collect();
                Validated::MultiInvalid(mapped)
            }
        }
    }
    
    fn to_result(self) -> Result<Self::Success, E> {
        match self {
            Validated::Valid(t) => Ok(t),
            Validated::SingleInvalid(e) => Err(e),
            Validated::MultiInvalid(es) => {
                // Take the first error as the primary error
                if !es.is_empty() {
                    Err(es[0].clone())
                } else {
                    // This should not happen with proper Validated usage
                    panic!("MultiInvalid with no errors")
                }
            }
        }
    }
}

/// Specialization of `sequence_result` for standardizing error handling.
///
/// This function converts a collection of results into a result containing
/// a collection of values, short-circuiting on the first error.
///
/// # Examples
///
/// ```
/// use rustica::utils::error_utils::sequence;
///
/// let results: Vec<Result<i32, &str>> = vec![Ok(1), Ok(2), Ok(3)];
/// assert_eq!(sequence(results), Ok(vec![1, 2, 3]));
///
/// let results: Vec<Result<i32, &str>> = vec![Ok(1), Err("error"), Ok(3)];
/// assert_eq!(sequence(results), Err("error"));
/// ```
#[inline]
pub fn sequence<A, E>(collection: Vec<Result<A, E>>) -> Result<Vec<A>, E> {
    sequence_result(collection)
}

/// Specialization of `traverse_result` for standardizing error handling.
///
/// This function applies a function that might fail to each element of a collection,
/// collecting the results if everything succeeds, or returning the first error.
///
/// # Examples
///
/// ```
/// use rustica::utils::error_utils::traverse;
///
/// let parse_int = |s: &str| s.parse::<i32>().map_err(|_| "parse error");
/// let inputs = vec!["1", "2", "3"];
/// assert_eq!(traverse(inputs, parse_int), Ok(vec![1, 2, 3]));
///
/// let inputs = vec!["1", "not_a_number", "3"];
/// assert_eq!(traverse(inputs, parse_int), Err("parse error"));
/// ```
#[inline]
pub fn traverse<A, B, E, F>(collection: impl IntoIterator<Item = A>, f: F) -> Result<Vec<B>, E>
where
    F: Fn(A) -> Result<B, E>,
{
    traverse_result(collection, f)
}

/// Applies a function that might fail to each element, collecting all errors.
///
/// Unlike `traverse`, this continues processing even after encountering errors,
/// collecting all errors that occur.
///
/// # Examples
///
/// ```
/// use rustica::utils::error_utils::traverse_validated;
/// use rustica::datatypes::validated::Validated;
///
/// let parse_int = |s: &str| s.parse::<i32>().map_err(|_| "parse error");
/// let inputs = vec!["1", "not_a_number", "3", "also_not_a_number"];
/// 
/// let result = traverse_validated(inputs, parse_int);
/// assert!(result.is_invalid());
/// assert_eq!(result.errors().len(), 2);
/// ```
pub fn traverse_validated<A, B, E, F>(
    collection: impl IntoIterator<Item = A>, 
    f: F
) -> Validated<E, Vec<B>>
where
    F: Fn(A) -> Result<B, E>,
    E: Clone,
    B: Clone,
{
    let mut result = Vec::new();
    let mut errors = Vec::new();
    let mut has_errors = false;

    for item in collection {
        match f(item) {
            Ok(b) => result.push(b),
            Err(e) => {
                has_errors = true;
                errors.push(e);
            }
        }
    }

    if has_errors {
        match errors.len() {
            1 => Validated::invalid(errors.remove(0)),
            _ => Validated::invalid_vec(errors),
        }
    } else {
        Validated::valid(result)
    }
}

/// Converts a collection of `WithError` values into a Result.
///
/// This function generalizes the `sequence` function to work with any type
/// that implements the `WithError` trait.
///
/// # Examples
///
/// ```
/// use rustica::utils::error_utils::{sequence_with_error, WithError};
/// use rustica::datatypes::either::Either;
///
/// let results: Vec<Either<&str, i32>> = vec![
///     Either::right(1),
///     Either::right(2),
///     Either::right(3),
/// ];
/// assert_eq!(sequence_with_error(results), Ok(vec![1, 2, 3]));
///
/// let results: Vec<Either<&str, i32>> = vec![
///     Either::right(1),
///     Either::left("error"),
///     Either::right(3),
/// ];
/// assert_eq!(sequence_with_error(results), Err("error"));
/// ```
pub fn sequence_with_error<T, E, C>(collection: Vec<C>) -> Result<Vec<T>, E>
where
    C: WithError<E, Success = T>,
{
    let mut result = Vec::with_capacity(collection.len());
    
    for item in collection {
        match item.to_result() {
            Ok(t) => result.push(t),
            Err(e) => return Err(e),
        }
    }
    
    Ok(result)
}

/// Transforms a Result into an Either.
///
/// This is a convenience function for converting between error handling types.
///
/// # Examples
///
/// ```
/// use rustica::utils::error_utils::result_to_either;
/// use rustica::datatypes::either::Either;
///
/// let ok_result: Result<i32, &str> = Ok(42);
/// assert_eq!(result_to_either(ok_result), Either::right(42));
///
/// let err_result: Result<i32, &str> = Err("error");
/// assert_eq!(result_to_either(err_result), Either::left("error"));
/// ```
#[inline]
pub fn result_to_either<T, E>(result: Result<T, E>) -> Either<E, T> {
    match result {
        Ok(t) => Either::Right(t),
        Err(e) => Either::Left(e),
    }
}

/// Transforms an Either into a Result.
///
/// This is a convenience function for converting between error handling types.
///
/// # Examples
///
/// ```
/// use rustica::utils::error_utils::either_to_result;
/// use rustica::datatypes::either::Either;
///
/// let right: Either<&str, i32> = Either::right(42);
/// assert_eq!(either_to_result(right), Ok(42));
///
/// let left: Either<&str, i32> = Either::left("error");
/// assert_eq!(either_to_result(left), Err("error"));
/// ```
#[inline]
pub fn either_to_result<T, E>(either: Either<E, T>) -> Result<T, E> {
    match either {
        Either::Right(t) => Ok(t),
        Either::Left(e) => Err(e),
    }
}

/// A chainable error handling extension trait.
pub trait ResultExt<T, E> {
    /// Transforms a Result into a Validated.
    fn to_validated(self) -> Validated<E, T>
    where
        E: Clone,
        T: Clone;
        
    /// Transforms a Result into an Either.
    fn to_either(self) -> Either<E, T>;
    
    /// Returns the result or a default value.
    fn unwrap_or_default(self) -> T
    where
        T: Default;
        
    /// Maps both the success and error values of a Result.
    fn bimap<U, F, G, E2>(self, success_map: F, error_map: G) -> Result<U, E2>
    where
        F: FnOnce(T) -> U,
        G: FnOnce(E) -> E2;
}

impl<T, E> ResultExt<T, E> for Result<T, E> {
    #[inline]
    fn to_validated(self) -> Validated<E, T>
    where
        E: Clone,
        T: Clone,
    {
        match self {
            Ok(t) => Validated::valid(t),
            Err(e) => Validated::invalid(e),
        }
    }
    
    #[inline]
    fn to_either(self) -> Either<E, T> {
        result_to_either(self)
    }
    
    #[inline]
    fn unwrap_or_default(self) -> T
    where
        T: Default,
    {
        self.unwrap_or_default()
    }
    
    #[inline]
    fn bimap<U, F, G, E2>(self, success_map: F, error_map: G) -> Result<U, E2>
    where
        F: FnOnce(T) -> U,
        G: FnOnce(E) -> E2,
    {
        match self {
            Ok(t) => Ok(success_map(t)),
            Err(e) => Err(error_map(e)),
        }
    }
}

/// Creates a custom error type with context.
///
/// This is useful for creating specialized error types that carry
/// additional context.
///
/// # Examples
///
/// ```
/// use rustica::utils::error_utils::{AppError, error_with_context};
///
/// let error = error_with_context("File not found", "trying to open config.json");
/// assert_eq!(error.message(), &"File not found");
/// assert_eq!(error.context(), Some(&"trying to open config.json"));
/// ```
#[derive(Debug, Clone)]
pub struct AppError<M, C = ()> {
    message: M,
    context: Option<C>,
}

impl<M, C> AppError<M, C> {
    #[inline]
    pub fn new(message: M) -> Self {
        AppError {
            message,
            context: None,
        }
    }
    
    #[inline]
    pub fn with_context(message: M, context: C) -> Self {
        AppError {
            message,
            context: Some(context),
        }
    }
    
    #[inline]
    pub fn message(&self) -> &M {
        &self.message
    }
    
    #[inline]
    pub fn context(&self) -> Option<&C> {
        self.context.as_ref()
    }
    
    #[inline]
    pub fn map<N, F>(self, f: F) -> AppError<N, C>
    where
        F: FnOnce(M) -> N,
    {
        AppError {
            message: f(self.message),
            context: self.context,
        }
    }
    
    #[inline]
    pub fn map_context<D, F>(self, f: F) -> AppError<M, D>
    where
        F: FnOnce(Option<C>) -> Option<D>,
    {
        AppError {
            message: self.message,
            context: f(self.context),
        }
    }
}

impl<M: Debug, C: Debug> std::fmt::Display for AppError<M, C> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if let Some(ref context) = self.context {
            write!(f, "{:?} (context: {:?})", self.message, context)
        } else {
            write!(f, "{:?}", self.message)
        }
    }
}

impl<M: Debug + Clone, C: Debug + Clone> std::error::Error for AppError<M, C> {}

/// Creates an error with a message.
///
/// This is a convenience function for creating an `AppError`.
///
/// # Examples
///
/// ```
/// use rustica::utils::error_utils::error;
///
/// let error = error("File not found");
/// assert_eq!(*error.message(), "File not found");
/// assert_eq!(error.context(), None::<&()>);
/// ```
#[inline]
pub fn error<M>(message: M) -> AppError<M> {
    AppError::new(message)
}

/// Creates an error with a message and context.
///
/// This is a convenience function for creating an `AppError` with context.
///
/// # Examples
///
/// ```
/// use rustica::utils::error_utils::error_with_context;
///
/// let error = error_with_context("File not found", "trying to open config.json");
/// assert_eq!(error.message(), &"File not found");
/// assert_eq!(error.context(), Some(&"trying to open config.json"));
/// ```
#[inline]
pub fn error_with_context<M, C>(message: M, context: C) -> AppError<M, C> {
    AppError::with_context(message, context)
}

// Sequence implementation for Option
pub fn sequence_option<A>(collection: Vec<Option<A>>) -> Option<Vec<A>> {
    let mut result = Vec::new();

    for item in collection {
        match item {
            Some(a) => result.push(a),
            None => return None,
        }
    }

    Some(result)
}

// Sequence implementation for Result
pub fn sequence_result<A, E>(collection: Vec<Result<A, E>>) -> Result<Vec<A>, E> {
    let mut result = Vec::new();

    for item in collection {
        match item {
            Ok(a) => result.push(a),
            Err(e) => return Err(e),
        }
    }

    Ok(result)
}

// Traverse implementation for Option
pub fn traverse_option<A, B, F>(collection: impl IntoIterator<Item = A>, f: F) -> Option<Vec<B>>
where
    F: Fn(A) -> Option<B>,
{
    let mut result = Vec::new();

    for item in collection {
        match f(item) {
            Some(b) => result.push(b),
            None => return None,
        }
    }

    Some(result)
}

// Traverse implementation for Result
pub fn traverse_result<A, B, E, F>(
    collection: impl IntoIterator<Item = A>,
    f: F,
) -> Result<Vec<B>, E>
where
    F: Fn(A) -> Result<B, E>,
{
    let mut result = Vec::new();

    for item in collection {
        match f(item) {
            Ok(b) => result.push(b),
            Err(e) => return Err(e),
        }
    }

    Ok(result)
}
