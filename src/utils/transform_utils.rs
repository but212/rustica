//! # Transformation Utilities
//!
//! This module provides utilities for transforming functorial data types and building
//! transformation pipelines. These tools help you work with functors in an ergonomic
//! and composable way.
//!
//! ## Key Features
//!
//! - **Transformation Functions**: Apply transformations to functorial values
//! - **Pipeline Builder**: Build fluent transformation chains with the `Pipeline` type
//! - **Type-Safe Operations**: Leverage Rust's type system for safe transformations
//!
//! The utilities in this module work with any type that implements the `Functor` trait,
//! including standard library types like `Option` and `Result`, and library types
//! like `Either` and `Maybe`.
use crate::prelude::Functor;

// ===== Transformation Functions =====

/// Applies a transformation to all functorial values in a collection.
///
/// This function maps a transformation over each functorial value in the collection,
/// using the `Functor` trait's capabilities.
///
/// # Type Parameters
///
/// * `T`: A type that implements `Functor`
/// * `F`: The transformation function type
/// * `U`: The result type of the transformation
///
/// # Arguments
///
/// * `values`: The collection of functorial values to transform
/// * `f`: The transformation function to apply to the content of each functor
///
/// # Returns
///
/// A new vector containing the transformed functorial values
///
/// # Examples
///
/// ```rust
/// use rustica::utils::transform_utils::transform_all;
/// use rustica::prelude::*;
/// use rustica::datatypes::maybe::Maybe;
///
/// // Create a collection of Maybe values
/// let values: Vec<Maybe<i32>> = vec![
///     Maybe::Just(1),
///     Maybe::Just(2),
///     Maybe::Nothing,
///     Maybe::Just(4)
/// ];
///
/// // Transform the values inside each Maybe
/// let doubles = transform_all(&values, |&x| x * 2);
///
/// // The transformation is applied only to the Just values
/// assert_eq!(doubles[0], Maybe::Just(2));
/// assert_eq!(doubles[1], Maybe::Just(4));
/// assert_eq!(doubles[2], Maybe::Nothing);
/// assert_eq!(doubles[3], Maybe::Just(8));
/// ```
///
/// Works with standard library types too:
///
/// ```rust
/// use rustica::utils::transform_utils::transform_all;
/// use rustica::prelude::*;
///
/// // A collection of Option values
/// let options: Vec<Option<String>> = vec![
///     Some("hello".to_string()),
///     None,
///     Some("world".to_string())
/// ];
///
/// // Transform the values inside each Option
/// let uppercase = transform_all(&options, |s| s.to_uppercase());
///
/// assert_eq!(uppercase[0], Some("HELLO".to_string()));
/// assert_eq!(uppercase[1], None);
/// assert_eq!(uppercase[2], Some("WORLD".to_string()));
/// ```
#[inline]
pub fn transform_all<T, F, U>(values: &[T], f: F) -> Vec<T::Output<U>>
where
    T: Functor,
    F: Fn(&T::Source) -> U + Copy,
    U: Clone,
{
    values.iter().map(|v| v.fmap(f)).collect()
}

/// Applies a transformation to a single optional value.
///
/// This function maps a transformation over the value inside an `Option` functor,
/// preserving the `None` case and transforming the `Some` case.
///
/// # Type Parameters
///
/// * `T`: A type that implements `Functor`
/// * `F`: The transformation function type
/// * `U`: The result type of the transformation
///
/// # Arguments
///
/// * `value`: The optional functorial value to transform
/// * `f`: The transformation function to apply to the content
///
/// # Returns
///
/// An optional transformed functorial value, or `None` if the input was `None`
///
/// # Examples
///
/// ```rust
/// use rustica::utils::transform_utils::transform_chain;
/// use rustica::prelude::*;
/// use rustica::datatypes::maybe::Maybe;
///
/// // Apply a transformation to a Just value
/// let maybe_just: Option<Maybe<i32>> = Some(Maybe::Just(5));
/// let result1 = transform_chain(maybe_just, |&x| x * 2);
/// assert_eq!(result1, Some(Maybe::Just(10)));
///
/// // Apply a transformation to a Nothing value
/// let maybe_nothing: Option<Maybe<i32>> = Some(Maybe::Nothing);
/// let result2 = transform_chain(maybe_nothing, |&x| x * 2);
/// assert_eq!(result2, Some(Maybe::Nothing));
///
/// // When the outer Option is None, the result is None
/// let none: Option<Maybe<i32>> = None;
/// let result3 = transform_chain(none, |&x| x * 2);
/// assert_eq!(result3, None);
/// ```
#[inline]
pub fn transform_chain<T, F, U>(value: Option<T>, f: F) -> Option<T::Output<U>>
where
    T: Functor,
    F: Fn(&T::Source) -> U,
    U: Clone,
{
    value.map(|v| v.fmap(f))
}

// ===== Pipeline Builder =====

/// A pipeline for building chains of transformations on functorial values.
///
/// This type provides a fluent interface for applying a sequence of transformations
/// to a functorial value. It wraps the value and allows chaining transformations
/// before finally extracting the result.
///
/// # Type Parameters
///
/// * `T`: The type of the functorial value in the pipeline
///
/// # Examples
///
/// ```rust
/// use rustica::utils::transform_utils::Pipeline;
/// use rustica::prelude::*;
///
/// // Create a pipeline with an Option value
/// let pipeline = Pipeline::new(Some(5));
///
/// // Apply a series of transformations
/// let result = pipeline
///     .map(|&x| x * 2)      // Double the value
///     .map(|x| x.to_string()) // Convert to string
///     .extract();
///
/// assert_eq!(result, Some("10".to_string()));
///
/// // Works with Either as well
/// use rustica::datatypes::either::Either;
///
/// let err_pipeline = Pipeline::new(Either::<&str, i32>::left("error"));
/// let err_result = err_pipeline
///     .map(|&x| x * 2)
///     .extract();
///
/// assert_eq!(err_result, Either::left("error"));
///
/// let ok_pipeline = Pipeline::new(Either::<&str, i32>::right(7));
/// let ok_result = ok_pipeline
///     .map(|&x| x * 2)
///     .extract();
///
/// assert_eq!(ok_result, Either::right(14));
/// ```
#[repr(transparent)]
#[derive(Clone)]
pub struct Pipeline<T>(T);

impl<T> Pipeline<T> {
    /// Creates a new pipeline with the given functorial value.
    ///
    /// # Arguments
    ///
    /// * `value`: The initial functorial value for the pipeline
    ///
    /// # Returns
    ///
    /// A new pipeline containing the value
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::utils::transform_utils::Pipeline;
    /// use rustica::datatypes::maybe::Maybe;
    ///
    /// // Create a pipeline with a Maybe value
    /// let pipeline: Pipeline<Maybe<i32>> = Pipeline::new(Maybe::Just(42));
    ///
    /// // Create a pipeline with an Option value
    /// let option_pipeline: Pipeline<Option<String>> = Pipeline::new(Some("hello".to_string()));
    /// ```
    #[inline]
    pub fn new(value: T) -> Self {
        Pipeline(value)
    }

    /// Extracts the final value from the pipeline.
    ///
    /// This method returns the transformed value after all pipeline operations
    /// have been applied.
    ///
    /// # Returns
    ///
    /// The final transformed functorial value
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::utils::transform_utils::Pipeline;
    /// use rustica::prelude::*;
    ///
    /// // Create and extract from a pipeline
    /// let result = Pipeline::new(Some(10))
    ///     .extract();
    ///
    /// assert_eq!(result, Some(10));
    /// ```
    #[inline]
    pub fn extract(self) -> T {
        self.0
    }
}

impl<T: Functor> Pipeline<T> {
    /// Maps a transformation over the inner value, taking ownership.
    ///
    /// This method applies a transformation to the content of the functorial value
    /// using the owned version of `fmap`. This is useful when you don't need to
    /// preserve the original value.
    ///
    /// # Type Parameters
    ///
    /// * `F`: The transformation function type
    /// * `U`: The result type of the transformation
    ///
    /// # Arguments
    ///
    /// * `f`: The transformation function to apply
    ///
    /// # Returns
    ///
    /// A new pipeline containing the transformed value
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::utils::transform_utils::Pipeline;
    /// use rustica::prelude::*;
    ///
    /// // Transform with map_owned
    /// let result = Pipeline::new(Some(5))
    ///     .map_owned(|x| x * 3)  // Using value by value
    ///     .extract();
    ///
    /// assert_eq!(result, Some(15));
    /// ```
    #[inline]
    pub fn map_owned<F, U>(self, f: F) -> Pipeline<T::Output<U>>
    where
        F: Fn(T::Source) -> U,
        U: Clone,
    {
        Pipeline(self.0.fmap_owned(f))
    }

    /// Maps a transformation over the inner value, operating by reference.
    ///
    /// This method applies a transformation to the content of the functorial value
    /// using the reference version of `fmap`. This preserves the pattern of
    /// operating on values by reference.
    ///
    /// # Type Parameters
    ///
    /// * `F`: The transformation function type
    /// * `U`: The result type of the transformation
    ///
    /// # Arguments
    ///
    /// * `f`: The transformation function to apply
    ///
    /// # Returns
    ///
    /// A new pipeline containing the transformed value
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::utils::transform_utils::Pipeline;
    /// use rustica::prelude::*;
    /// use rustica::datatypes::either::Either;
    ///
    /// // Transform with map
    /// let result = Pipeline::new(Either::<String, i32>::right(7))
    ///     .map(|&x| x.to_string())  // Using value by reference
    ///     .extract();
    ///
    /// assert_eq!(result, Either::<String, String>::right("7".to_string()));
    /// ```
    #[inline]
    pub fn map<F, U>(self, f: F) -> Pipeline<T::Output<U>>
    where
        F: Fn(&T::Source) -> U,
        U: Clone,
    {
        Pipeline(self.0.fmap(f))
    }
}

impl<T> IntoIterator for Pipeline<T>
where
    T: IntoIterator,
{
    type Item = T::Item;
    type IntoIter = T::IntoIter;

    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}
