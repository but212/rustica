//! # Transform Utilities
//!
//! This module provides utility functions for working with types that implement the `Transform` trait.
//! These utilities make it easier to build data transformation pipelines and handle common operations
//! on transformable types.
//!
//! ## Usage Examples
//!
//! ```rust
//! use rustica::traits::hkt::HKT;
//! use rustica::traits::transform::Transform;
//! use rustica::utils::transform_utils::{transform_all, transform_chain};
//!
//! // Using transform_all to transform a vector of options
//! let values: Vec<Option<i32>> = vec![Some(1), Some(2), Some(3)];
//! let doubled: Vec<Option<i32>> = transform_all(&values, |x| x * 2);
//! assert_eq!(doubled, vec![Some(2), Some(4), Some(6)]);
//!
//! // Using transform_chain for optional chaining
//! let value: Option<i32> = Some(42);
//! let result = transform_chain(Some(value), |x| x.to_string());
//! assert_eq!(result, Some(Some("42".to_string())));
//! ```

use crate::prelude::Transform;

/// Transforms all values in a collection using the provided function.
///
/// This utility function applies a transformation to each element in a collection
/// of transformable types.
///
/// # Type Parameters
///
/// * `T`: A type that implements `Transform`
/// * `F`: A function type that transforms `&T::Source` into `U`
/// * `U`: The output type of the transformation
///
/// # Arguments
///
/// * `values`: A vector of transformable values
/// * `f`: A function to apply to each value
///
/// # Returns
///
/// A vector of transformed values
///
/// # Examples
///
/// ```rust
/// use rustica::traits::hkt::HKT;
/// use rustica::traits::transform::Transform;
/// use rustica::utils::transform_utils::transform_all;
///
/// let options: Vec<Option<i32>> = vec![Some(1), Some(2), None, Some(3)];
/// let doubled: Vec<Option<i32>> = transform_all(&options, |x| x * 2);
/// assert_eq!(doubled, vec![Some(2), Some(4), None, Some(6)]);
/// ```
#[inline]
pub fn transform_all<T, F, U>(values: &Vec<T>, f: F) -> Vec<T::Output<U>>
where
    T: Transform,
    F: Fn(&T::Source) -> U + Copy,
    U: Clone,
{
    values.iter().map(|v| v.transform(f)).collect()
}

/// Applies a transformation to an optional value.
///
/// This function creates a safe chaining operation for transformable types
/// wrapped in an Option.
///
/// # Type Parameters
///
/// * `T`: A type that implements `Transform`
/// * `F`: A function type that transforms `&T::Source` into `U`
/// * `U`: The output type of the transformation
///
/// # Arguments
///
/// * `value`: An optional transformable value
/// * `f`: A function to apply to the value if present
///
/// # Returns
///
/// An optional transformed value
///
/// # Examples
///
/// ```rust
/// use rustica::traits::hkt::HKT;
/// use rustica::traits::transform::Transform;
/// use rustica::utils::transform_utils::transform_chain;
///
/// let value: Option<Option<i32>> = Some(Some(42));
/// let result = transform_chain(value, |x| x.to_string());
/// assert_eq!(result, Some(Some("42".to_string())));
///
/// let empty: Option<Option<i32>> = None;
/// let result = transform_chain(empty, |x| x.to_string());
/// assert_eq!(result, None);
/// ```
#[inline]
pub fn transform_chain<T, F, U>(value: Option<T>, f: F) -> Option<T::Output<U>>
where
    T: Transform,
    F: Fn(&T::Source) -> U,
    U: Clone,
{
    value.map(|v| v.transform(f))
}

/// Data processing pipeline that supports transformable types.
///
/// This structure makes it easy to chain multiple transformations together
/// in a readable way.
///
/// # Type Parameters
///
/// * `T`: A type that implements `Transform`
///
/// # Examples
///
/// ```rust
/// use rustica::traits::hkt::HKT;
/// use rustica::traits::transform::Transform;
/// use rustica::utils::transform_utils::Pipeline;
///
/// // Create a pipeline with an Option<i32>
/// let pipeline = Pipeline::new(Some(42));
///
/// // Chain transformations
/// let result = pipeline
///     .map(|x| x * 2)
///     .map(|x| x.to_string())
///     .map(|s| s.to_owned() + "!")
///     .extract();
///
/// assert_eq!(result, Some("84!".to_string()));
/// ```
pub struct Pipeline<T>(T);

impl<T> Pipeline<T> {
    /// Creates a new pipeline with the given value.
    ///
    /// # Arguments
    ///
    /// * `value`: The initial value for the pipeline
    ///
    /// # Returns
    ///
    /// A new pipeline containing the value
    #[inline]
    pub fn new(value: T) -> Self {
        Pipeline(value)
    }

    /// Extracts the final value from the pipeline.
    ///
    /// # Returns
    ///
    /// The transformed value
    #[inline]
    pub fn extract(self) -> T {
        self.0
    }
}

impl<T: Transform> Pipeline<T> {
    /// Applies a transformation to the value in the pipeline.
    ///
    /// # Type Parameters
    ///
    /// * `F`: A function type that transforms `T::Source` into `U`
    /// * `U`: The output type of the transformation
    ///
    /// # Arguments
    ///
    /// * `f`: A function to apply to the value
    ///
    /// # Returns
    ///
    /// A new pipeline containing the transformed value
    #[inline]
    pub fn map_owned<F, U>(self, f: F) -> Pipeline<T::Output<U>>
    where
        F: Fn(T::Source) -> U,
        U: Clone,
    {
        Pipeline(self.0.transform_owned(f))
    }

    /// Applies a transformation to the value in the pipeline using a reference.
    ///
    /// # Type Parameters
    ///
    /// * `F`: A function type that transforms `&T::Source` into `U`
    /// * `U`: The output type of the transformation
    ///
    /// # Arguments
    ///
    /// * `f`: A function to apply to a reference of the value
    ///
    /// # Returns
    ///
    /// A new pipeline containing the transformed value
    #[inline]
    pub fn map<F, U>(self, f: F) -> Pipeline<T::Output<U>>
    where
        F: Fn(&T::Source) -> U,
        U: Clone,
    {
        Pipeline(self.0.transform(f))
    }
}
