//! Transform trait defines the ability to transform data within a higher-kinded type.
//!
//! This trait is a fundamental component for mapping operations in functional programming,
//! providing a way to transform the inner values of container types without changing the
//! container structure itself.
//!
//! # Mathematical Definition
//!
//! The transform operation corresponds to the functor laws from category theory,
//! which describe how to map between categories while preserving structure.
//!
//! # Relationship to other traits
//!
//! Transform is a foundational trait for implementing the Functor type class:
//!
//! ```text
//! Transform -> Functor -> Applicative -> Monad
//! ```
//!
//! # Usage
//!
//! The Transform trait is used to transform the contents of higher-kinded types.
//! For example, it can be used to convert an `Option<i32>` to an `Option<String>`.

use crate::traits::hkt::HKT;

/// A type that can transform its inner values without changing its structure.
///
/// The Transform trait defines methods for applying a function to the inner values
/// of a container type, returning a new container with transformed values.
///
/// # Type Parameters
///
/// * `F` - The function type that transforms values
/// * `NewType` - The type of the transformed values
///
/// # Examples
///
/// ```rust
/// use rustica::traits::hkt::HKT;
/// use rustica::traits::transform::Transform;
///
/// // A simple container type
/// struct Container<T>(T);
///
/// impl<T> HKT for Container<T> {
///     type Source = T;
///     type Output<NewType> = Container<NewType>;
/// }
///
/// impl<T> Transform for Container<T> {
///     fn transform<F, NewType>(&self, f: F) -> Self::Output<NewType>
///     where
///         F: Fn(&Self::Source) -> NewType,
///     {
///         Container(f(&self.0))
///     }
///
///     fn transform_owned<F, NewType>(self, f: F) -> Self::Output<NewType>
///     where
///         F: Fn(Self::Source) -> NewType,
///     {
///         Container(f(self.0))
///     }
/// }
///
/// // Using the transform methods
/// let container = Container(42);
/// let transformed = container.transform(|x: &i32| x.to_string());
/// assert_eq!(transformed.0, "42");
/// ```
pub trait Transform: HKT {
    /// Transforms the inner value using a function, without consuming the container.
    ///
    /// # Type Parameters
    ///
    /// * `F` - The function type
    /// * `NewType` - The type of the transformed value
    ///
    /// # Parameters
    ///
    /// * `f` - A function that takes a reference to the inner value and returns a new value
    ///
    /// # Returns
    ///
    /// A new container with the transformed value
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::traits::transform::Transform;
    ///
    /// // Using transform with Option
    /// let some_value: Option<i32> = Some(42);
    /// let transformed: Option<String> = some_value.transform(|x: &i32| x.to_string());
    /// assert_eq!(transformed, Some("42".to_string()));
    ///
    /// // Using transform with None
    /// let none_value: Option<i32> = None;
    /// let transformed: Option<String> = none_value.transform(|x: &i32| x.to_string());
    /// assert_eq!(transformed, None);
    /// ```
    fn transform<F, NewType>(&self, f: F) -> Self::Output<NewType>
    where
        F: Fn(&Self::Source) -> NewType;

    /// Transforms the inner value using a function, consuming the container.
    ///
    /// # Type Parameters
    ///
    /// * `F` - The function type
    /// * `NewType` - The type of the transformed value
    ///
    /// # Parameters
    ///
    /// * `f` - A function that takes ownership of the inner value and returns a new value
    ///
    /// # Returns
    ///
    /// A new container with the transformed value
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::traits::transform::Transform;
    ///
    /// // Using transform_owned with Option
    /// let some_value: Option<i32> = Some(42);
    /// let transformed: Option<String> = some_value.transform_owned(|x: i32| x.to_string());
    /// assert_eq!(transformed, Some("42".to_string()));
    ///
    /// // Using transform_owned with None
    /// let none_value: Option<i32> = None;
    /// let transformed: Option<String> = none_value.transform_owned(|x: i32| x.to_string());
    /// assert_eq!(transformed, None);
    /// ```
    fn transform_owned<F, NewType>(self, f: F) -> Self::Output<NewType>
    where
        F: Fn(Self::Source) -> NewType;
}

/// Extension methods for types that implement `Transform`.
///
/// This trait provides additional utility methods for transforming values.
///
/// # Examples
///
/// ```rust
/// use rustica::traits::transform::{Transform, TransformExt};
///
/// let some_value: Option<i32> = Some(42);
///
/// // Using map_or with a default value
/// let result_with_default: String = some_value.map_or("default".to_string(), |x: i32| x.to_string());
/// assert_eq!(result_with_default, "42");
///
/// // For None values, the default is used
/// let none_value: Option<i32> = None;
/// let result_with_default: String = none_value.map_or("default".to_string(), |x: i32| x.to_string());
/// assert_eq!(result_with_default, "default");
/// ```
pub trait TransformExt: Transform {
    /// Returns the transformed value or a default value if the container is empty.
    ///
    /// # Type Parameters
    ///
    /// * `B` - The type of the transformed value and default value
    /// * `F` - The function type
    ///
    /// # Parameters
    ///
    /// * `default` - The default value to return if the container is empty
    /// * `f` - A function that transforms the inner value
    ///
    /// # Returns
    ///
    /// The transformed value or the default value
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::traits::transform::{Transform, TransformExt};
    ///
    /// let some_value: Option<i32> = Some(42);
    /// let result = some_value.map_or("default".to_string(), |x: i32| x.to_string());
    /// assert_eq!(result, "42");
    ///
    /// let none_value: Option<i32> = None;
    /// let result = none_value.map_or("default".to_string(), |x: i32| x.to_string());
    /// assert_eq!(result, "default");
    /// ```
    fn map_or<B, F>(&self, default: B, f: F) -> B
    where
        F: Fn(&Self::Source) -> B;

    /// Returns the transformed value or calls a default function if the container is empty.
    ///
    /// # Type Parameters
    ///
    /// * `B` - The type of the transformed value
    /// * `D` - The default function type
    /// * `F` - The transform function type
    ///
    /// # Parameters
    ///
    /// * `default_fn` - A function that returns a default value
    /// * `f` - A function that transforms the inner value
    ///
    /// # Returns
    ///
    /// The transformed value or the result of the default function
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::traits::transform::{Transform, TransformExt};
    ///
    /// let some_value: Option<i32> = Some(42);
    ///
    /// // Using map_or_else with a default value
    /// let result = some_value.map_or_else(
    ///     || "default".to_string(),
    ///     |x: i32| x.to_string()
    /// );
    /// assert_eq!(result, "42");
    ///
    /// // For None values, the default is used
    /// let none_value: Option<i32> = None;
    /// let result = none_value.map_or_else(
    ///     || "default".to_string(),
    ///     |x: i32| x.to_string()
    /// );
    /// assert_eq!(result, "default");
    /// ```
    fn map_or_else<B, D, F>(&self, default_fn: D, f: F) -> B
    where
        D: FnOnce() -> B,
        F: Fn(&Self::Source) -> B;

    /// Returns the transformed value or calls a default function if the container is empty,
    /// consuming the container.
    ///
    /// # Type Parameters
    ///
    /// * `B` - The type of the transformed value
    /// * `D` - The default function type
    /// * `F` - The transform function type
    ///
    /// # Parameters
    ///
    /// * `default_fn` - A function that returns a default value
    /// * `f` - A function that transforms the inner value
    ///
    /// # Returns
    ///
    /// The transformed value or the result of the default function
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::traits::transform::{Transform, TransformExt};
    ///
    /// let some_value: Option<i32> = Some(42);
    ///
    /// // Using map_or_else with a default value
    /// let result = some_value.map_or_else(
    ///     || "default".to_string(),
    ///     |x: i32| x.to_string()
    /// );
    /// assert_eq!(result, "42");
    ///
    /// // For None values, the default is used
    /// let none_value: Option<i32> = None;
    /// let result = none_value.map_or_else(
    ///     || "default".to_string(),
    ///     |x: i32| x.to_string()
    /// );
    /// assert_eq!(result, "default");
    /// ```
    fn map_or_else_owned<B, D, F>(self, default_fn: D, f: F) -> B
    where
        D: FnOnce() -> B,
        F: FnOnce(Self::Source) -> B;
}

// Implementations for standard types
impl<T> Transform for Option<T> {
    fn transform<F, NewType>(&self, f: F) -> Self::Output<NewType>
    where
        F: Fn(&Self::Source) -> NewType,
    {
        self.as_ref().map(f)
    }

    fn transform_owned<F, NewType>(self, f: F) -> Self::Output<NewType>
    where
        F: Fn(Self::Source) -> NewType,
    {
        self.map(f)
    }
}

impl<T, E: Clone> Transform for Result<T, E> {
    fn transform<F, NewType>(&self, f: F) -> Self::Output<NewType>
    where
        F: Fn(&Self::Source) -> NewType,
    {
        match self {
            Ok(value) => Ok(f(value)),
            Err(e) => Err(e.clone()),
        }
    }

    fn transform_owned<F, NewType>(self, f: F) -> Self::Output<NewType>
    where
        F: Fn(Self::Source) -> NewType,
    {
        self.map(f)
    }
}

impl<T> Transform for Vec<T> {
    fn transform<F, NewType>(&self, f: F) -> Self::Output<NewType>
    where
        F: Fn(&Self::Source) -> NewType,
    {
        self.iter().map(f).collect()
    }

    fn transform_owned<F, NewType>(self, f: F) -> Self::Output<NewType>
    where
        F: Fn(Self::Source) -> NewType,
    {
        self.into_iter().map(f).collect()
    }
}

impl<T> Transform for std::marker::PhantomData<T> {
    fn transform<F, NewType>(&self, _f: F) -> Self::Output<NewType>
    where
        F: Fn(&Self::Source) -> NewType,
    {
        std::marker::PhantomData
    }

    fn transform_owned<F, NewType>(self, _f: F) -> Self::Output<NewType>
    where
        F: Fn(Self::Source) -> NewType,
    {
        std::marker::PhantomData
    }
}
