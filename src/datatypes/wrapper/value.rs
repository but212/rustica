//! A simple value wrapper that can be evaluated.
//!
//! This module provides the `Value` type, which wraps a value
//! in a structure that implements the `Evaluate` trait.
//!
//! # Examples
//!
//! ```rust
//! use rustica::traits::evaluate::{Evaluate, EvaluateExt};
//! use rustica::datatypes::wrapper::value::Value;
//!
//! // Create a wrapped value
//! let value = Value::new(42);
//!
//! // Evaluate the value
//! assert_eq!(value.evaluate(), 42);
//!
//! // Using extension methods
//! let doubled: i32 = value.fmap_evaluate(|x| x * 2);
//! assert_eq!(doubled, 84);
//!
//! // Chain evaluations
//! let result: String = value.bind_evaluate(|x| {
//!     Value::new(x.to_string())
//! });
//! assert_eq!(result, "42");
//! ```

use crate::traits::evaluate::Evaluate;
use crate::traits::functor::Functor;
use crate::traits::hkt::HKT;
use crate::traits::identity::Identity;

/// A simple value container that just returns its wrapped value when evaluated.
///
/// This type is useful for:
/// - Creating constant values that adhere to the Evaluate interface
/// - Converting regular values to work with evaluation pipelines
/// - Unifying different evaluation sources in a common interface
///
/// # Type Parameters
///
/// * `T` - The type of the contained value
#[repr(transparent)]
pub struct Value<T>(pub T);

impl<T> Value<T> {
    /// Creates a new Value wrapper.
    ///
    /// # Parameters
    ///
    /// * `value` - The value to wrap
    ///
    /// # Returns
    ///
    /// A new `Value` instance containing the given value
    #[inline]
    pub fn new(value: T) -> Self {
        Value(value)
    }
}

impl<T> HKT for Value<T> {
    type Source = T;
    type Output<U> = Value<U>;
}

impl<T: Clone> Identity for Value<T> {
    fn value(&self) -> &Self::Source {
        &self.0
    }

    fn into_value(self) -> Self::Source {
        self.0
    }

    fn pure_identity<A>(value: A) -> Self::Output<A>
    where
        Self::Output<A>: Identity,
        A: Clone,
    {
        Value(value)
    }
}

impl<T: Clone> Functor for Value<T> {
    #[inline]
    fn fmap<U, F>(&self, f: F) -> Self::Output<U>
    where
        F: FnOnce(&Self::Source) -> U,
    {
        Value(f(&self.0))
    }

    #[inline]
    fn fmap_owned<U, F>(self, f: F) -> Self::Output<U>
    where
        F: FnOnce(Self::Source) -> U,
    {
        Value(f(self.0))
    }
}

impl<T: Clone> Evaluate for Value<T> {
    #[inline]
    fn evaluate(&self) -> T {
        self.0.clone()
    }

    #[inline]
    fn evaluate_owned(self) -> T {
        self.0
    }
}
