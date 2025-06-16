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
//!
//! # Performance Characteristics
//!
//! - Time Complexity: O(1) for creation and evaluation operations
//! - Space Complexity: O(1) - only stores the wrapped value
//! - Memory Usage: Minimal overhead - uses `#[repr(transparent)]` to ensure the wrapper has the same memory layout as the wrapped type

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
///
/// # Evaluate Laws
///
/// Value satisfies the following laws:
///
/// 1. **Idempotence**: Evaluating multiple times produces the same result
///    ```rust
///    # use rustica::datatypes::wrapper::value::Value;
///    # use rustica::traits::evaluate::Evaluate;
///    let value = Value::new(42);
///    assert_eq!(value.evaluate(), value.evaluate());
///    ```
///
/// 2. **Referential Transparency**: Replacing a Value with its evaluated result doesn't change behavior
///    ```rust
///    # use rustica::datatypes::wrapper::value::Value;
///    # use rustica::traits::evaluate::Evaluate;
///    let value = Value::new(42);
///    let result = value.evaluate();
///    
///    // These should be equivalent operations:
///    let result1 = value.evaluate() + 1;
///    let result2 = result + 1;
///    assert_eq!(result1, result2);
///    ```
///
/// 3. **Identity Law**: Evaluating a pure value should return that value unchanged
///    ```rust
///    # use rustica::datatypes::wrapper::value::Value;
///    # use rustica::traits::evaluate::Evaluate;
///    # use rustica::traits::identity::Identity;
///    let original = 42;
///    let value = Value::new(original.clone());
///    assert_eq!(value.evaluate(), original);
///    ```
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
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::wrapper::value::Value;
    ///
    /// let value = Value::new(42);
    /// assert_eq!(value.0, 42);
    /// ```
    ///
    /// # Performance
    ///
    /// - Time Complexity: O(1)
    /// - Space Complexity: O(1)
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
    /// Maps a function over the wrapped value, returning a new Value.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::wrapper::value::Value;
    /// use rustica::traits::functor::Functor;
    ///
    /// let value = Value::new(42);
    /// let doubled = value.fmap(|x| x * 2);
    /// assert_eq!(doubled.0, 84);
    /// ```
    ///
    /// # Performance
    ///
    /// - Time Complexity: O(1) plus the cost of the mapping function
    #[inline]
    fn fmap<U, F>(&self, f: F) -> Self::Output<U>
    where
        F: FnOnce(&Self::Source) -> U,
    {
        Value(f(&self.0))
    }

    /// Maps a function over the wrapped value by consuming it.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::wrapper::value::Value;
    /// use rustica::traits::functor::Functor;
    ///
    /// let value = Value::new(42);
    /// let doubled = value.fmap_owned(|x| x * 2);
    /// assert_eq!(doubled.0, 84);
    /// ```
    ///
    /// # Performance
    ///
    /// - Time Complexity: O(1) plus the cost of the mapping function
    /// - This method may be more efficient than `fmap` as it avoids cloning
    #[inline]
    fn fmap_owned<U, F>(self, f: F) -> Self::Output<U>
    where
        F: FnOnce(Self::Source) -> U,
    {
        Value(f(self.0))
    }
}

impl<T: Clone> Evaluate for Value<T> {
    /// Returns the wrapped value.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::wrapper::value::Value;
    /// use rustica::traits::evaluate::Evaluate;
    ///
    /// let value = Value::new(42);
    /// assert_eq!(value.evaluate(), 42);
    /// ```
    ///
    /// # Performance
    ///
    /// - Time Complexity: O(1) plus the cost of cloning the inner value
    #[inline]
    fn evaluate(&self) -> T {
        self.0.clone()
    }

    /// Consumes the Value and returns the wrapped value.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::wrapper::value::Value;
    /// use rustica::traits::evaluate::Evaluate;
    ///
    /// let value = Value::new(42);
    /// assert_eq!(value.evaluate_owned(), 42);
    /// ```
    ///
    /// # Performance
    ///
    /// - Time Complexity: O(1) - no cloning required
    #[inline]
    fn evaluate_owned(self) -> T {
        self.0
    }
}
