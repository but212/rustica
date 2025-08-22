//! # Value
//!
//! A simple value wrapper that can be evaluated.
//!
//! This module provides the `Value` type, which wraps a value
//! in a structure that implements the `Evaluate` trait.
//!
//! ## Functional Programming Context
//!
//! In functional programming, `Value<T>` represents the identity functor -
//! the simplest context that wraps a value without adding effects. It serves as:
//!
//! - A minimal implementation of various type classes
//! - A way to lift plain values into evaluatable contexts
//! - A building block for more complex functional patterns
//!
//! ## Type Class Laws
//!
//! ### Evaluate Laws
//!
//! `Value<T>` satisfies these laws:
//!
//! - **Idempotence**: `value.evaluate() == value.evaluate()`
//!   - Multiple evaluations of the same value produce the same result.
//!
//! - **Referential Transparency**: Replacing a `Value` with its evaluated result preserves behavior
//!   - For any function `f` and value `v`, `f(value.evaluate())` is equivalent to `f(v)`
//!     where `v` is the inner wrapped value.
//!
//! - **Identity**: `Value::new(x).evaluate() == x`
//!   - Wrapping a value and then evaluating it returns the original value.
//!
//! ### Functor Laws
//!
//! `Value<T>` satisfies the functor laws:
//!
//! - **Identity**: `value.fmap(|x| x) == value`
//!   - Mapping the identity function over a `Value` returns the original `Value`.
//!
//! - **Composition**: `value.fmap(f).fmap(g) == value.fmap(|x| g(f(x)))`
//!   - Mapping two functions in sequence is equivalent to mapping their composition.
//!
//! ## Performance Characteristics
//!
//! - **Time Complexity**: O(1) for creation and evaluation operations
//! - **Space Complexity**: O(1) - only stores the wrapped value
//! - **Memory Usage**: Zero overhead - uses `#[repr(transparent)]` for identical memory layout
//! - **Borrowing**: Supports both owned and borrowed access patterns
//!
//! ## Type Class Implementations
//!
//! `Value<T>` implements several type classes:
//!
//! - `Evaluate`: Returns the contained value
//! - `Functor`: Maps functions over the contained value
//! - `Identity`: Provides identity operations
//! - `HKT`: Higher-kinded type representation
//!
//! ## Quick Start
//!
//! ```rust
//! use rustica::datatypes::wrapper::value::Value;
//! use rustica::traits::{evaluate::Evaluate, functor::Functor};
//!
//! // Create a Value wrapper
//! let value = Value::new(42);
//!
//! // Evaluate to get the wrapped value
//! assert_eq!(value.evaluate(), 42);
//! assert_eq!(value.evaluate_owned(), 42);
//!
//! // Transform the value using Functor
//! let doubled = value.fmap(|x| x * 2);
//! assert_eq!(doubled.evaluate(), 84);
//!
//! // Values preserve their wrapped content
//! let text = Value::new("hello");
//! let uppercased = text.fmap(|s| s.to_uppercase());
//! assert_eq!(uppercased.evaluate(), "HELLO");
//! ```
//!
//! ## Documentation Notes
//!
//! For detailed practical examples demonstrating the type class laws, usage patterns, and
//! performance characteristics, please refer to the function-level documentation of the
//! relevant methods such as `evaluate`, `evaluate_owned`, `fmap`, and others.

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
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
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
    /// Returns a reference to the contained value without consuming the wrapper.
    ///
    /// # Performance
    ///
    /// - **Time Complexity**: O(1) - just returns a reference
    /// - **Memory Usage**: No additional memory allocation
    /// - **Borrowing**: Returns a borrowed reference to the internal value
    ///
    /// # Type Class Laws
    ///
    /// ## Value Law
    ///
    /// ```rust
    /// use rustica::datatypes::wrapper::value::Value;
    /// use rustica::traits::identity::Identity;
    ///
    /// // For any Value(x): *value() should equal x
    /// fn verify_value_law<T: Clone + PartialEq>(x: T) -> bool {
    ///     let wrapped = Value(x.clone());
    ///     *wrapped.value() == x
    /// }
    ///
    /// assert!(verify_value_law(42));
    /// assert!(verify_value_law("hello".to_string()));
    /// ```
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::wrapper::value::Value;
    /// use rustica::traits::identity::Identity;
    ///
    /// let value = Value::new(42);
    /// assert_eq!(*value.value(), 42);
    ///
    /// // The original wrapper is still available after using value()
    /// let doubled = *value.value() * 2;
    /// assert_eq!(doubled, 84);
    /// assert_eq!(*value.value(), 42);  // Original value is unchanged
    /// ```
    fn value(&self) -> &Self::Source {
        &self.0
    }

    /// Consumes the wrapper and returns the contained value.
    ///
    /// # Performance
    ///
    /// - **Time Complexity**: O(1) - simply unwraps the value
    /// - **Memory Usage**: No additional memory allocation
    /// - **Ownership**: Transfers ownership of the internal value to the caller
    ///
    /// # Type Class Laws
    ///
    /// ## Into Value Law
    ///
    /// ```rust
    /// use rustica::datatypes::wrapper::value::Value;
    /// use rustica::traits::identity::Identity;
    ///
    /// // For any Value(x): into_value() should equal x
    /// fn verify_into_value_law<T: Clone + PartialEq>(x: T) -> bool {
    ///     let wrapped = Value(x.clone());
    ///     wrapped.into_value() == x
    /// }
    ///
    /// assert!(verify_into_value_law(42));
    /// assert!(verify_into_value_law("hello".to_string()));
    /// ```
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::wrapper::value::Value;
    /// use rustica::traits::identity::Identity;
    ///
    /// let value = Value::new(42);
    /// let unwrapped = value.into_value();
    ///
    /// assert_eq!(unwrapped, 42);
    /// // Note that value is consumed and can no longer be used
    /// ```
    fn into_value(self) -> Self::Source {
        self.0
    }

    /// Creates a new Value wrapper containing the provided value.
    ///
    /// This is the "lifting" function that introduces a value into the Value context.
    ///
    /// # Performance
    ///
    /// - **Time Complexity**: O(1) - simply wraps the value
    /// - **Memory Usage**: Minimal overhead for the Value wrapper
    /// - **Ownership**: Takes ownership of the value parameter
    ///
    /// # Type Class Laws
    ///
    /// ## Pure Identity Law
    ///
    /// ```rust
    /// use rustica::datatypes::wrapper::value::Value;
    /// use rustica::traits::identity::Identity;
    ///
    /// // For any x: pure_identity(x) should create a valid Value(x)
    /// fn verify_pure_identity_law<T: Clone + PartialEq>(x: T) -> bool {
    ///     let wrapped = Value::<()>::pure_identity(x.clone());
    ///     wrapped.into_value() == x
    /// }
    ///
    /// assert!(verify_pure_identity_law(42));
    /// assert!(verify_pure_identity_law("hello".to_string()));
    /// ```
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::wrapper::value::Value;
    /// use rustica::traits::identity::Identity;
    ///
    /// // Create a Value from an integer
    /// let int_value: Value<i32> = Value::<()>::pure_identity(42);
    /// assert_eq!(*int_value.value(), 42);
    ///
    /// // Create a Value from a string
    /// let str_value = Value::<bool>::pure_identity("hello".to_string());
    /// assert_eq!(*str_value.value(), "hello");
    /// ```
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
    /// This method applies the given function `f` to a reference of the inner value
    /// and wraps the result in a new `Value` instance, preserving the original Value.
    ///
    /// # Performance
    ///
    /// - **Time Complexity**: O(1) plus the cost of the mapping function `f`
    /// - **Memory Usage**: Creates a new `Value` wrapper with the result of `f`
    /// - **Borrowing**: Borrows the inner value without cloning it
    ///
    /// # Type Class Laws
    ///
    /// ## Identity Law
    ///
    /// ```rust
    /// use rustica::datatypes::wrapper::value::Value;
    /// use rustica::traits::functor::Functor;
    ///
    /// // For any Value(x): fmap(id) == id
    /// // where id is the identity function
    /// fn verify_identity_law<T: Clone + PartialEq>(x: T) -> bool {
    ///     let value_x = Value::new(x.clone());
    ///     
    ///     // Apply identity function
    ///     let mapped = value_x.fmap(|val| val.clone());
    ///     
    ///     mapped == value_x
    /// }
    ///
    /// assert!(verify_identity_law(42));
    /// assert!(verify_identity_law("hello".to_string()));
    /// ```
    ///
    /// ## Composition Law
    ///
    /// ```rust
    /// use rustica::datatypes::wrapper::value::Value;
    /// use rustica::traits::functor::Functor;
    ///
    /// // For any Value(x) and functions f and g:
    /// // fmap(f . g) == fmap(g) . fmap(f)
    /// fn verify_composition_law<T: Clone + PartialEq>(x: T) -> bool
    /// where T: std::fmt::Debug + std::ops::Add<Output = T> + From<u8>
    /// {
    ///     let value_x = Value::new(x);
    ///     
    ///     // Define two functions
    ///     let f = |x: &T| x.clone() + T::from(1);
    ///     let g = |x: &T| x.clone() + T::from(2);
    ///     
    ///     // Compose the functions (f after g)
    ///     let fg = |x: &T| f(&g(x));
    ///     
    ///     // Apply the functions in two different ways
    ///     let result1 = value_x.clone().fmap(fg);
    ///     let result2 = value_x.fmap(g).fmap(f);
    ///     
    ///     result1 == result2
    /// }
    ///
    /// assert!(verify_composition_law(5));
    /// ```
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::wrapper::value::Value;
    /// use rustica::traits::functor::Functor;
    ///
    /// let value = Value::new(42);
    ///
    /// // Double the value
    /// let doubled = value.fmap(|x| x * 2);
    /// assert_eq!(doubled.0, 84);
    ///
    /// // Original value is preserved
    /// assert_eq!(value.0, 42);
    /// ```
    #[inline]
    fn fmap<U, F>(&self, f: F) -> Self::Output<U>
    where
        F: FnOnce(&Self::Source) -> U,
    {
        Value(f(&self.0))
    }

    /// Maps a function over the wrapped value by consuming it.
    ///
    /// This method applies the given function `f` to the inner value, consuming
    /// the original `Value` and returning a new `Value` containing the result.
    /// This is more efficient than `fmap` when you no longer need the original `Value`.
    ///
    /// # Performance
    ///
    /// - **Time Complexity**: O(1) plus the cost of the mapping function `f`
    /// - **Memory Usage**: Creates a new `Value` wrapper with the result of `f`
    /// - **Ownership**: Takes ownership of the inner value, avoiding clones
    ///
    /// # Type Class Laws
    ///
    /// ## Identity Law
    ///
    /// ```rust
    /// use rustica::datatypes::wrapper::value::Value;
    /// use rustica::traits::functor::Functor;
    ///
    /// // For any Value(x): fmap_owned(id) == id
    /// // where id is the identity function
    /// fn verify_identity_law<T: Clone + PartialEq>(x: T) -> bool {
    ///     let value_x = Value::new(x.clone());
    ///     
    ///     // Apply identity function
    ///     let mapped = value_x.fmap_owned(|val| val);
    ///     
    ///     mapped == Value::new(x)
    /// }
    ///
    /// assert!(verify_identity_law(42));
    /// assert!(verify_identity_law("hello".to_string()));
    /// ```
    ///
    /// ## Composition Law
    ///
    /// ```rust
    /// use rustica::datatypes::wrapper::value::Value;
    /// use rustica::traits::functor::Functor;
    ///
    /// // For any Value(x) and functions f and g:
    /// // fmap_owned(f . g) == fmap_owned(g) . fmap_owned(f)
    /// fn verify_composition_law() -> bool {
    ///     let x = 5;
    ///     
    ///     // Define two functions
    ///     let f = |x: i32| x * 2;
    ///     let g = |x: i32| x + 3;
    ///     
    ///     // Compose the functions (g then f)
    ///     let fg = |x: i32| f(g(x));
    ///     
    ///     // Apply the functions in two different ways
    ///     let result1 = Value::new(x).fmap_owned(fg);
    ///     let result2 = Value::new(x).fmap_owned(g).fmap_owned(f);
    ///     
    ///     // Extract values for comparison since Value<T> doesn't implement PartialEq
    ///     result1.0 == result2.0
    /// }
    ///
    /// assert!(verify_composition_law());
    /// ```
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::wrapper::value::Value;
    /// use rustica::traits::functor::Functor;
    ///
    /// let value = Value::new(42);
    ///
    /// // Consume value and double the contained number
    /// let doubled = value.fmap_owned(|x| x * 2);
    /// assert_eq!(doubled.0, 84);
    ///
    /// // Note: value is consumed and can no longer be used
    /// ```
    #[inline]
    fn fmap_owned<U, F>(self, f: F) -> Self::Output<U>
    where
        F: FnOnce(Self::Source) -> U,
    {
        Value(f(self.0))
    }
}

impl<T: Clone> Evaluate for Value<T> {
    /// Returns the wrapped value by cloning it.
    ///
    /// This method retrieves the wrapped value without consuming the `Value` container.
    /// Since the container is preserved, the internal value is cloned.
    ///
    /// # Performance
    ///
    /// - **Time Complexity**: O(1) plus the cost of cloning the inner value
    /// - **Memory Usage**: Creates a copy of the wrapped value
    /// - **Borrowing**: Preserves the original `Value` container
    ///
    /// # Type Class Laws
    ///
    /// ## Idempotence Law
    ///
    /// ```rust
    /// use rustica::datatypes::wrapper::value::Value;
    /// use rustica::traits::evaluate::Evaluate;
    ///
    /// // Evaluating multiple times produces the same result
    /// fn verify_idempotence_law<T: Clone + PartialEq>(x: T) -> bool {
    ///     let value = Value::new(x);
    ///     
    ///     value.evaluate() == value.evaluate()
    /// }
    ///
    /// assert!(verify_idempotence_law(42));
    /// assert!(verify_idempotence_law("hello".to_string()));
    /// ```
    ///
    /// ## Referential Transparency Law
    ///
    /// ```rust
    /// use rustica::datatypes::wrapper::value::Value;
    /// use rustica::traits::evaluate::Evaluate;
    ///
    /// // Replacing a Value with its evaluated result doesn't change behavior
    /// fn verify_ref_transparency<T: Clone + PartialEq + std::ops::Add<Output = T> + From<u8>>(x: T) -> bool {
    ///     let value = Value::new(x.clone());
    ///     let result = value.evaluate();
    ///     
    ///     // These operations should be equivalent:
    ///     let result1 = value.evaluate() + T::from(1);
    ///     let result2 = result + T::from(1);
    ///     
    ///     result1 == result2
    /// }
    ///
    /// assert!(verify_ref_transparency(42));
    /// ```
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::wrapper::value::Value;
    /// use rustica::traits::evaluate::Evaluate;
    ///
    /// let value = Value::new(42);
    /// assert_eq!(value.evaluate(), 42);
    ///
    /// // Original Value is still available after evaluation
    /// assert_eq!(value.evaluate(), 42);
    /// ```
    #[inline]
    fn evaluate(&self) -> T {
        self.0.clone()
    }

    /// Consumes the Value and returns the wrapped value without cloning.
    ///
    /// This method is more efficient than `evaluate()` when you no longer need the
    /// `Value` container, as it avoids the need to clone the inner value.
    ///
    /// # Performance
    ///
    /// - **Time Complexity**: O(1) - no cloning required
    /// - **Memory Usage**: No additional memory allocation
    /// - **Ownership**: Consumes the wrapper and moves ownership of the inner value
    ///
    /// # Type Class Laws
    ///
    /// ## Owned Equivalence Law
    ///
    /// ```rust
    /// use rustica::datatypes::wrapper::value::Value;
    /// use rustica::traits::evaluate::Evaluate;
    ///
    /// // evaluate_owned() should produce the same result as evaluate()
    /// fn verify_owned_equivalence<T: Clone + PartialEq>(x: T) -> bool {
    ///     let value1 = Value::new(x.clone());
    ///     let value2 = Value::new(x.clone());
    ///     
    ///     value1.evaluate() == value2.evaluate_owned()
    /// }
    ///
    /// assert!(verify_owned_equivalence(42));
    /// assert!(verify_owned_equivalence("hello".to_string()));
    /// ```
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::wrapper::value::Value;
    /// use rustica::traits::evaluate::Evaluate;
    ///
    /// let value = Value::new(42);
    /// let result = value.evaluate_owned();
    ///
    /// assert_eq!(result, 42);
    /// // Note: value is consumed and can no longer be used
    /// ```
    #[inline]
    fn evaluate_owned(self) -> T {
        self.0
    }
}
