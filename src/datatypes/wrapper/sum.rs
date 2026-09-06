//! # Sum Wrapper
//!
//! This module provides the `Sum<T>` wrapper type which forms a semigroup under addition.
//! It enables treating values as summable entities regardless of context.
//!
//! ## Key Features
//!
//! - Implements `Semigroup` for any type implementing `Add`
//! - Implements Monoid when the inner type also has a zero value (`Default`)
//! - Provides a consistent way to combine values via addition
//! - Useful for aggregating collections of numeric values
//!
//! ## Functional Programming Context
//!
//! The `Sum` wrapper is a fundamental building block for functional programming patterns:
//!
//! - **Aggregation**: Provides a principled way to combine values
//! - **Transformation**: Works with `Functor` to map inner values while preserving the wrapper
//! - **Composition**: Combines with other algebraic structures for complex operations
//!
//! ## Type Class Laws
//!
//! ### Semigroup Laws
//!
//! `Sum<T>` satisfies the semigroup associativity law:
//!
//! - **Associativity**: `(a ⊕ b) ⊕ c = a ⊕ (b ⊕ c)`
//!   - For all values a, b, and c, combining a and b and then combining the result with c
//!     yields the same result as combining a with the combination of b and c.
//!
//! ### Monoid Laws
//!
//! `Sum<T>` satisfies the monoid identity laws when the inner type has a zero value:
//!
//! - **Left Identity**: `empty() ⊕ a = a`
//!   - Combining the identity element (typically zero) with any value gives the original value.
//!
//! - **Right Identity**: `a ⊕ empty() = a`
//!   - Combining any value with the identity element gives the original value.
//!
//! ### Functor Laws
//!
//! `Sum<T>` satisfies the functor laws:
//!
//! - **Identity**: `fmap(id) = id`
//!   - Mapping the identity function over a `Sum` value gives the same value.
//!
//! - **Composition**: `fmap(f . g) = fmap(f) . fmap(g)`
//!   - Mapping a composed function is the same as mapping each function in sequence.
//!
//! ## Type Class Implementations
//!
//! `Sum<T>` implements the following type classes:
//!
//! - `Semigroup`: For any `T` that implements `Add`
//! - `Monoid`: For any `T` that implements `Add` and `Default`
//! - `Functor`: For mapping operations over the inner value
//! - `HKT`: For higher-kinded type operations
//!
//! ## Quick Start
//!
//! ```rust
//! use rustica::datatypes::wrapper::sum::Sum;
//! use rustica::traits::{semigroup::Semigroup, monoid::Monoid};
//!
//! // Create Sum wrappers
//! let a = Sum(3);
//! let b = Sum(7);
//! let c = Sum(5);
//!
//! // Values are combined by addition
//! assert_eq!(a.clone().combine(b.clone()), Sum(10)); // 3 + 7 = 10
//! assert_eq!(b.clone().combine(c.clone()), Sum(12)); // 7 + 5 = 12
//!
//! // Chaining additions
//! let result = a.clone().combine(b).combine(c.clone());
//! assert_eq!(result, Sum(15)); // 3 + 7 + 5 = 15
//!
//! // Identity element (additive identity: 0)
//! let empty = Sum::empty();
//! assert_eq!(a.clone().combine(empty), a); // 3 + 0 = 3
//! ```

use crate::traits::functor::Functor;
use crate::traits::hkt::HKT;
use crate::traits::monoid::Monoid;
use crate::traits::semigroup::Semigroup;
use std::fmt;
use std::ops::Add;

/// A wrapper type that forms a semigroup under addition.
///
/// `Sum<T>` wraps a value of type `T` that can be added to other values of the same type.
/// When the inner type also implements `Default`, `Sum<T>` forms a complete monoid with
/// a zero identity element.
///
/// # Type Parameters
///
/// * `T`: The inner type that supports addition via the `Add` trait
///
/// # Properties
///
/// For `Sum<T>` to work correctly, the addition operation of `T` should satisfy:
///
/// - **Associativity**: `(a + b) + c = a + (b + c)`
/// - **Identity** (for Monoid): `0 + a = a + 0 = a`
///
/// # Performance
///
/// - Time Complexity: All operations are O(1)
/// - Memory Usage: Stores exactly one value of type `T`
///
/// # Examples
///
/// Basic usage with integers:
///
/// ```rust
/// use rustica::datatypes::wrapper::sum::Sum;
/// use rustica::traits::semigroup::Semigroup;
/// use rustica::traits::monoid::Monoid;
///
/// // Create Sum values
/// let a: Sum<i32> = Sum(5);
/// let b: Sum<i32> = Sum(7);
///
/// // Combine them (addition)
/// let c = a.combine(b);
/// assert_eq!(c.into_inner(), 12);
///
/// // Addition is associative: (a + b) + c = a + (b + c)
/// let x: Sum<i32> = Sum(1);
/// let y: Sum<i32> = Sum(2);
/// let z: Sum<i32> = Sum(3);
///
/// let result1 = x.clone().combine(y.clone()).combine(z.clone());
/// let result2 = x.combine(y.combine(z));
/// assert_eq!(result1.into_inner(), result2.into_inner());
///
/// // Identity element
/// let id: Sum<i32> = Sum(0);
/// assert_eq!(*id.get(), 0);
/// assert_eq!(Sum(42).combine(id.clone()).into_inner(), 42);
/// assert_eq!(id.combine(Sum(42)).into_inner(), 42);
/// ```
///
/// Working with floating-point numbers:
///
/// ```rust
/// use rustica::datatypes::wrapper::sum::Sum;
/// use rustica::traits::semigroup::Semigroup;
///
/// let a: Sum<f64> = Sum(2.5);
/// let b: Sum<f64> = Sum(3.7);
/// let c = a.combine(b);
/// assert_eq!(c.into_inner(), 6.2);
/// ```
///
/// Custom types that implement `Add`:
///
/// ```rust
/// use rustica::datatypes::wrapper::sum::Sum;
/// use rustica::traits::semigroup::Semigroup;
/// use std::ops::Add;
///
/// #[derive(Debug, Clone, PartialEq)]
/// struct Vector2D {
///     x: f64,
///     y: f64,
/// }
///
/// impl Add for Vector2D {
///     type Output = Self;
///
///     fn add(self, other: Self) -> Self {
///         Vector2D {
///             x: self.x + other.x,
///             y: self.y + other.y,
///         }
///     }
/// }
///
/// // Now we can use Sum with our custom type
/// let v1: Sum<Vector2D> = Sum(Vector2D { x: 1.0, y: 2.0 });
/// let v2: Sum<Vector2D> = Sum(Vector2D { x: 3.0, y: 4.0 });
/// let v3 = v1.combine(v2);
///
/// assert_eq!(v3.into_inner(), Vector2D { x: 4.0, y: 6.0 });
/// ```
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[repr(transparent)]
pub struct Sum<T>(pub T);

impl<T> Sum<T> {
    /// Creates a new `Sum` wrapping the given value.
    #[inline]
    pub const fn new(value: T) -> Self {
        Sum(value)
    }

    /// Consumes the wrapper and returns the contained value.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::wrapper::sum::Sum;
    /// let sum = Sum(42);
    /// assert_eq!(sum.into_inner(), 42);
    /// ```
    #[inline]
    pub fn into_inner(self) -> T {
        self.0
    }

    /// Returns a reference to the contained value.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::wrapper::sum::Sum;
    /// let sum = Sum(42);
    /// assert_eq!(*sum.get(), 42);
    /// ```
    #[inline]
    pub fn get(&self) -> &T {
        &self.0
    }
}

impl<T: Clone> Sum<T> {
    /// Unwraps the sum value.
    #[deprecated(since = "0.15.0", note = "use `into_inner()` or `get()` instead")]
    #[inline]
    pub fn unwrap(&self) -> T {
        self.0.clone()
    }

    /// Unwraps the sum value or returns a default.
    #[deprecated(since = "0.15.0", note = "use `into_inner()` or `get()` instead")]
    #[inline]
    pub fn unwrap_or(&self, _default: T) -> T {
        self.0.clone()
    }
}

impl<T> AsRef<T> for Sum<T> {
    #[inline]
    fn as_ref(&self) -> &T {
        &self.0
    }
}

impl<T: Add<Output = T>> Semigroup for Sum<T> {
    /// Combines two `Sum` values through addition, consuming self.
    ///
    /// # Examples
    /// ```rust
    /// use rustica::datatypes::wrapper::sum::Sum;
    /// use rustica::traits::semigroup::Semigroup;
    ///
    /// let a = Sum(5);
    /// let b = Sum(10);
    /// let c = a.combine(b);
    /// assert_eq!(c, Sum(15));
    /// ```
    #[inline]
    fn combine(self, other: Self) -> Self {
        Sum(self.0 + other.0)
    }
}

impl<T: fmt::Debug> fmt::Debug for Sum<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Sum({:?})", self.0)
    }
}

impl<T: fmt::Display> fmt::Display for Sum<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Sum({})", self.0)
    }
}

impl<T: Clone + Add<Output = T> + Default> Monoid for Sum<T> {
    /// Returns the identity element for the addition operation.
    ///
    /// This method creates a `Sum` that contains the default value of type `T`,
    /// which is expected to be an identity element for addition (typically zero).
    /// Any `Sum` combined with this identity element should remain unchanged.
    ///
    /// # Performance
    ///
    /// - **Time Complexity**: O(1) plus the complexity of `T::default()`
    /// - **Memory Usage**: Creates a single new `Sum` wrapper with the default value of `T`
    /// - **Note**: For primitive numeric types, `T::default()` returns zero
    ///
    /// # Type Class Laws
    ///
    /// ## Left Identity
    ///
    ///
    /// Algebraic laws for this wrapper are verified by unit tests.
    ///
    /// ## Right Identity
    ///
    ///
    /// Algebraic laws for this wrapper are verified by unit tests.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::wrapper::sum::Sum;
    /// use rustica::traits::monoid::Monoid;
    /// use rustica::traits::semigroup::Semigroup;
    ///
    /// // Create the identity element (Sum(0))
    /// let identity: Sum<i32> = Sum::empty();
    /// assert_eq!(*identity.get(), 0);
    ///
    /// // Identity property demonstration
    /// let a = Sum(42);
    /// assert_eq!(a.clone().combine(identity.clone()), a);  // a + 0 = a
    /// assert_eq!(identity.clone().combine(a.clone()), a);  // 0 + a = a
    /// ```
    #[inline]
    fn empty() -> Self {
        Sum(T::default())
    }
}

impl<T> HKT for Sum<T> {
    type Source = T;
    type Output<U> = Sum<U>;
}

impl<T: Add<Output = T>> Functor for Sum<T> {
    #[inline]
    fn fmap<U, F>(self, mut f: F) -> Self::Output<U>
    where
        F: FnMut(Self::Source) -> U,
    {
        Sum(f(self.0))
    }
}

impl<T> From<T> for Sum<T> {
    #[inline]
    fn from(value: T) -> Self {
        Sum(value)
    }
}
