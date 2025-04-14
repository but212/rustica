//! # Sum Wrapper
//!
//! This module provides the `Sum<T>` wrapper type which forms a semigroup under addition.
//! It enables treating values as summable entities regardless of context.
//!
//! ## Key Features
//!
//! - Implements `Semigroup` for any type implementing `Add`
//! - Implements `Monoid` when the inner type also has a zero value (`Default`)
//! - Provides a consistent way to combine values via addition
//! - Useful for aggregating collections of numeric values
//!
//! ## Basic Usage
//!
//! ```rust
//! use rustica::datatypes::wrapper::sum::Sum;
//! use rustica::traits::semigroup::Semigroup;
//! use rustica::traits::monoid::Monoid;
//!
//! // Create Sum values with explicit type annotation
//! let a: Sum<i32> = Sum::new(5);
//! let b: Sum<i32> = Sum::new(10);
//!
//! // Combine them using the Semigroup trait
//! let c = a.combine(&b);
//! assert_eq!(*c.inner_ref(), 15);
//!
//! // Use the identity element from Monoid
//! let zero: Sum<i32> = Sum::empty();  // Sum(0)
//! assert_eq!(*zero.inner_ref(), 0);
//! assert_eq!(*a.combine(&zero).inner_ref(), 5);
//! assert_eq!(*zero.combine(&a).inner_ref(), 5);
//! ```
//!
//! ## With Collections
//!
//! ```rust
//! use rustica::datatypes::wrapper::sum::Sum;
//! use rustica::traits::semigroup::Semigroup;
//! use rustica::traits::monoid::Monoid;
//!
//! // Sum a collection of values
//! let numbers: Vec<i32> = vec![1, 2, 3, 4, 5];
//! let sum: Sum<i32> = numbers.iter()
//!     .map(|&n| Sum::new(n))
//!     .fold(Sum::empty(), |acc, x| acc.combine(&x));
//!
//! assert_eq!(*sum.inner_ref(), 15); // 1 + 2 + 3 + 4 + 5 = 15
//! ```

use crate::traits::foldable::Foldable;
use crate::traits::functor::Functor;
use crate::traits::hkt::HKT;
use crate::traits::identity::Identity;
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
/// let a: Sum<i32> = Sum::new(5);
/// let b: Sum<i32> = Sum::new(7);
///
/// // Combine them (addition)
/// let c = a.combine(&b);
/// assert_eq!(*c.inner_ref(), 12);
///
/// // Addition is associative: (a + b) + c = a + (b + c)
/// let x: Sum<i32> = Sum::new(1);
/// let y: Sum<i32> = Sum::new(2);
/// let z: Sum<i32> = Sum::new(3);
///
/// let result1 = x.clone().combine(&y).combine(&z.clone());
/// let result2 = x.combine(&y.combine(&z));
/// assert_eq!(*result1.inner_ref(), *result2.inner_ref());
///
/// // Identity element
/// let id: Sum<i32> = Sum::empty();  // Sum(0)
/// assert_eq!(*id.inner_ref(), 0);
/// assert_eq!(*Sum::new(42).combine(&id).inner_ref(), 42);
/// assert_eq!(*id.combine(&Sum::new(42)).inner_ref(), 42);
/// ```
///
/// Working with floating-point numbers:
///
/// ```rust
/// use rustica::datatypes::wrapper::sum::Sum;
/// use rustica::traits::semigroup::Semigroup;
///
/// let a: Sum<f64> = Sum::new(2.5);
/// let b: Sum<f64> = Sum::new(3.7);
/// let c = a.combine(&b);
/// assert_eq!(*c.inner_ref(), 6.2);
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
/// let v1: Sum<Vector2D> = Sum::new(Vector2D { x: 1.0, y: 2.0 });
/// let v2: Sum<Vector2D> = Sum::new(Vector2D { x: 3.0, y: 4.0 });
/// let v3 = v1.combine(&v2);
///
/// assert_eq!(*v3.inner_ref(), Vector2D { x: 4.0, y: 6.0 });
/// ```
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Sum<T>(pub T);

impl<T> Sum<T> {
    /// Creates a new `Sum` wrapper around a value.
    ///
    /// # Parameters
    ///
    /// * `value`: The value to wrap
    ///
    /// # Returns
    ///
    /// A new `Sum` instance containing the given value
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::wrapper::sum::Sum;
    ///
    /// let sum: Sum<i32> = Sum::new(42);
    /// assert_eq!(*sum.inner_ref(), 42);
    /// ```
    #[inline]
    pub fn new(value: T) -> Self {
        Sum(value)
    }

    /// Returns the wrapped value, consuming the `Sum`.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::datatypes::wrapper::sum::Sum;
    ///
    /// let value = Sum::new(42);
    /// assert_eq!(value.inner(), 42);
    /// ```
    #[inline]
    pub fn inner(self) -> T {
        self.0
    }

    /// Returns a reference to the wrapped value.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::datatypes::wrapper::sum::Sum;
    ///
    /// let value = Sum::new(42);
    /// assert_eq!(*value.inner_ref(), 42);
    /// ```
    #[inline]
    pub fn inner_ref(&self) -> &T {
        &self.0
    }

    /// Clones and returns the inner value.
    ///
    /// This method is useful when you want to get the inner value
    /// without consuming the `Sum`.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::datatypes::wrapper::sum::Sum;
    ///
    /// let value = Sum::new(42);
    /// assert_eq!(value.inner_cloned(), 42);
    /// // value can still be used
    /// assert_eq!(*value.inner_ref(), 42);
    /// ```
    #[inline]
    pub fn inner_cloned(&self) -> T
    where
        T: Clone,
    {
        self.0.clone()
    }
}

impl<T: Clone + Add<Output = T>> Semigroup for Sum<T> {
    fn combine_owned(self, other: Self) -> Self {
        Sum(self.0 + other.0)
    }

    fn combine(&self, other: &Self) -> Self {
        Sum(self.0.clone() + other.0.clone())
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
    fn empty() -> Self {
        Sum(T::default())
    }
}

impl<T> HKT for Sum<T> {
    type Source = T;
    type Output<U> = Sum<U>;
}

impl<T: Clone + Add<Output = T>> Identity for Sum<T> {
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
        Sum(value)
    }
}

impl<T: Clone + Add<Output = T>> Functor for Sum<T> {
    fn fmap<U, F>(&self, f: F) -> Self::Output<U>
    where
        F: Fn(&Self::Source) -> U,
    {
        Sum(f(&self.0))
    }

    fn fmap_owned<U, F>(self, f: F) -> Self::Output<U>
    where
        F: FnOnce(Self::Source) -> U,
    {
        Sum(f(self.0))
    }
}

impl<T: Clone + Add<Output = T>> Foldable for Sum<T> {
    fn fold_left<U, F>(&self, init: &U, f: F) -> U
    where
        F: Fn(&U, &Self::Source) -> U,
        U: Clone,
    {
        f(init, &self.0)
    }

    fn fold_right<U, F>(&self, init: &U, f: F) -> U
    where
        F: Fn(&Self::Source, &U) -> U,
        U: Clone,
    {
        f(&self.0, init)
    }
}
