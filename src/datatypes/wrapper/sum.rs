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
//! ## Performance Characteristics
//!
//! - Time Complexity: All operations (`combine`, `empty`, `fmap`, etc.) are O(1)
//! - Memory Usage: Stores exactly one value of type `T` with no additional overhead
//! - Clone Cost: Depends on the cost of cloning the inner type `T`
//!
//! ## Basic Usage
//!
//! ```rust
//! use rustica::datatypes::wrapper::sum::Sum;
//! use rustica::traits::semigroup::Semigroup;
//! use rustica::traits::monoid::Monoid;
//! use rustica::traits::identity::Identity;
//!
//! // Create Sum values with explicit type annotation
//! let a: Sum<i32> = Sum(5);
//! let b: Sum<i32> = Sum(10);
//!
//! // Combine them using the Semigroup trait
//! let c = a.combine(&b);
//! assert_eq!(*c.value(), 15);
//!
//! // Use the identity element from Monoid
//! let zero: Sum<i32> = Sum::empty();  // Sum(0)
//! assert_eq!(*zero.value(), 0);
//! assert_eq!(*a.combine(&zero).value(), 5);
//! assert_eq!(*zero.combine(&a).value(), 5);
//! ```
//!
//! ## With Collections
//!
//! ```rust
//! use rustica::datatypes::wrapper::sum::Sum;
//! use rustica::traits::semigroup::Semigroup;
//! use rustica::traits::monoid::Monoid;
//! use rustica::traits::identity::Identity;
//!
//! // Sum a collection of values
//! let numbers: Vec<i32> = vec![1, 2, 3, 4, 5];
//! let sum: Sum<i32> = numbers.iter()
//!     .map(|&n| Sum(n))
//!     .fold(Sum::empty(), |acc, x| acc.combine(&x));
//!
//! assert_eq!(*sum.value(), 15); // 1 + 2 + 3 + 4 + 5 = 15
//! ```
//!
//! ## Semigroup Laws
//!
//! ```rust
//! use rustica::datatypes::wrapper::sum::Sum;
//! use rustica::traits::semigroup::Semigroup;
//!
//! // Associativity: (a + b) + c = a + (b + c)
//! fn verify_associativity<T>(a: T, b: T, c: T) -> bool
//! where T: Clone + PartialEq + std::ops::Add<Output = T>
//! {
//!     let sum_a = Sum(a.clone());
//!     let sum_b = Sum(b.clone());
//!     let sum_c = Sum(c.clone());
//!
//!     let left = sum_a.clone().combine(&sum_b).combine(&sum_c.clone());
//!     let right = sum_a.combine(&sum_b.combine(&sum_c));
//!
//!     left == right
//! }
//!
//! assert!(verify_associativity(1, 2, 3));
//! assert!(verify_associativity(1.5, 2.5, 3.5));
//! ```
//!
//! ## Monoid Laws
//!
//! ```rust
//! use rustica::datatypes::wrapper::sum::Sum;
//! use rustica::traits::monoid::Monoid;
//! use rustica::traits::semigroup::Semigroup;
//!
//! // Left identity: empty() + a = a
//! // Right identity: a + empty() = a
//! fn verify_identity<T>(a: T) -> bool
//! where T: Clone + PartialEq + std::ops::Add<Output = T> + Default
//! {
//!     let sum_a = Sum(a.clone());
//!     let empty = Sum::<T>::empty();
//!
//!     let left_id = empty.clone().combine(&sum_a.clone());
//!     let right_id = sum_a.clone().combine(&empty);
//!
//!     left_id == sum_a.clone() && right_id == sum_a
//! }
//!
//! assert!(verify_identity(42));
//! assert!(verify_identity(3.14));
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
/// use rustica::traits::identity::Identity;
///
/// // Create Sum values
/// let a: Sum<i32> = Sum(5);
/// let b: Sum<i32> = Sum(7);
///
/// // Combine them (addition)
/// let c = a.combine(&b);
/// assert_eq!(*c.value(), 12);
///
/// // Addition is associative: (a + b) + c = a + (b + c)
/// let x: Sum<i32> = Sum(1);
/// let y: Sum<i32> = Sum(2);
/// let z: Sum<i32> = Sum(3);
///
/// let result1 = x.clone().combine(&y).combine(&z.clone());
/// let result2 = x.combine(&y.combine(&z));
/// assert_eq!(*result1.value(), *result2.value());
///
/// // Identity element
/// let id: Sum<i32> = Sum(0);
/// assert_eq!(*id.value(), 0);
/// assert_eq!(*Sum(42).combine(&id).value(), 42);
/// assert_eq!(*id.combine(&Sum(42)).value(), 42);
/// ```
///
/// Working with floating-point numbers:
///
/// ```rust
/// use rustica::datatypes::wrapper::sum::Sum;
/// use rustica::traits::semigroup::Semigroup;
/// use rustica::traits::identity::Identity;
///
/// let a: Sum<f64> = Sum(2.5);
/// let b: Sum<f64> = Sum(3.7);
/// let c = a.combine(&b);
/// assert_eq!(*c.value(), 6.2);
/// ```
///
/// Custom types that implement `Add`:
///
/// ```rust
/// use rustica::datatypes::wrapper::sum::Sum;
/// use rustica::traits::semigroup::Semigroup;
/// use rustica::traits::identity::Identity;
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
/// let v3 = v1.combine(&v2);
///
/// assert_eq!(*v3.value(), Vector2D { x: 4.0, y: 6.0 });
/// ```
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Sum<T>(pub T);

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
