//! # Product
//!
//! This module provides the `Product` wrapper type which forms a semigroup under multiplication.
//!
//! ```rust
//! use rustica::datatypes::wrapper::product::Product;
//! use rustica::traits::semigroup::Semigroup;
//! use rustica::traits::monoid::Monoid;
//!
//! let a = Product(5);
//! let b = Product(10);
//! let c = a.combine(&b);
//! assert_eq!(c, Product(50));
//! ```
//!
//! ## Performance Characteristics
//!
//! - Time Complexity: All operations (`combine`, `empty`, `fmap`, etc.) are O(1)
//! - Memory Usage: Stores exactly one value of type `T` with no additional overhead
//! - Clone Cost: Depends on the cost of cloning the inner type `T`

use crate::traits::foldable::Foldable;
use crate::traits::functor::Functor;
use crate::traits::hkt::HKT;
use crate::traits::identity::Identity;
use crate::traits::monoid::Monoid;
use crate::traits::semigroup::Semigroup;
use std::fmt;
use std::ops::Mul;

/// A wrapper type that forms a semigroup under multiplication.
///
/// `Product<T>` wraps a value of type `T` that can be multiplied with other values of the same type.
/// When the inner type also has a multiplicative identity of 1, `Product<T>` forms a complete monoid.
///
/// # Type Parameters
///
/// * `T`: The inner type that supports multiplication via the `Mul` trait
///
/// # Properties
///
/// For `Product<T>` to work correctly, the multiplication operation of `T` should satisfy:
///
/// - **Associativity**: `(a * b) * c = a * (b * c)`
/// - **Identity** (for Monoid): `1 * a = a * 1 = a`
///
/// # Examples
///
/// ```rust
/// use rustica::datatypes::wrapper::product::Product;
/// use rustica::traits::semigroup::Semigroup;
/// use rustica::traits::monoid::Monoid;
///
/// // Create Product values
/// let a = Product(5);
/// let b = Product(7);
///
/// // Combine them (multiplication)
/// let c = a.combine(&b);
/// assert_eq!(c, Product(35));
///
/// // Multiplication is associative: (a * b) * c = a * (b * c)
/// let x = Product(2);
/// let y = Product(3);
/// let z = Product(4);
///
/// let result1 = x.clone().combine(&y).combine(&z.clone());
/// let result2 = x.combine(&y.combine(&z));
/// assert_eq!(result1, result2);
///
/// // Identity element
/// let id = Product::empty();  // Product(1)
/// assert_eq!(id, Product(1));
/// assert_eq!(Product(42).combine(&id), Product(42));
/// assert_eq!(id.combine(&Product(42)), Product(42));
/// ```
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
pub struct Product<T>(pub T);

impl<T: Clone + Mul<Output = T>> Semigroup for Product<T> {
    #[inline]
    fn combine_owned(self, other: Self) -> Self {
        Product(self.0 * other.0)
    }

    #[inline]
    fn combine(&self, other: &Self) -> Self {
        Product(self.0.clone() * other.0.clone())
    }
}

impl<T: fmt::Debug> fmt::Debug for Product<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Product({:?})", self.0)
    }
}

impl<T: fmt::Display> fmt::Display for Product<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Product({})", self.0)
    }
}

impl<T: Clone + Mul<Output = T> + From<u8>> Monoid for Product<T> {
    #[inline]
    fn empty() -> Self {
        Product(T::from(1))
    }
}

impl<T> HKT for Product<T> {
    type Source = T;
    type Output<U> = Product<U>;
}

impl<T: Clone + Mul<Output = T>> Identity for Product<T> {
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
        Product(value)
    }
}

impl<T: Clone + Mul<Output = T>> Functor for Product<T> {
    #[inline]
    fn fmap<U, F>(&self, f: F) -> Self::Output<U>
    where
        F: FnOnce(&Self::Source) -> U,
    {
        Product(f(&self.0))
    }

    #[inline]
    fn fmap_owned<U, F>(self, f: F) -> Self::Output<U>
    where
        F: FnOnce(Self::Source) -> U,
    {
        Product(f(self.0))
    }
}

impl<T: Clone + Mul<Output = T>> Foldable for Product<T> {
    #[inline]
    fn fold_left<U: Clone, F>(&self, init: &U, f: F) -> U
    where
        F: FnOnce(&U, &Self::Source) -> U,
    {
        f(init, &self.0)
    }

    #[inline]
    fn fold_right<U: Clone, F>(&self, init: &U, f: F) -> U
    where
        F: FnOnce(&Self::Source, &U) -> U,
    {
        f(&self.0, init)
    }
}
