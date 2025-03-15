//! # Sum
//!
//! This module provides the `Sum` wrapper type which forms a semigroup under addition.
//!
//! ```rust
//! use rustica::datatypes::wrapper::sum::Sum;
//! use rustica::traits::semigroup::Semigroup;
//! use rustica::traits::monoid::Monoid;
//!
//! let a = Sum(5);
//! let b = Sum(10);
//! let c = a.combine(&b);
//! assert_eq!(c, Sum(15));
//! ```

use crate::traits::foldable::Foldable;
use crate::traits::hkt::HKT;
use crate::traits::monoid::Monoid;
use crate::traits::semigroup::Semigroup;
use std::fmt;
use std::ops::Add;

/// A wrapper type that forms a semigroup under addition.
///
/// When the inner type can be combined with a zero value, this also forms a monoid.
///
/// # Examples
///
/// ```rust
/// use rustica::datatypes::wrapper::sum::Sum;
/// use rustica::traits::semigroup::Semigroup;
/// use rustica::traits::monoid::Monoid;
///
/// let a = Sum(5);
/// let b = Sum(7);
/// let c = a.combine(&b);
/// assert_eq!(c, Sum(12));
///
/// // Addition is associative: (a + b) + c = a + (b + c)
/// let x = Sum(1);
/// let y = Sum(2);
/// let z = Sum(3);
/// assert_eq!(x.clone().combine(&y.clone()).combine(&z.clone()),
///            x.combine(&y.combine(&z)));
///
/// // Identity element
/// let id = Sum::empty();  // Sum(0)
/// assert_eq!(id, Sum(0));
/// assert_eq!(Sum(42).clone().combine(&id.clone()), Sum(42));
/// assert_eq!(id.combine(&Sum(42)), Sum(42));
/// ```
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
pub struct Sum<T>(pub T);

impl<T: Clone + Add<Output = T>> Semigroup for Sum<T> {
    #[inline]
    fn combine_owned(self, other: Self) -> Self {
        Sum(self.0 + other.0)
    }

    #[inline]
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
    #[inline]
    fn empty() -> Self {
        Sum(T::default())
    }
}

impl<T> HKT for Sum<T> {
    type Source = T;
    type Output<U> = Sum<U>;
}

impl<T: Clone + Add<Output = T>> Foldable for Sum<T> {
    #[inline]
    fn fold_left<U: Clone, F>(&self, init: &U, f: F) -> U
    where
        F: Fn(U, &Self::Source) -> U,
    {
        f(init.clone(), &self.0)
    }

    #[inline]
    fn fold_right<U: Clone, F>(&self, init: &U, f: F) -> U
    where
        F: Fn(&Self::Source, U) -> U,
    {
        f(&self.0, init.clone())
    }
}
