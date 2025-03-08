//! # Min
//!
//! This module provides the `Min` wrapper type which forms a semigroup under taking the minimum.
//!
//! ```rust
//! use rustica::datatypes::wrapper::min::Min;
//! use rustica::traits::semigroup::Semigroup;
//!
//! let a = Min(5);
//! let b = Min(10);
//! let c = a.combine(&b);
//! assert_eq!(c, Min(5));
//! ```

use crate::traits::semigroup::Semigroup;
use crate::traits::foldable::Foldable;
use crate::traits::hkt::HKT;
use std::cmp::Ordering;
use std::fmt;

/// A wrapper type that forms a semigroup under the minimum operation.
///
/// When the inner type has a maximum value, this also forms a monoid.
///
/// # Examples
///
/// ```rust
/// use rustica::datatypes::wrapper::min::Min;
/// use rustica::traits::semigroup::Semigroup;
///
/// let a = Min(5);
/// let b = Min(7);
/// let c = a.combine(&b);
/// assert_eq!(c, Min(5));
///
/// // Taking the minimum is associative: min(min(a, b), c) = min(a, min(b, c))
/// let x = Min(10);
/// let y = Min(2);
/// let z = Min(6);
/// assert_eq!(x.clone().combine(&y.clone()).combine(&z.clone()), 
///            x.clone().combine(&y.clone()).combine(&z.clone()));
/// ```
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct Min<T>(pub T);

impl<T: Clone + Ord> Semigroup for Min<T> {
    fn combine_owned(self, other: Self) -> Self {
        match self.0.cmp(&other.0) {
            Ordering::Less | Ordering::Equal => self,
            Ordering::Greater => other,
        }
    }

    fn combine(&self, other: &Self) -> Self {
        match self.0.cmp(&other.0) {
            Ordering::Less | Ordering::Equal => Min(self.0.clone()),
            Ordering::Greater => Min(other.0.clone()),
        }
    }
}

impl<T: fmt::Debug> fmt::Debug for Min<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Min({:?})", self.0)
    }
}

impl<T: fmt::Display> fmt::Display for Min<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Min({})", self.0)
    }
}

impl<T> HKT for Min<T> {
    type Source = T;
    type Output<U> = Min<U>;
}

impl<T: Clone + Ord> Foldable for Min<T> {
    #[inline]
    fn fold_left<U: Clone, F>(&self, init: &U, f: F) -> U
        where
            F: Fn(U, &Self::Source) -> U {
        f(init.clone(), &self.0)
    }

    #[inline]
    fn fold_right<U: Clone, F>(&self, init: &U, f: F) -> U
        where
            F: Fn(&Self::Source, U) -> U {
        f(&self.0, init.clone())
    }
}
