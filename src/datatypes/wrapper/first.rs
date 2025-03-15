//! # First
//!
//! This module provides the `First` wrapper type which forms a semigroup by taking the first non-None value.
//!
//! ```rust
//! use rustica::datatypes::wrapper::first::First;
//! use rustica::traits::semigroup::Semigroup;
//!
//! let a = First(Some(5));
//! let b = First(Some(10));
//! let c = a.combine(&b);
//! assert_eq!(c, First(Some(5))); // Takes the first value
//!
//! let x = First(None);
//! let y = First(Some(7));
//! let z = x.combine(&y);
//! assert_eq!(z, First(Some(7))); // First value was None, so takes the second
//! ```

use crate::traits::foldable::Foldable;
use crate::traits::hkt::HKT;
use crate::traits::monoid::Monoid;
use crate::traits::semigroup::Semigroup;
use std::fmt;

/// A wrapper type that forms a semigroup by taking the first non-None value.
///
/// The monoid instance uses `None` as the identity element.
///
/// # Examples
///
/// ```rust
/// use rustica::datatypes::wrapper::first::First;
/// use rustica::traits::semigroup::Semigroup;
/// use rustica::traits::monoid::Monoid;
///
/// let a = First(Some(5));
/// let b = First(Some(7));
/// let c = a.combine(&b);
/// assert_eq!(c, First(Some(5)));
///
/// // First is associative
/// let x = First(Some(1));
/// let y = First(None);
/// let z = First(Some(3));
/// assert_eq!(x.clone().combine(&y.clone()).combine(&z.clone()),
///            x.clone().combine(&y.clone()).combine(&z.clone()));
///
/// // Identity element
/// let id = First::empty();  // First(None)
/// assert_eq!(id, First(None));
/// assert_eq!(First(Some(42)).combine(&id.clone()), First(Some(42)));
/// assert_eq!(id.combine(&First(Some(42))), First(Some(42)));
/// ```
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
#[repr(transparent)]
pub struct First<T>(pub Option<T>);

impl<T: Clone> Semigroup for First<T> {
    #[inline]
    fn combine_owned(self, other: Self) -> Self {
        match self.0 {
            Some(_) => self,
            None => other,
        }
    }

    #[inline]
    fn combine(&self, other: &Self) -> Self {
        match &self.0 {
            Some(_) => First(self.0.clone()),
            None => First(other.0.clone()),
        }
    }
}

impl<T: fmt::Display> fmt::Display for First<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.0 {
            Some(value) => write!(f, "First(Some({}))", value),
            None => write!(f, "First(None)"),
        }
    }
}

impl<T: Clone> Monoid for First<T> {
    #[inline]
    fn empty() -> Self {
        First(None)
    }
}

impl<T> HKT for First<T> {
    type Source = T;
    type Output<U> = First<U>;
}

impl<T: Clone> Foldable for First<T> {
    #[inline]
    fn fold_left<U: Clone, F>(&self, init: &U, f: F) -> U
    where
        F: Fn(U, &Self::Source) -> U,
    {
        f(init.clone(), self.0.as_ref().unwrap())
    }

    #[inline]
    fn fold_right<U: Clone, F>(&self, init: &U, f: F) -> U
    where
        F: Fn(&Self::Source, U) -> U,
    {
        f(self.0.as_ref().unwrap(), init.clone())
    }
}
