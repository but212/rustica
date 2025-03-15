//! # Last
//!
//! This module provides the `Last` wrapper type which forms a semigroup by taking the last non-None value.
//!
//! ```rust
//! use rustica::datatypes::wrapper::last::Last;
//! use rustica::traits::semigroup::Semigroup;
//!
//! let a = Last(Some(5));
//! let b = Last(Some(10));
//! let c = a.combine(&b);
//! assert_eq!(c, Last(Some(10))); // Takes the last value
//! 
//! let x = Last(None);
//! let y = Last(Some(7));
//! let z = x.combine(&y);
//! assert_eq!(z, Last(Some(7))); // First value was None, so takes the second
//! ```

use crate::traits::semigroup::Semigroup;
use crate::traits::monoid::Monoid;
use crate::traits::foldable::Foldable;
use crate::traits::hkt::HKT;
use std::fmt;

/// A wrapper type that forms a semigroup by taking the last non-None value.
///
/// The monoid instance uses `None` as the identity element.
///
/// # Examples
///
/// ```rust
/// use rustica::datatypes::wrapper::last::Last;
/// use rustica::traits::semigroup::Semigroup;
/// use rustica::traits::monoid::Monoid;
///
/// let a = Last(Some(5));
/// let b = Last(Some(7));
/// let c = a.combine(&b);
/// assert_eq!(c, Last(Some(7)));
///
/// // Last is associative
/// let x = Last(Some(1));
/// let y = Last(None);
/// let z = Last(Some(3));
/// assert_eq!(x.clone().combine(&y.clone()).combine(&z.clone()), 
///            x.clone().combine(&y.clone()).combine(&z.clone()));
///
/// // Identity element
/// let id = Last::empty();  // Last(None)
/// assert_eq!(id, Last(None));
/// assert_eq!(Last(Some(42)).combine(&id.clone()), Last(Some(42)));
/// assert_eq!(id.combine(&Last(Some(42))), Last(Some(42)));
/// ```
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
#[repr(transparent)]
pub struct Last<T>(pub Option<T>);

impl<T: Clone> Semigroup for Last<T> {
    #[inline]
    fn combine_owned(self, other: Self) -> Self {
        match other.0 {
            Some(_) => other,
            None => self,
        }
    }

    #[inline]
    fn combine(&self, other: &Self) -> Self {
        match &other.0 {
            Some(_) => Last(other.0.clone()),
            None => Last(self.0.clone()),
        }
    }
}

impl<T: fmt::Display> fmt::Display for Last<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.0 {
            Some(value) => write!(f, "Last(Some({}))", value),
            None => write!(f, "Last(None)"),
        }
    }
}

impl<T: Clone> Monoid for Last<T> {
    #[inline]
    fn empty() -> Self {
        Last(None)
    }
}

impl<T> HKT for Last<T> {
    type Source = T;
    type Output<U> = Last<U>;
}

impl<T: Clone> Foldable for Last<T> {
    #[inline]
    fn fold_left<U: Clone, F>(&self, init: &U, f: F) -> U
        where
            F: Fn(U, &Self::Source) -> U {
        f(init.clone(), &self.0.as_ref().unwrap())
    }

    #[inline]
    fn fold_right<U: Clone, F>(&self, init: &U, f: F) -> U
        where
            F: Fn(&Self::Source, U) -> U {
        f(&self.0.as_ref().unwrap(), init.clone())
    }
}
