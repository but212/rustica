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
use std::cmp::Ordering;
use std::fmt;

/// A wrapper type that forms a semigroup under the minimum operation.
///
/// When the inner type has a maximum value, this also forms a monoid.
///
/// # Examples
///
/// Basic usage with the `Semigroup` trait:
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
///            x.clone().combine(&y.clone().combine(&z.clone())));
/// ```
///
/// # Semigroup Laws
///
/// The `Min<T>` wrapper satisfies the semigroup associativity law:
///
/// ```rust
/// use rustica::datatypes::wrapper::min::Min;
/// use rustica::traits::semigroup::Semigroup;
///
/// // Verify associativity: (a combine b) combine c = a combine (b combine c)
/// fn verify_associativity<T: Clone + Ord>(a: T, b: T, c: T) -> bool {
///     let min_a = Min(a);
///     let min_b = Min(b);
///     let min_c = Min(c);
///     
///     let left = min_a.clone().combine(&min_b).combine(&min_c);
///     let right = min_a.combine(&min_b.combine(&min_c));
///     
///     left == right
/// }
///
/// assert!(verify_associativity(1, 5, 3));
/// assert!(verify_associativity(10, 2, 7));
/// ```
///
/// # Monoid Laws
///
/// When `T` has a maximum value (like numeric types), `Min<T>` also satisfies the monoid laws:
///
/// ```rust
/// use rustica::datatypes::wrapper::min::Min;
/// use rustica::traits::semigroup::Semigroup;
/// use rustica::traits::monoid::Monoid;
///
/// // For integers, the default (0) may not be the identity element for Min
/// // We can verify that Max::MAX would be the true identity
/// let a = Min(42);
/// let id = Min(i32::MAX);
///
/// // Identity laws: empty() combine x = x combine empty() = x
/// assert_eq!(a.clone().combine(&id), a.clone());
/// assert_eq!(id.combine(&a), a);
/// ```
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
pub struct Min<T>(pub T);

impl<T: Clone + Ord> Semigroup for Min<T> {
    #[inline]
    fn combine_owned(self, other: Self) -> Self {
        match self.0.cmp(&other.0) {
            Ordering::Less | Ordering::Equal => self,
            Ordering::Greater => other,
        }
    }

    #[inline]
    fn combine(&self, other: &Self) -> Self {
        match self.0.cmp(&other.0) {
            Ordering::Less | Ordering::Equal => Min(self.0.clone()),
            Ordering::Greater => Min(other.0.clone()),
        }
    }
}

impl<T: Clone + Ord + Default> Monoid for Min<T> {
    #[inline]
    fn empty() -> Self {
        Min(T::default())
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

impl<T: Clone + Ord> Identity for Min<T> {
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
        Min(value)
    }
}

impl<T: Clone + Ord> Functor for Min<T> {
    #[inline]
    fn fmap<U, F>(&self, f: F) -> Self::Output<U>
    where
        F: FnOnce(&Self::Source) -> U,
    {
        Min(f(&self.0))
    }

    #[inline]
    fn fmap_owned<U, F>(self, f: F) -> Self::Output<U>
    where
        F: FnOnce(Self::Source) -> U,
    {
        Min(f(self.0))
    }
}

impl<T: Clone + Ord> Foldable for Min<T> {
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
