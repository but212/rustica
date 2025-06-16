//! # Max
//!
//! This module provides the `Max` wrapper type which forms a semigroup under taking the maximum.
//!
//! ```rust
//! use rustica::datatypes::wrapper::max::Max;
//! use rustica::traits::semigroup::Semigroup;
//!
//! let a = Max(5);
//! let b = Max(10);
//! let c = a.combine(&b);
//! assert_eq!(c, Max(10));
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

/// A wrapper type that forms a semigroup under the maximum operation.
///
/// When the inner type has a minimum value, this also forms a monoid.
///
/// # Examples
///
/// ```rust
/// use rustica::datatypes::wrapper::max::Max;
/// use rustica::traits::semigroup::Semigroup;
///
/// let a = Max(5);
/// let b = Max(7);
/// let c = a.combine(&b);
/// assert_eq!(c, Max(7));
///
/// // Taking the maximum is associative: max(max(a, b), c) = max(a, max(b, c))
/// let x = Max(10);
/// let y = Max(2);
/// let z = Max(6);
/// assert_eq!(x.clone().combine(&y.clone()).combine(&z.clone()),
///            x.clone().combine(&y.clone().combine(&z.clone())));
/// ```
///
/// # Semigroup Laws
///
/// The `Max<T>` wrapper satisfies the semigroup associativity law:
///
/// ```rust
/// use rustica::datatypes::wrapper::max::Max;
/// use rustica::traits::semigroup::Semigroup;
///
/// // Verify associativity: (a combine b) combine c = a combine (b combine c)
/// fn verify_associativity<T: Clone + Ord>(a: T, b: T, c: T) -> bool {
///     let max_a = Max(a);
///     let max_b = Max(b);
///     let max_c = Max(c);
///     
///     let left = max_a.clone().combine(&max_b).combine(&max_c);
///     let right = max_a.combine(&max_b.combine(&max_c));
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
/// When `T` has a default value (typically the minimum possible value), `Max<T>` forms a monoid:
///
/// ```rust
/// use rustica::datatypes::wrapper::max::Max;
/// use rustica::traits::semigroup::Semigroup;
/// use rustica::traits::monoid::Monoid;
///
/// // Verify identity laws: empty combine x = x combine empty = x
/// fn verify_identity_laws<T: Clone + Ord + Default>(x: T) -> bool {
///     let max_x = Max(x.clone());
///     let empty = Max::<T>::empty();
///     
///     let left_id = empty.clone().combine(&max_x.clone()) == max_x.clone();
///     let right_id = max_x.clone().combine(&empty) == max_x;
///     
///     left_id && right_id
/// }
///
/// assert!(verify_identity_laws(42));
/// assert!(verify_identity_laws(0));
/// ```
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
pub struct Max<T>(pub T);

impl<T: Clone + Ord> Semigroup for Max<T> {
    #[inline]
    fn combine_owned(self, other: Self) -> Self {
        match self.0.cmp(&other.0) {
            Ordering::Greater | Ordering::Equal => self,
            Ordering::Less => other,
        }
    }

    #[inline]
    fn combine(&self, other: &Self) -> Self {
        match self.0.cmp(&other.0) {
            Ordering::Greater | Ordering::Equal => Max(self.0.clone()),
            Ordering::Less => Max(other.0.clone()),
        }
    }
}

impl<T: Clone + Ord + Default> Monoid for Max<T> {
    #[inline]
    fn empty() -> Self {
        Max(T::default())
    }
}

impl<T: fmt::Debug> fmt::Debug for Max<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Max({:?})", self.0)
    }
}

impl<T: fmt::Display> fmt::Display for Max<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Max({})", self.0)
    }
}

impl<T> HKT for Max<T> {
    type Source = T;
    type Output<U> = Max<U>;
}

impl<T: Clone + Ord> Identity for Max<T> {
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
        Max(value)
    }
}

impl<T: Clone + Ord> Functor for Max<T> {
    #[inline]
    fn fmap<U, F>(&self, f: F) -> Self::Output<U>
    where
        F: FnOnce(&Self::Source) -> U,
    {
        Max(f(&self.0))
    }

    #[inline]
    fn fmap_owned<U, F>(self, f: F) -> Self::Output<U>
    where
        F: FnOnce(Self::Source) -> U,
    {
        Max(f(self.0))
    }
}

impl<T: Clone + Ord> Foldable for Max<T> {
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
