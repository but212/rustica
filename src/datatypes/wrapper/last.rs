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
//!
//! ## Performance Characteristics
//!
//! - Time Complexity: All operations (`combine`, `empty`, `fmap`, etc.) are O(1)
//! - Memory Usage: Stores exactly one `Option<T>` value with no additional overhead
//! - Clone Cost: Depends on the cost of cloning the inner type `T`

use crate::traits::foldable::Foldable;
use crate::traits::functor::Functor;
use crate::traits::hkt::HKT;
use crate::traits::identity::Identity;
use crate::traits::monoid::Monoid;
use crate::traits::semigroup::Semigroup;
use std::fmt;

/// A wrapper type that forms a semigroup by taking the last non-None value.
///
/// The monoid instance uses `None` as the identity element.
///
/// # Examples
///
/// Basic usage with the `Semigroup` trait:
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
///            x.clone().combine(&y.clone().combine(&z.clone())));
///
/// // Identity element
/// let id = Last::empty();  // Last(None)
/// assert_eq!(id, Last(None));
/// assert_eq!(Last(Some(42)).combine(&id.clone()), Last(Some(42)));
/// assert_eq!(id.combine(&Last(Some(42))), Last(Some(42)));
/// ```
///
/// Using with `Functor` to transform the inner value:
///
/// ```rust
/// use rustica::datatypes::wrapper::last::Last;
/// use rustica::traits::functor::Functor;
///
/// let a = Last(Some(5));
/// let b = a.fmap(|x| x * 2);
/// assert_eq!(b, Last(Some(10)));
///
/// let c = Last(None);
/// let d = c.fmap(|x| x * 2);
/// assert_eq!(d, Last(None));
/// ```
///
/// Using with `Foldable` to extract and process values:
///
/// ```rust
/// use rustica::datatypes::wrapper::last::Last;
/// use rustica::traits::foldable::Foldable;
///
/// let a = Last(Some(5));
/// let result = a.fold_left(&10, |acc, val| acc + val);
/// assert_eq!(result, 15);
/// ```
///
/// Using with `Identity` to access the inner value:
///
/// ```rust
/// use rustica::datatypes::wrapper::last::Last;
/// use rustica::traits::identity::Identity;
///
/// let a = Last(Some(42));
/// assert_eq!(*a.value(), 42);
/// assert_eq!(a.into_value(), 42);
///
/// let b = Last::<i32>::pure_identity(100);
/// assert_eq!(b, Last(Some(100)));
/// ```
///
/// # Semigroup Laws
///
/// Last satisfies the semigroup associativity law:
///
/// ```rust
/// use rustica::datatypes::wrapper::last::Last;
/// use rustica::traits::semigroup::Semigroup;
///
/// // Verify associativity: (a ⊕ b) ⊕ c = a ⊕ (b ⊕ c)
/// fn check_associativity<T: Clone + PartialEq>(a: Last<T>, b: Last<T>, c: Last<T>) -> bool {
///     let left = a.clone().combine(&b).combine(&c);
///     let right = a.combine(&b.combine(&c));
///     left == right
/// }
///
/// // Test with different combinations
/// assert!(check_associativity(Last(Some(1)), Last(Some(2)), Last(Some(3))));
/// assert!(check_associativity(Last(Some(1)), Last(None), Last(Some(3))));
/// assert!(check_associativity(Last(None), Last(Some(2)), Last(None)));
/// ```
///
/// # Monoid Laws
///
/// Last satisfies the monoid identity laws:
///
/// ```rust
/// use rustica::datatypes::wrapper::last::Last;
/// use rustica::traits::semigroup::Semigroup;
/// use rustica::traits::monoid::Monoid;
///
/// // Verify left identity: empty() ⊕ a = a
/// fn check_left_identity<T: Clone + PartialEq>(a: Last<T>) -> bool {
///     let empty = Last::empty();
///     empty.combine(&a) == a
/// }
///
/// // Verify right identity: a ⊕ empty() = a
/// fn check_right_identity<T: Clone + PartialEq>(a: Last<T>) -> bool {
///     let empty = Last::empty();
///     a.combine(&empty) == a
/// }
///
/// assert!(check_left_identity(Last(Some(42))));
/// assert!(check_right_identity(Last(Some(42))));
/// assert!(check_left_identity::<i32>(Last(None)));
/// assert!(check_right_identity::<i32>(Last(None)));
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
            Some(value) => write!(f, "Last(Some({value}))"),
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
        F: FnOnce(&U, &Self::Source) -> U,
    {
        f(init, self.0.as_ref().unwrap())
    }

    #[inline]
    fn fold_right<U: Clone, F>(&self, init: &U, f: F) -> U
    where
        F: FnOnce(&Self::Source, &U) -> U,
    {
        f(self.0.as_ref().unwrap(), init)
    }
}

impl<T: Clone> Identity for Last<T> {
    fn value(&self) -> &Self::Source {
        self.0.as_ref().unwrap()
    }

    fn into_value(self) -> Self::Source {
        self.0.unwrap()
    }

    fn pure_identity<A>(value: A) -> Self::Output<A>
    where
        Self::Output<A>: Identity,
        A: Clone,
    {
        Last(Some(value))
    }
}

impl<T: Clone> Functor for Last<T> {
    #[inline]
    fn fmap<U, F>(&self, f: F) -> Self::Output<U>
    where
        F: FnOnce(&Self::Source) -> U,
    {
        match &self.0 {
            Some(value) => Last(Some(f(value))),
            None => Last(None),
        }
    }

    #[inline]
    fn fmap_owned<U, F>(self, f: F) -> Self::Output<U>
    where
        F: FnOnce(Self::Source) -> U,
    {
        match self.0 {
            Some(value) => Last(Some(f(value))),
            None => Last(None),
        }
    }
}
