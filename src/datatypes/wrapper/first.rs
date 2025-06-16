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

/// A wrapper type that forms a semigroup by taking the first non-None value.
///
/// The monoid instance uses `None` as the identity element.
///
/// # Examples
///
/// Basic usage with the `Semigroup` trait:
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
///            x.clone().combine(&y.clone().combine(&z.clone())));
///
/// // Identity element
/// let id = First::empty();  // First(None)
/// assert_eq!(id, First(None));
/// assert_eq!(First(Some(42)).combine(&id.clone()), First(Some(42)));
/// assert_eq!(id.combine(&First(Some(42))), First(Some(42)));
/// ```
///
/// Using with `Functor` to transform the inner value:
///
/// ```rust
/// use rustica::datatypes::wrapper::first::First;
/// use rustica::traits::functor::Functor;
///
/// let a = First(Some(5));
/// let b = a.fmap(|x| x * 2);
/// assert_eq!(b, First(Some(10)));
///
/// let c = First(None);
/// let d = c.fmap(|x: &i32| x * 2);
/// assert_eq!(d, First(None));
/// ```
///
/// Using with `Foldable` to extract and process values:
///
/// ```rust
/// use rustica::datatypes::wrapper::first::First;
/// use rustica::traits::foldable::Foldable;
///
/// let a = First(Some(5));
/// let result = a.fold_left(&10, |acc, val| acc + val);
/// assert_eq!(result, 15);
/// ```
///
/// # Semigroup Laws
///
/// First satisfies the semigroup associativity law:
///
/// ```rust
/// use rustica::datatypes::wrapper::first::First;
/// use rustica::traits::semigroup::Semigroup;
///
/// // Verify associativity: (a ⊕ b) ⊕ c = a ⊕ (b ⊕ c)
/// fn verify_associativity<T: Clone + PartialEq>(a: First<T>, b: First<T>, c: First<T>) -> bool {
///     let left = a.clone().combine(&b).combine(&c);
///     let right = a.combine(&b.combine(&c));
///     left == right
/// }
///
/// // Test with various combinations
/// assert!(verify_associativity(First(Some(1)), First(Some(2)), First(Some(3))));
/// assert!(verify_associativity(First(None), First(Some(2)), First(Some(3))));
/// assert!(verify_associativity(First(Some(1)), First(None), First(Some(3))));
/// assert!(verify_associativity(First(Some(1)), First(Some(2)), First(None)));
/// ```
///
/// # Monoid Laws
///
/// First satisfies the monoid identity laws:
///
/// ```rust
/// use rustica::datatypes::wrapper::first::First;
/// use rustica::traits::monoid::Monoid;
/// use rustica::traits::semigroup::Semigroup;
///
/// // Verify left identity: empty() ⊕ a = a
/// fn verify_left_identity<T: Clone + PartialEq>(a: First<T>) -> bool {
///     let empty = First::empty();
///     empty.combine(&a) == a
/// }
///
/// // Verify right identity: a ⊕ empty() = a
/// fn verify_right_identity<T: Clone + PartialEq>(a: First<T>) -> bool {
///     let empty = First::empty();
///     a.combine(&empty) == a
/// }
///
/// // Test with Some and None values
/// assert!(verify_left_identity(First(Some(42))));
/// assert!(verify_left_identity::<i32>(First::empty()));
/// assert!(verify_right_identity(First(Some(42))));
/// assert!(verify_right_identity::<i32>(First::empty()));
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
            Some(value) => write!(f, "First(Some({value}))"),
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

impl<T: Clone> Identity for First<T> {
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
        First(Some(value))
    }
}

impl<T: Clone> Functor for First<T> {
    #[inline]
    fn fmap<U, F>(&self, f: F) -> Self::Output<U>
    where
        F: FnOnce(&Self::Source) -> U,
    {
        match &self.0 {
            Some(value) => First(Some(f(value))),
            None => First(None),
        }
    }

    #[inline]
    fn fmap_owned<U, F>(self, f: F) -> Self::Output<U>
    where
        F: FnOnce(Self::Source) -> U,
    {
        match self.0 {
            Some(value) => First(Some(f(value))),
            None => First(None),
        }
    }
}
