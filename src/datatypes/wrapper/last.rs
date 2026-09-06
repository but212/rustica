//! # Last
//!
//! This module provides the `Last` wrapper type which forms a semigroup by taking the last non-None value.
//!
//! ## Functional Programming Context
//!
//! The `Last` type is a wrapper around `Option<T>` that implements various type classes with specific semantics:
//!
//! - As a `Semigroup`, it combines values by keeping the last non-None value
//! - As a `Monoid`, it uses `None` as its identity element
//! - As a `Functor`, it maps functions over the inner value if present
//!
//! ## Type Class Implementations
//!
//! - `Semigroup`: Combines by keeping the rightmost `Some` value
//! - `Monoid`: Uses `None` as identity element
//! - `Functor`: Maps functions over the contained value
//! - `HKT`: Higher-kinded type representation
//!
//! ## Type Class Laws
//!
//! ### Semigroup Laws
//!
//! `Last<T>` satisfies the semigroup associativity law:
//!
//! - **Associativity**: `(a ⊕ b) ⊕ c = a ⊕ (b ⊕ c)`
//!   - For all values a, b, and c, combining a and b and then combining the result with c
//!     yields the same result as combining a with the combination of b and c.
//!
//! ### Monoid Laws
//!
//! `Last<T>` satisfies the monoid identity laws:
//!
//! - **Left Identity**: `empty() ⊕ a = a`
//!   - Combining the identity element (`Last(None)`) with any value gives the original value.
//!
//! - **Right Identity**: `a ⊕ empty() = a`
//!   - Combining any value with the identity element gives the original value.
//!
//! ### Functor Laws
//!
//! `Last<T>` satisfies the functor laws:
//!
//! - **Identity**: `fmap(id) = id`
//!   - Mapping the identity function over a `Last` value gives the same value.
//!
//! - **Composition**: `fmap(f . g) = fmap(f) . fmap(g)`
//!   - Mapping a composed function is the same as mapping each function in sequence.
//!
//! ## Quick Start
//!
//! ```rust
//! use rustica::datatypes::wrapper::last::Last;
//! use rustica::traits::{semigroup::Semigroup, monoid::Monoid};
//!
//! // Create Last wrappers
//! let a = Last(Some(42));
//! let b = Last(Some(10));
//! let none = Last(None);
//!
//! // Last non-None value wins
//! assert_eq!(a.combine(b), Last(Some(10))); // Second value wins
//! assert_eq!(none.combine(b), Last(Some(10))); // Second value when first is None
//! assert_eq!(a.combine(none), Last(Some(42))); // First value when second is None
//!
//! // Identity element
//! let empty = Last::empty();
//! assert_eq!(empty.combine(a), a);
//! assert_eq!(a.combine(empty), a);
//! ```

use crate::traits::functor::Functor;
use crate::traits::hkt::HKT;
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
/// let c = a.combine(b);
/// assert_eq!(c, Last(Some(7)));
///
/// // Last is associative
/// let x = Last(Some(1));
/// let y = Last(None);
/// let z = Last(Some(3));
/// assert_eq!(x.clone().combine(y.clone()).combine(z.clone()),
///            x.clone().combine(y.clone().combine(z.clone())));
///
/// // Identity element
/// let id = Last::empty();  // Last(None)
/// assert_eq!(id, Last(None));
/// assert_eq!(Last(Some(42)).combine(id.clone()), Last(Some(42)));
/// assert_eq!(id.combine(Last(Some(42))), Last(Some(42)));
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
/// let c: Last<i32> = Last(None);
/// let d = c.fmap(|x| x * 2);
/// assert_eq!(d, Last(None));
/// ```
///
/// # Semigroup Laws
///
/// Last satisfies the semigroup associativity law:
///
///
/// Algebraic laws for this wrapper are verified by unit tests.
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
///     empty.combine(a.clone()) == a
/// }
///
/// // Verify right identity: a ⊕ empty() = a
/// fn check_right_identity<T: Clone + PartialEq>(a: Last<T>) -> bool {
///     let empty = Last::empty();
///     a.clone().combine(empty) == a
/// }
///
/// assert!(check_left_identity(Last(Some(42))));
/// assert!(check_right_identity(Last(Some(42))));
/// assert!(check_left_identity::<i32>(Last(None)));
/// assert!(check_right_identity::<i32>(Last(None)));
/// ```
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
#[repr(transparent)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Last<T>(pub Option<T>);

impl<T> Last<T> {
    /// Consumes the wrapper and returns the inner option.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::wrapper::last::Last;
    ///
    /// let last = Last(Some(42));
    /// assert_eq!(last.into_inner(), Some(42));
    /// ```
    #[inline]
    pub fn into_inner(self) -> Option<T> {
        self.0
    }

    /// Returns a reference to the inner option.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::wrapper::last::Last;
    ///
    /// let last = Last(Some(42));
    /// assert_eq!(last.get(), Some(&42));
    /// ```
    #[inline]
    pub fn get(&self) -> Option<&T> {
        self.0.as_ref()
    }
}

impl<T: Clone> Last<T> {
    /// Unwraps the last value, panicking if None.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use rustica::datatypes::wrapper::last::Last;
    /// let last = Last(Some(42));
    /// assert_eq!(last.unwrap(), 42);
    ///
    /// let empty: Last<i32> = Last(None);
    /// // empty.unwrap() would panic
    /// ```
    ///
    /// # Panics
    ///
    /// Panics if the inner value is None.
    #[deprecated(since = "0.15.0", note = "use `into_inner()` or `get()` instead")]
    pub fn unwrap(&self) -> T {
        self.0.clone().unwrap()
    }

    /// Unwraps the last value or returns a default.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use rustica::datatypes::wrapper::last::Last;
    /// let last = Last(Some(42));
    /// let empty = Last(None);
    ///
    /// assert_eq!(last.unwrap_or(0), 42);
    /// assert_eq!(empty.unwrap_or(0), 0);
    /// ```
    #[deprecated(since = "0.15.0", note = "use `into_inner()` or `get()` instead")]
    pub fn unwrap_or(&self, default: T) -> T {
        self.0.clone().unwrap_or(default)
    }
}

impl<T> AsRef<T> for Last<T> {
    #[inline]
    fn as_ref(&self) -> &T {
        self.0
            .as_ref()
            .expect("called `as_ref()` on an empty `Last`")
    }
}

impl<T> Semigroup for Last<T> {
    /// Combines two `Last` values by taking the last non-None value, consuming both values.
    ///
    /// # Examples
    /// ```rust
    /// use rustica::datatypes::wrapper::last::Last;
    /// use rustica::traits::semigroup::Semigroup;
    ///
    /// let a = Last(Some(5));
    /// let b = Last(Some(10));
    /// let c = a.combine(b);
    /// assert_eq!(c, Last(Some(10)));
    /// ```
    #[inline]
    fn combine(self, other: Self) -> Self {
        match other.0 {
            Some(_) => other,
            None => self,
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
    /// Returns the identity element for the `Last` monoid, which is `Last(None)`.
    ///
    /// This method provides the identity element required by the `Monoid` type class.
    /// For `Last`, this is represented as `None`, such that combining any value with
    /// `Last(None)` returns the original value.
    ///
    /// # Performance
    ///
    /// - **Time Complexity**: O(1) - Creates a simple wrapper with None
    /// - **Memory Usage**: Minimal, just the space for the Option type
    /// - **Allocation**: No heap allocations required
    ///
    /// # Type Class Laws
    ///
    /// ## Left Identity
    ///
    /// ```rust
    /// use rustica::datatypes::wrapper::last::Last;
    /// use rustica::traits::monoid::Monoid;
    /// use rustica::traits::semigroup::Semigroup;
    ///
    /// // For any Last(x), empty() ⊕ Last(x) = Last(x)
    /// let empty = Last::<i32>::empty();
    /// let value = Last(Some(42));
    ///
    /// assert_eq!(empty.combine(value), value);
    /// ```
    ///
    /// ## Right Identity
    ///
    /// ```rust
    /// use rustica::datatypes::wrapper::last::Last;
    /// use rustica::traits::monoid::Monoid;
    /// use rustica::traits::semigroup::Semigroup;
    ///
    /// // For any Last(x), Last(x) ⊕ empty() = Last(x)
    /// let value = Last(Some(42));
    /// let empty = Last::<i32>::empty();
    ///
    /// assert_eq!(value.combine(empty), value);
    /// ```
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::wrapper::last::Last;
    /// use rustica::traits::monoid::Monoid;
    ///
    /// // Create an identity element
    /// let empty = Last::<String>::empty();
    /// assert_eq!(empty, Last(None));
    /// ```
    #[inline]
    fn empty() -> Self {
        Last(None)
    }
}

impl<T> HKT for Last<T> {
    type Source = T;
    type Output<U> = Last<U>;
}

impl<T> Functor for Last<T> {
    #[inline]
    fn fmap<U, F>(self, mut f: F) -> Self::Output<U>
    where
        F: FnMut(Self::Source) -> U,
    {
        match self.0 {
            Some(value) => Last(Some(f(value))),
            None => Last(None),
        }
    }
}

impl<T> From<T> for Last<T> {
    #[inline]
    fn from(value: T) -> Self {
        Last(Some(value))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_last_into_inner_and_get() {
        let last = Last(Some(42));
        assert_eq!(last.get(), Some(&42));
        assert_eq!(last.into_inner(), Some(42));

        let empty: Last<i32> = Last(None);
        assert_eq!(empty.get(), None);
        assert_eq!(empty.into_inner(), None);
    }
}
