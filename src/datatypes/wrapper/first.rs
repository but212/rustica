//! This module provides the `First` wrapper type which forms a semigroup by taking the first non-None value.
//!
//! ## Functional Programming Context
//!
//! The `First` type is a wrapper around `Option<T>` that implements various type classes with specific semantics:
//!
//! - As a `Semigroup`, it combines values by keeping the first non-None value
//! - As a `Monoid`, it uses `None` as its identity element
//! - As a `Functor`, it maps functions over the inner value if present
//!
//! ## Type Class Laws
//!
//! ### Semigroup Laws
//!
//! `First<T>` satisfies the semigroup associativity law:
//!
//! - **Associativity**: `(a ⊕ b) ⊕ c = a ⊕ (b ⊕ c)`
//!   - For all values a, b, and c, combining a and b and then combining the result with c
//!     yields the same result as combining a with the combination of b and c.
//!
//! ### Monoid Laws
//!
//! `First<T>` satisfies the monoid identity laws:
//!
//! - **Left Identity**: `empty() ⊕ a = a`
//!   - Combining the identity element (`First(None)`) with any value gives the original value.
//!
//! - **Right Identity**: `a ⊕ empty() = a`
//!   - Combining any value with the identity element gives the original value.
//!
//! ### Functor Laws
//!
//! `First<T>` satisfies the functor laws:
//!
//! - **Identity**: `fmap(id) = id`
//!   - Mapping the identity function over a `First` value gives the same value.
//!
//! - **Composition**: `fmap(f . g) = fmap(f) . fmap(g)`
//!   - Mapping a composed function is the same as mapping each function in sequence.
//!
//! ## Type Class Implementations
//!
//! `First<T>` implements the following type classes:
//!
//! - `Semigroup`: For any `T` that implements `Clone`
//! - `Monoid`: For any `T` that implements `Clone`
//! - `Functor`: For mapping operations over the inner value
//!
//! ## Quick Start
//!
//! ```rust
//! use rustica::datatypes::wrapper::first::First;
//! use rustica::traits::{semigroup::Semigroup, monoid::Monoid};
//!
//! // Create First wrappers
//! let a = First(Some(42));
//! let b = First(Some(10));
//! let none = First(None);
//!
//! // First non-None value wins
//! assert_eq!(a.combine(b), First(Some(42))); // First value wins
//! assert_eq!(none.combine(b), First(Some(10))); // Second value when first is None
//! assert_eq!(a.combine(none), First(Some(42))); // First value when second is None
//!
//! // Identity element
//! let empty = First::empty();
//! assert_eq!(empty.combine(a), a);
//! assert_eq!(a.combine(empty), a);
//! ```
use crate::traits::functor::Functor;
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
/// Basic usage with the `Semigroup` trait:
///
/// ```rust
/// use rustica::datatypes::wrapper::first::First;
/// use rustica::traits::semigroup::Semigroup;
/// use rustica::traits::monoid::Monoid;
///
/// let a = First(Some(5));
/// let b = First(Some(7));
/// let c = a.combine(b);
/// assert_eq!(c, First(Some(5)));
///
/// // First is associative
/// let x = First(Some(1));
/// let y = First(None);
/// let z = First(Some(3));
/// assert_eq!(x.clone().combine(y.clone()).combine(z.clone()),
///            x.clone().combine(y.clone().combine(z.clone())));
///
/// // Identity element
/// let id = First::empty();  // First(None)
/// assert_eq!(id, First(None));
/// assert_eq!(First(Some(42)).combine(id.clone()), First(Some(42)));
/// assert_eq!(id.combine(First(Some(42))), First(Some(42)));
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
/// let c: First<i32> = First(None);
/// let d = c.fmap(|x| x * 2);
/// assert_eq!(d, First(None));
/// ```
///
/// # Semigroup Laws
///
/// First satisfies the semigroup associativity law:
///
///
/// Algebraic laws for this wrapper are verified by unit tests.
///
/// # Monoid Laws
///
/// First satisfies the monoid identity laws:
///
///
/// Algebraic laws for this wrapper are verified by unit tests.
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[repr(transparent)]
pub struct First<T>(pub Option<T>);

impl<T: Clone> First<T> {
    /// Unwraps the first value, panicking if None.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use rustica::datatypes::wrapper::first::First;
    /// let first = First(Some(42));
    /// assert_eq!(first.unwrap(), 42);
    ///
    /// let empty: First<i32> = First(None);
    /// // empty.unwrap() would panic
    /// ```
    ///
    /// # Panics
    ///
    /// Panics if the inner value is None.
    pub fn unwrap(&self) -> T {
        self.0.clone().unwrap()
    }

    /// Unwraps the first value or returns a default.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use rustica::datatypes::wrapper::first::First;
    /// let first = First(Some(42));
    /// let empty = First(None);
    ///
    /// assert_eq!(first.unwrap_or(0), 42);
    /// assert_eq!(empty.unwrap_or(0), 0);
    /// ```
    pub fn unwrap_or(&self, default: T) -> T {
        self.0.clone().unwrap_or(default)
    }
}

impl<T> AsRef<T> for First<T> {
    #[inline]
    fn as_ref(&self) -> &T {
        self.0
            .as_ref()
            .expect("called `as_ref()` on an empty `First`")
    }
}

impl<T> Semigroup for First<T> {
    /// Combines two `First` values by taking the first non-None value, consuming both values.
    ///
    /// # Examples
    /// ```rust
    /// use rustica::datatypes::wrapper::first::First;
    /// use rustica::traits::semigroup::Semigroup;
    ///
    /// let a = First(Some(5));
    /// let b = First(Some(10));
    /// let c = a.combine(b);
    /// assert_eq!(c, First(Some(5)));
    /// ```
    #[inline]
    fn combine(self, other: Self) -> Self {
        match self.0 {
            Some(_) => self,
            None => other,
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
    /// Returns the identity element for the `First` monoid, which is `First(None)`.
    ///
    /// This method provides the identity element required by the `Monoid` type class.
    /// For `First`, this is represented as `None`, such that combining any value with
    /// `First(None)` returns the original value.
    ///
    /// # Type Class Laws
    ///
    /// ## Left Identity
    ///
    /// ```rust
    /// use rustica::datatypes::wrapper::first::First;
    /// use rustica::traits::monoid::Monoid;
    /// use rustica::traits::semigroup::Semigroup;
    ///
    /// // For any First(x), empty() ⊕ First(x) = First(x)
    /// let empty = First::<i32>::empty();
    /// let value = First(Some(42));
    ///
    /// assert_eq!(empty.combine(value), value);
    /// ```
    ///
    /// ## Right Identity
    ///
    /// ```rust
    /// use rustica::datatypes::wrapper::first::First;
    /// use rustica::traits::monoid::Monoid;
    /// use rustica::traits::semigroup::Semigroup;
    ///
    /// // For any First(x), First(x) ⊕ empty() = First(x)
    /// let value = First(Some(42));
    /// let empty = First::<i32>::empty();
    ///
    /// assert_eq!(value.combine(empty), value);
    /// ```
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::wrapper::first::First;
    /// use rustica::traits::monoid::Monoid;
    ///
    /// // Create an identity element
    /// let empty = First::<String>::empty();
    /// assert_eq!(empty, First(None));
    /// ```
    #[inline]
    fn empty() -> Self {
        First(None)
    }
}

impl<T> HKT for First<T> {
    type Source = T;
    type Output<U> = First<U>;
}

impl<T> Functor for First<T> {
    #[inline]
    fn fmap<U, F>(self, mut f: F) -> Self::Output<U>
    where
        F: FnMut(Self::Source) -> U,
    {
        match self.0 {
            Some(value) => First(Some(f(value))),
            None => First(None),
        }
    }
}

impl<T> From<T> for First<T> {
    #[inline]
    fn from(value: T) -> Self {
        First(Some(value))
    }
}
