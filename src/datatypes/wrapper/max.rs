//! # Max
//!
//! This module provides the `Max` wrapper type which forms a semigroup under taking the maximum.
//!
//! ## Functional Programming Context
//!
//! The `Max` wrapper is a fundamental building block for functional programming patterns:
//!
//! - **Aggregation**: Provides a principled way to find maximum values
//! - **Transformation**: Works with `Functor` to map inner values while preserving the wrapper
//!
//! ## Type Class Laws
//!
//! ### Semigroup Laws
//!
//! `Max<T>` satisfies the semigroup associativity law:
//!
//! - **Associativity**: `(a ⊕ b) ⊕ c = a ⊕ (b ⊕ c)`
//!   - For all values a, b, and c, combining a and b and then combining the result with c
//!     yields the same result as combining a with the combination of b and c.
//!
//! ### Functor Laws
//!
//! `Max<T>` satisfies the functor laws:
//!
//! - **Identity**: `fmap(id) = id`
//!   - Mapping the identity function over a `Max` value gives the same value.
//!
//! - **Composition**: `fmap(f . g) = fmap(f) . fmap(g)`
//!   - Mapping a composed function is the same as mapping each function in sequence.
//!
//! ## Type Class Implementations
//!
//! `Max<T>` implements the following type classes:
//!
//! - `Semigroup`: For any `T` that implements `Ord`
//! - `Functor`: For mapping operations over the inner value
//!
//! ## Quick Start
//!
//! ```rust
//! use rustica::datatypes::wrapper::max::Max;
//! use rustica::traits::semigroup::Semigroup;
//!
//! // Create Max wrappers
//! let a = Max(5);
//! let b = Max(10);
//! let c = Max(3);
//!
//! // Maximum value wins when combining
//! assert_eq!(a.combine(b), Max(10)); // Larger value wins
//! assert_eq!(b.combine(c), Max(10)); // Keeps maximum
//!
//! // Chaining multiple values
//! let result = a.combine(b).combine(c);
//! assert_eq!(result, Max(10)); // Overall maximum
//! ```

use crate::traits::functor::Functor;
use crate::traits::hkt::HKT;
use crate::traits::semigroup::Semigroup;
use std::cmp::Ordering;
use std::fmt;

/// A wrapper type that forms a semigroup under the maximum operation.
///
/// Empty-capable reductions can use `crate::traits::semigroup::combine_all_values`.
///
/// # Examples
///
/// ```rust
/// use rustica::datatypes::wrapper::max::Max;
/// use rustica::traits::semigroup::Semigroup;
///
/// let a = Max(5);
/// let b = Max(7);
/// let c = a.combine(b);
/// assert_eq!(c, Max(7));
///
/// // Taking the maximum is associative: max(max(a, b), c) = max(a, max(b, c))
/// let x = Max(10);
/// let y = Max(2);
/// let z = Max(6);
/// assert_eq!(x.clone().combine(y.clone()).combine(z.clone()),
///            x.clone().combine(y.clone().combine(z.clone())));
/// ```
///
/// # Semigroup Laws
///
/// The `Max<T>` wrapper satisfies the semigroup associativity law:
///
///
/// Algebraic laws for this wrapper are verified by unit tests.
///
/// # Explicit Extremum Seeds
///
/// When a domain has a known minimum, it can be supplied explicitly as a
/// reduction seed:
///
/// ```rust
/// use rustica::datatypes::wrapper::max::Max;
/// use rustica::traits::semigroup::Semigroup;
///
/// let value = Max(42);
/// let identity = Max(i32::MIN);
/// assert_eq!(value.combine(identity), value);
/// assert_eq!(identity.combine(value), value);
/// ```
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Max<T>(pub T);

impl<T> Max<T> {
    /// Creates a new `Max` wrapping the given value.
    #[inline]
    pub const fn new(value: T) -> Self {
        Max(value)
    }

    /// Consumes the wrapper and returns the contained value.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::wrapper::max::Max;
    /// let max = Max(42);
    /// assert_eq!(max.into_inner(), 42);
    /// ```
    #[inline]
    pub fn into_inner(self) -> T {
        self.0
    }

    /// Returns a reference to the contained value.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::wrapper::max::Max;
    /// let max = Max(42);
    /// assert_eq!(*max.get(), 42);
    /// ```
    #[inline]
    pub fn get(&self) -> &T {
        &self.0
    }
}

impl<T: Clone> Max<T> {
    /// Unwraps the max value.
    #[deprecated(since = "0.15.0", note = "use `into_inner()` or `get()` instead")]
    #[inline]
    pub fn unwrap(&self) -> T {
        self.0.clone()
    }

    /// Unwraps the max value or returns a default.
    #[deprecated(since = "0.15.0", note = "use `into_inner()` or `get()` instead")]
    #[inline]
    pub fn unwrap_or(&self, _default: T) -> T {
        self.0.clone()
    }
}

impl<T> AsRef<T> for Max<T> {
    #[inline]
    fn as_ref(&self) -> &T {
        &self.0
    }
}

impl<T: Ord> Semigroup for Max<T> {
    /// Combines two `Max` values by taking the maximum, consuming self.
    ///
    /// # Examples
    /// ```rust
    /// use rustica::datatypes::wrapper::max::Max;
    /// use rustica::traits::semigroup::Semigroup;
    ///
    /// let a = Max(5);
    /// let b = Max(10);
    /// let c = a.combine(b);
    /// assert_eq!(c, Max(10));
    /// ```
    #[inline]
    fn combine(self, other: Self) -> Self {
        match self.0.cmp(&other.0) {
            Ordering::Greater | Ordering::Equal => self,
            Ordering::Less => other,
        }
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

impl<T: Ord> Functor for Max<T> {
    #[inline]
    fn fmap<U, F>(self, mut f: F) -> Self::Output<U>
    where
        F: FnMut(Self::Source) -> U,
    {
        Max(f(self.0))
    }
}

impl<T> From<T> for Max<T> {
    fn from(value: T) -> Self {
        Max(value)
    }
}
