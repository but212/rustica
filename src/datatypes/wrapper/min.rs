//! # Min
//!
//! This module provides the `Min` wrapper type which forms a semigroup under taking the minimum.
//!
//! ## Functional Programming Context
//!
//! The `Min` wrapper is a fundamental building block for functional programming patterns:
//!
//! - **Aggregation**: Provides a principled way to find minimum values
//! - **Transformation**: Works with `Functor` to map inner values while preserving the wrapper
//!
//! ## Type Class Laws
//!
//! ### Semigroup Laws
//!
//! `Min<T>` satisfies the semigroup associativity law:
//!
//! - **Associativity**: `(a ⊕ b) ⊕ c = a ⊕ (b ⊕ c)`
//!   - For all values a, b, and c, combining a and b and then combining the result with c
//!     yields the same result as combining a with the combination of b and c.
//!
//! ### Functor Laws
//!
//! `Min<T>` satisfies the functor laws:
//!
//! - **Identity**: `fmap(id) = id`
//!   - Mapping the identity function over a `Min` value gives the same value.
//!
//! - **Composition**: `fmap(f . g) = fmap(f) . fmap(g)`
//!   - Mapping a composed function is the same as mapping each function in sequence.
//!
//! ## Type Class Implementations
//!
//! `Min<T>` implements the following type classes:
//!
//! - `Semigroup`: For any `T` that implements `Ord`
//! - `Functor`: For mapping operations over the inner value
//!
//! ## Quick Start
//!
//! ```rust
//! use rustica::datatypes::wrapper::min::Min;
//! use rustica::traits::semigroup::Semigroup;
//!
//! // Create Min wrappers
//! let a = Min(5);
//! let b = Min(10);
//! let c = Min(3);
//!
//! // Minimum value wins when combining
//! assert_eq!(a.combine(b), Min(5)); // Smaller value wins
//! assert_eq!(b.combine(c), Min(3)); // Keeps minimum
//!
//! // Chaining multiple values
//! let result = a.combine(b).combine(c);
//! assert_eq!(result, Min(3)); // Overall minimum
//! ```
use crate::traits::functor::Functor;
use crate::traits::hkt::HKT;
use crate::traits::semigroup::Semigroup;
use std::cmp::Ordering;
use std::fmt;

/// A wrapper type that forms a semigroup under the minimum operation.
///
/// Empty-capable reductions can use `crate::traits::semigroup::combine_all_values`.
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
/// let c = a.combine(b);
/// assert_eq!(c, Min(5));
///
/// // Taking the minimum is associative: min(min(a, b), c) = min(a, min(b, c))
/// let x = Min(10);
/// let y = Min(2);
/// let z = Min(6);
/// assert_eq!(x.clone().combine(y.clone()).combine(z.clone()),
///            x.clone().combine(y.clone().combine(z.clone())));
/// ```
///
/// # Semigroup Laws
///
/// The `Min<T>` wrapper satisfies the semigroup associativity law:
///
///
/// Algebraic laws for this wrapper are verified by unit tests.
///
/// # Explicit Extremum Seeds
///
/// When a domain has a known maximum, it can be supplied explicitly as a
/// reduction seed:
///
/// ```rust
/// use rustica::datatypes::wrapper::min::Min;
/// use rustica::traits::semigroup::Semigroup;
///
/// let value = Min(42);
/// let identity = Min(i32::MAX);
/// assert_eq!(value.combine(identity), value);
/// assert_eq!(identity.combine(value), value);
/// ```
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Min<T>(pub T);

impl<T> Min<T> {
    /// Creates a new `Min` wrapping the given value.
    #[inline]
    pub const fn new(value: T) -> Self {
        Min(value)
    }

    /// Consumes the wrapper and returns the contained value.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::wrapper::min::Min;
    /// let min = Min(42);
    /// assert_eq!(min.into_inner(), 42);
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
    /// use rustica::datatypes::wrapper::min::Min;
    /// let min = Min(42);
    /// assert_eq!(*min.get(), 42);
    /// ```
    #[inline]
    pub fn get(&self) -> &T {
        &self.0
    }
}

impl<T: Clone> Min<T> {
    /// Unwraps the min value.
    #[deprecated(since = "0.15.0", note = "use `into_inner()` or `get()` instead")]
    #[inline]
    pub fn unwrap(&self) -> T {
        self.0.clone()
    }

    /// Unwraps the min value or returns a default.
    #[deprecated(since = "0.15.0", note = "use `into_inner()` or `get()` instead")]
    #[inline]
    pub fn unwrap_or(&self, _default: T) -> T {
        self.0.clone()
    }
}

impl<T> AsRef<T> for Min<T> {
    #[inline]
    fn as_ref(&self) -> &T {
        &self.0
    }
}

impl<T: Ord> Semigroup for Min<T> {
    /// Combines two `Min` values by taking the minimum, consuming self.
    ///
    /// # Examples
    /// ```rust
    /// use rustica::datatypes::wrapper::min::Min;
    /// use rustica::traits::semigroup::Semigroup;
    ///
    /// let a = Min(5);
    /// let b = Min(10);
    /// let c = a.combine(b);
    /// assert_eq!(c, Min(5));
    /// ```
    #[inline]
    fn combine(self, other: Self) -> Self {
        match self.0.cmp(&other.0) {
            Ordering::Less | Ordering::Equal => self,
            Ordering::Greater => other,
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

impl<T: Ord> Functor for Min<T> {
    #[inline]
    fn fmap<U, F>(self, mut f: F) -> Self::Output<U>
    where
        F: FnMut(Self::Source) -> U,
    {
        Min(f(self.0))
    }
}

impl<T> From<T> for Min<T> {
    #[inline]
    fn from(value: T) -> Self {
        Min(value)
    }
}
