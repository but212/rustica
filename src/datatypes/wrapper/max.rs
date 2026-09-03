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
//! assert_eq!(a.combine(&b), Max(10)); // Larger value wins
//! assert_eq!(b.combine(&c), Max(10)); // Keeps maximum
//!
//! // Chaining multiple values
//! let result = a.combine(&b).combine(&c);
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
/// assert_eq!(value.combine(&identity), value);
/// assert_eq!(identity.combine(&value), value);
/// ```
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Max<T>(pub T);

impl<T: Clone> Max<T> {
    /// Unwraps the max value.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use rustica::datatypes::wrapper::max::Max;
    /// let max = Max(42);
    /// assert_eq!(max.unwrap(), 42);
    /// ```
    #[inline]
    pub fn unwrap(&self) -> T {
        self.0.clone()
    }

    /// Unwraps the max value or returns a default.
    ///
    /// Since `Max` always contains a value, this method simply returns the contained value.
    /// The `default` parameter is ignored.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use rustica::datatypes::wrapper::max::Max;
    /// let max = Max(42);
    /// assert_eq!(max.unwrap_or(0), 42);
    /// ```
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

impl<T: Clone + Ord> Semigroup for Max<T> {
    /// Combines two `Max` values by taking the maximum, consuming self.
    ///
    /// This method implements the Semigroup operation for `Max<T>`, which is taking
    /// the maximum of two values. This method consumes both operands.
    ///
    /// # Performance
    ///
    /// - **Time Complexity**: O(1) - Just performs a comparison and returns one of the values
    /// - **Memory Usage**: No additional memory allocation
    /// - **Ownership**: Takes ownership of both `self` and `other`
    ///
    /// # Type Class Laws
    ///
    /// ## Associativity
    ///
    ///
    /// Algebraic laws for this wrapper are verified by unit tests.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::wrapper::max::Max;
    /// use rustica::traits::semigroup::Semigroup;
    ///
    /// let a = Max(5);
    /// let b = Max(10);
    ///
    /// // a and b are consumed
    /// let c = a.combine_owned(b);
    /// assert_eq!(c, Max(10));
    /// ```
    #[inline]
    fn combine_owned(self, other: Self) -> Self {
        match self.0.cmp(&other.0) {
            Ordering::Greater | Ordering::Equal => self,
            Ordering::Less => other,
        }
    }

    /// Combines two `Max` values by taking the maximum, borrowing self.
    ///
    /// This method implements the Semigroup operation for `Max<T>`, which is taking
    /// the maximum of two values. This method borrows both operands and returns a new `Max`.
    ///
    /// # Performance
    ///
    /// - **Time Complexity**: O(1) - Just performs a comparison and clones one of the values
    /// - **Memory Usage**: Creates a new `Max` wrapper with a clone of one of the input values
    /// - **Borrowing**: Borrows `self` and `other`, avoiding unnecessary cloning of both
    ///
    /// # Type Class Laws
    ///
    /// ## Associativity
    ///
    ///
    /// Algebraic laws for this wrapper are verified by unit tests.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::wrapper::max::Max;
    /// use rustica::traits::semigroup::Semigroup;
    ///
    /// let a = Max(5);
    /// let b = Max(10);
    ///
    /// // a and b are borrowed
    /// let c = a.combine(&b);
    /// assert_eq!(c, Max(10));
    ///
    /// // a and b can still be used
    /// let d = b.combine(&a);
    /// assert_eq!(d, Max(10));
    /// ```
    #[inline]
    fn combine(&self, other: &Self) -> Self {
        match self.0.cmp(&other.0) {
            Ordering::Greater | Ordering::Equal => Max(self.0.clone()),
            Ordering::Less => Max(other.0.clone()),
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

impl<T: Clone + Ord> Functor for Max<T> {
    /// Maps a function over the value contained in this `Max` wrapper.
    ///
    /// This method implements the Functor typeclass by applying the function `f`
    /// to the inner value and wrapping the result in a new `Max` container.
    /// This method borrows the inner value, avoiding consumption.
    ///
    /// # Performance
    ///
    /// - **Time Complexity**: O(1) plus the complexity of function `f`
    /// - **Memory Usage**: Creates a new `Max` wrapper with the transformed value
    /// - **Borrowing**: Takes a reference to the inner value, avoiding cloning it
    ///
    /// # Type Class Laws
    ///
    /// ## Identity Law
    ///
    ///
    /// Algebraic laws for this wrapper are verified by unit tests.
    ///
    /// ## Composition Law
    ///
    ///
    /// Algebraic laws for this wrapper are verified by unit tests.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::wrapper::max::Max;
    /// use rustica::traits::functor::Functor;
    ///
    /// let max_value = Max(5);
    /// let doubled = max_value.fmap(|x| x * 2);
    /// assert_eq!(doubled, Max(10));
    /// ```
    #[inline]
    fn fmap<U, F>(&self, f: F) -> Self::Output<U>
    where
        F: FnOnce(&Self::Source) -> U,
    {
        Max(f(&self.0))
    }

    /// Maps a function over the value contained in this `Max` wrapper, consuming it.
    ///
    /// This method is similar to `fmap` but takes ownership of `self` and passes
    /// ownership of the inner value to the mapping function. This avoids unnecessary
    /// cloning when the original value is no longer needed.
    ///
    /// # Performance
    ///
    /// - **Time Complexity**: O(1) plus the complexity of function `f`
    /// - **Memory Usage**: Creates a new `Max` wrapper with the transformed value
    /// - **Ownership**: Consumes `self`, avoiding unnecessary cloning
    ///
    /// # Type Class Laws
    ///
    /// The same functor laws apply as for `fmap`, but with ownership semantics.
    ///
    /// # Examples
    ///
    /// Basic transformation with ownership:
    ///
    /// ```rust
    /// use rustica::datatypes::wrapper::max::Max;
    /// use rustica::traits::functor::Functor;
    ///
    /// let max_string = Max(String::from("hello"));
    ///
    /// // Efficiently transform without cloning the string
    /// let max_length = max_string.fmap_owned(|s| s.len());
    /// assert_eq!(max_length, Max(5));
    ///
    /// // Note: max_string has been consumed and can't be used anymore
    /// ```
    #[inline]
    fn fmap_owned<U, F>(self, f: F) -> Self::Output<U>
    where
        F: FnOnce(Self::Source) -> U,
        Self::Source: Ord,
    {
        Max(f(self.0))
    }
}

impl<T> From<T> for Max<T> {
    fn from(value: T) -> Self {
        Max(value)
    }
}
