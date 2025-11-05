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
//! ### Monoid Laws
//!
//! When `T` has a minimum value, `Max<T>` also satisfies the monoid identity laws:
//!
//! - **Left Identity**: `empty() ⊕ a = a`
//!   - Combining the identity element (typically the minimum value of `T`) with any value gives the original value.
//!
//! - **Right Identity**: `a ⊕ empty() = a`
//!   - Combining any value with the identity element gives the original value.
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
//! ## Performance Characteristics
//!
//! - Time Complexity: All operations (`combine`, `empty`, `fmap`, etc.) are O(1)
//! - Memory Usage: Stores exactly one value of type `T` with no additional overhead
//! - Clone Cost: Depends on the cost of cloning the inner type `T`
//!
//! ## Type Class Implementations
//!
//! `Max<T>` implements the following type classes:
//!
//! - `Semigroup`: For any `T` that implements `Ord`
//! - `Monoid`: For any `T` that implements `Ord` and has a minimum value
//! - `Functor`: For mapping operations over the inner value
//! - `Identity`: For accessing the inner value
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
//!
//! ## Documentation Notes
//!
//! For detailed practical examples demonstrating the type class laws, usage patterns, and
//! performance characteristics, please refer to the function-level documentation of the
//! relevant methods such as `combine`, `empty`, `fmap`, and others.

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
    /// ```rust
    /// use rustica::datatypes::wrapper::max::Max;
    /// use rustica::traits::semigroup::Semigroup;
    ///
    /// // For any a, b, c: (a ⊕ b) ⊕ c = a ⊕ (b ⊕ c)
    /// // where ⊕ is the combine operation
    /// fn verify_associativity<T: Clone + Ord>(a: T, b: T, c: T) -> bool {
    ///     let max_a = Max(a);
    ///     let max_b = Max(b);
    ///     let max_c = Max(c);
    ///     
    ///     let left = max_a.clone().combine_owned(max_b.clone()).combine_owned(max_c.clone());
    ///     let right = max_a.combine_owned(max_b.combine_owned(max_c));
    ///     
    ///     left == right
    /// }
    ///
    /// assert!(verify_associativity(1, 5, 3));
    /// assert!(verify_associativity(10, 2, 7));
    /// assert!(verify_associativity(-5, -10, -3));
    /// ```
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
    /// ```rust
    /// use rustica::datatypes::wrapper::max::Max;
    /// use rustica::traits::semigroup::Semigroup;
    ///
    /// // For any a, b, c: (a ⊕ b) ⊕ c = a ⊕ (b ⊕ c)
    /// // where ⊕ is the combine operation
    /// fn verify_associativity<T: Clone + Ord + PartialEq>(a: T, b: T, c: T) -> bool {
    ///     let max_a = Max(a);
    ///     let max_b = Max(b);
    ///     let max_c = Max(c);
    ///     
    ///     let left = max_a.combine(&max_b).combine(&max_c);
    ///     let right = max_a.combine(&max_b.combine(&max_c));
    ///     
    ///     left == right
    /// }
    ///
    /// assert!(verify_associativity(1, 5, 3));
    /// assert!(verify_associativity(10, 2, 7));
    /// assert!(verify_associativity(-5, -10, -3));
    /// ```
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

impl<T: Clone + Ord + Default> Monoid for Max<T> {
    /// Returns the identity element for the `Max` monoid, which is `Max(T::default())`,
    /// typically the minimum possible value of `T`.
    ///
    /// For numeric types, this is usually the minimum possible value (e.g., MIN_INT for integers).
    /// When combined with any other `Max` value, the result will always be the other value.
    ///
    /// # Performance
    ///
    /// - **Time Complexity**: O(1) - Simply creates a wrapper with the default value
    /// - **Memory Usage**: Space required for the wrapper and the default value of type T
    /// - **Allocation**: Any allocations required by T::default() implementation
    ///
    /// # Type Class Laws
    ///
    /// ## Left Identity
    ///
    /// ```rust
    /// use rustica::datatypes::wrapper::max::Max;
    /// use rustica::traits::monoid::Monoid;
    /// use rustica::traits::semigroup::Semigroup;
    ///
    /// // For any Max(x), empty() ⊕ Max(x) = Max(x)
    /// fn verify_left_identity<T: Clone + Ord + Default + PartialEq>(x: T) -> bool {
    ///     let empty = Max::<T>::empty();
    ///     let value = Max(x);
    ///     
    ///     empty.combine(&value) == value
    /// }
    ///
    /// assert!(verify_left_identity(42));
    /// assert!(verify_left_identity(0));
    /// ```
    ///
    /// ## Right Identity
    ///
    /// ```rust
    /// use rustica::datatypes::wrapper::max::Max;
    /// use rustica::traits::monoid::Monoid;
    /// use rustica::traits::semigroup::Semigroup;
    ///
    /// // For any Max(x), Max(x) ⊕ empty() = Max(x)
    /// fn verify_right_identity<T: Clone + Ord + Default + PartialEq>(x: T) -> bool {
    ///     let value = Max(x);
    ///     let empty = Max::<T>::empty();
    ///     
    ///     value.combine(&empty) == value
    /// }
    ///
    /// assert!(verify_right_identity(42));
    /// assert!(verify_right_identity(0));
    /// ```
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::wrapper::max::Max;
    /// use rustica::traits::monoid::Monoid;
    /// use rustica::traits::semigroup::Semigroup;
    ///
    /// // Create an identity element for integers
    /// let empty = Max::<i32>::empty();
    /// assert_eq!(empty, Max(i32::default()));
    ///
    /// let empty_i64 = Max::<i64>::empty();
    /// assert_eq!(empty_i64, Max(i64::default()));
    /// ```
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
    /// ```rust
    /// use rustica::datatypes::wrapper::max::Max;
    /// use rustica::traits::functor::Functor;
    ///
    /// // For any Max(x), fmap(id) = id
    /// // where id is the identity function
    /// fn verify_identity_law<T: Clone + Ord + PartialEq>(x: T) -> bool {
    ///     let max_x = Max(x.clone());
    ///     let mapped = max_x.fmap(|a| a.clone());
    ///     mapped == max_x
    /// }
    ///
    /// // Test with various values
    /// assert!(verify_identity_law(42));
    /// assert!(verify_identity_law(-7));
    /// assert!(verify_identity_law(0));
    /// ```
    ///
    /// ## Composition Law
    ///
    /// ```rust
    /// use rustica::datatypes::wrapper::max::Max;
    /// use rustica::traits::functor::Functor;
    ///
    /// // For any Max(x) and functions f and g:
    /// // fmap(f . g) = fmap(f) . fmap(g)
    /// fn verify_composition_law<T>(x: T) -> bool
    /// where
    ///     T: Clone + Ord + PartialEq + std::fmt::Display,
    /// {
    ///     let max_x = Max(x);
    ///     
    ///     // Define two functions to compose
    ///     let f = |x: &String| x.len();
    ///     let g = |x: &T| x.to_string();
    ///     
    ///     // Left side: fmap(f . g)
    ///     let left_side = max_x.clone().fmap(|a| f(&g(a)));
    ///     
    ///     // Right side: fmap(f) . fmap(g)
    ///     let right_side = max_x.clone().fmap(g).fmap(f);
    ///     
    ///     left_side == right_side
    /// }
    ///
    /// // Test with a value that can be converted to String
    /// assert!(verify_composition_law(42));
    /// ```
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
