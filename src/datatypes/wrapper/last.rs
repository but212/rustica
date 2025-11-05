//! # Last
//!
//! This module provides the `Last` wrapper type which forms a semigroup by taking the last non-Maybe::Nothing value.
//!
//! ## Functional Programming Context
//!
//! The `Last` type is a wrapper around `Maybe<T>` that implements various type classes with specific semantics:
//!
//! - As a `Semigroup`, it combines values by keeping the last non-Maybe::Nothing value
//! - As a `Monoid`, it uses `Maybe::Nothing` as its identity element
//! - As a `Functor`, it maps functions over the inner value if present
//!
//! ## Type Class Implementations
//!
//! - `Semigroup`: Combines by keeping the rightmost `Maybe::Just` value
//! - `Monoid`: Uses `Maybe::Nothing` as identity element
//! - `Functor`: Maps functions over the contained value
//! - `Identity`: Provides access to the wrapped value
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
//!   - Combining the identity element (`Last(Maybe::Nothing)`) with any value gives the original value.
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
//! ## Performance Characteristics
//!
//! - Time Complexity: All operations (`combine`, `empty`, `fmap`, etc.) are O(1)
//! - Memory Usage: Stores exactly one `Maybe<T>` value with no additional overhead
//! - Clone Cost: Depends on the cost of cloning the inner type `T`
//!
//! ## Quick Start
//!
//! ```rust
//! use rustica::datatypes::maybe::Maybe;
//! use rustica::datatypes::wrapper::last::Last;
//! use rustica::traits::{semigroup::Semigroup, monoid::Monoid};
//!
//! // Create Last wrappers
//! let a = Last(Maybe::Just(42));
//! let b = Last(Maybe::Just(10));
//! let none = Last(Maybe::Nothing);
//!
//! // Last non-Maybe::Nothing value wins
//! assert_eq!(a.combine(&b), Last(Maybe::Just(10))); // Second value wins
//! assert_eq!(none.combine(&b), Last(Maybe::Just(10))); // Second value when first is Maybe::Nothing
//! assert_eq!(a.combine(&none), Last(Maybe::Just(42))); // First value when second is Maybe::Nothing
//!
//! // Identity element
//! let empty = Last::empty();
//! assert_eq!(empty.combine(&a), a);
//! assert_eq!(a.combine(&empty), a);
//! ```
//!
//! ## Documentation Notes
//!
//! For detailed practical examples demonstrating the type class laws, usage patterns, and
//! performance characteristics, please refer to the function-level documentation of the
//! relevant methods such as `combine`, `empty`, `fmap`, and others.

use crate::prelude::Maybe;
use crate::traits::functor::Functor;
use crate::traits::hkt::HKT;
use crate::traits::identity::Identity;
use crate::traits::monoid::Monoid;
use crate::traits::semigroup::Semigroup;
use std::fmt;

/// A wrapper type that forms a semigroup by taking the last non-Maybe::Nothing value.
///
/// The monoid instance uses `Maybe::Nothing` as the identity element.
///
/// # Examples
///
/// Basic usage with the `Semigroup` trait:
///
/// ```rust
/// use rustica::datatypes::maybe::Maybe;
/// use rustica::datatypes::wrapper::last::Last;
/// use rustica::traits::semigroup::Semigroup;
/// use rustica::traits::monoid::Monoid;
///
/// let a = Last(Maybe::Just(5));
/// let b = Last(Maybe::Just(7));
/// let c = a.combine(&b);
/// assert_eq!(c, Last(Maybe::Just(7)));
///
/// // Last is associative
/// let x = Last(Maybe::Just(1));
/// let y = Last(Maybe::Nothing);
/// let z = Last(Maybe::Just(3));
/// assert_eq!(x.clone().combine(&y.clone()).combine(&z.clone()),
///            x.clone().combine(&y.clone().combine(&z.clone())));
///
/// // Identity element
/// let id = Last::empty();  // Last(Maybe::Nothing)
/// assert_eq!(id, Last(Maybe::Nothing));
/// assert_eq!(Last(Maybe::Just(42)).combine(&id.clone()), Last(Maybe::Just(42)));
/// assert_eq!(id.combine(&Last(Maybe::Just(42))), Last(Maybe::Just(42)));
/// ```
///
/// Using with `Functor` to transform the inner value:
///
/// ```rust
/// use rustica::datatypes::maybe::Maybe;
/// use rustica::datatypes::wrapper::last::Last;
/// use rustica::traits::functor::Functor;
///
/// let a = Last(Maybe::Just(5));
/// let b = a.fmap(|x| x * 2);
/// assert_eq!(b, Last(Maybe::Just(10)));
///
/// let c = Last(Maybe::Nothing);
/// let d = c.fmap(|x| x * 2);
/// assert_eq!(d, Last(Maybe::Nothing));
/// ```
///
/// # Semigroup Laws
///
/// Last satisfies the semigroup associativity law:
///
/// ```rust
/// use rustica::datatypes::maybe::Maybe;
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
/// assert!(check_associativity(Last(Maybe::Just(1)), Last(Maybe::Just(2)), Last(Maybe::Just(3))));
/// assert!(check_associativity(Last(Maybe::Just(1)), Last(Maybe::Nothing), Last(Maybe::Just(3))));
/// assert!(check_associativity(Last(Maybe::Nothing), Last(Maybe::Just(2)), Last(Maybe::Nothing)));
/// ```
///
/// # Monoid Laws
///
/// Last satisfies the monoid identity laws:
///
/// ```rust
/// use rustica::datatypes::maybe::Maybe;
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
/// assert!(check_left_identity(Last(Maybe::Just(42))));
/// assert!(check_right_identity(Last(Maybe::Just(42))));
/// assert!(check_left_identity::<i32>(Last(Maybe::Nothing)));
/// assert!(check_right_identity::<i32>(Last(Maybe::Nothing)));
/// ```
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
#[repr(transparent)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Last<T>(pub Maybe<T>);

impl<T: Clone> Last<T> {
    /// Unwraps the last value, panicking if Maybe::Nothing.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::maybe::Maybe;
    /// # use rustica::datatypes::wrapper::last::Last;
    /// let last = Last(Maybe::Just(42));
    /// assert_eq!(last.unwrap(), 42);
    ///
    /// let empty: Last<i32> = Last(Maybe::Nothing);
    /// // empty.unwrap() would panic
    /// ```
    ///
    /// # Panics
    ///
    /// Panics if the inner value is Maybe::Nothing.
    pub fn unwrap(&self) -> T {
        self.0.clone().unwrap()
    }

    /// Unwraps the last value or returns a default.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::maybe::Maybe;
    /// # use rustica::datatypes::wrapper::last::Last;
    /// let last = Last(Maybe::Just(42));
    /// let empty = Last(Maybe::Nothing);
    ///
    /// assert_eq!(last.unwrap_or(0), 42);
    /// assert_eq!(empty.unwrap_or(0), 0);
    /// ```
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

impl<T: Clone> Semigroup for Last<T> {
    /// Combines two `Last` values by taking the last non-Maybe::Nothing value, consuming both values.
    ///
    /// This is the owned version of the semigroup operation that takes ownership of both `self` and `other`.
    /// It returns the second value if it contains `Maybe::Just`, otherwise it returns the first value.
    ///
    /// # Performance
    ///
    /// - **Time Complexity**: O(1) - Simply checks if the second value is Maybe::Just
    /// - **Memory Usage**: No additional allocations, just pattern matching
    /// - **Ownership**: Consumes both values, avoiding unnecessary clones
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::maybe::Maybe;
    /// use rustica::datatypes::wrapper::last::Last;
    /// use rustica::traits::semigroup::Semigroup;
    ///
    /// // When second value is Maybe::Just
    /// let a = Last(Maybe::Just(5));
    /// let b = Last(Maybe::Just(10));
    /// let c = a.combine_owned(b);
    /// assert_eq!(c, Last(Maybe::Just(10)));
    ///
    /// // When second value is Maybe::Nothing
    /// let x = Last(Maybe::Just(7));
    /// let y = Last(Maybe::Nothing);
    /// let z = x.combine_owned(y);
    /// assert_eq!(z, Last(Maybe::Just(7)));
    ///
    /// // When both values are Maybe::Nothing
    /// let p = Last::<i32>(Maybe::Nothing);
    /// let q = Last::<i32>(Maybe::Nothing);
    /// let r = p.combine_owned(q);
    /// assert_eq!(r, Last(Maybe::Nothing));
    /// ```
    #[inline]
    fn combine_owned(self, other: Self) -> Self {
        match other.0 {
            Maybe::Just(_) => other,
            Maybe::Nothing => self,
        }
    }

    /// Combines two `Last` values by taking the last non-Maybe::Nothing value, preserving the originals.
    ///
    /// This method implements the semigroup operation for `Last` by returning a new `Last`
    /// containing the last non-Maybe::Nothing value from either `self` or `other`. If both contain `Maybe::Nothing`,
    /// the result will be `Last(Maybe::Nothing)`.
    ///
    /// # Performance
    ///
    /// - **Time Complexity**: O(1) - Simply checks if the second value is Maybe::Just
    /// - **Memory Usage**: Requires cloning the inner value when returning a result
    /// - **Borrowing**: Takes references to both values, requiring `T: Clone`
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::maybe::Maybe;
    /// use rustica::datatypes::wrapper::last::Last;
    /// use rustica::traits::semigroup::Semigroup;
    ///
    /// // When second value is Maybe::Just
    /// let a = Last(Maybe::Just(5));
    /// let b = Last(Maybe::Just(10));
    /// let c = a.combine(&b);
    /// assert_eq!(c, Last(Maybe::Just(10)));
    /// // Original values are preserved
    /// assert_eq!(a, Last(Maybe::Just(5)));
    /// assert_eq!(b, Last(Maybe::Just(10)));
    ///
    /// // When second value is Maybe::Nothing
    /// let x = Last(Maybe::Just(7));
    /// let y = Last(Maybe::Nothing);
    /// let z = x.combine(&y);
    /// assert_eq!(z, Last(Maybe::Just(7)));
    ///
    /// // Demonstrating associativity
    /// let v1 = Last(Maybe::Nothing);
    /// let v2 = Last(Maybe::Just(10));
    /// let v3 = Last(Maybe::Just(20));
    ///
    /// // (v1 ⊕ v2) ⊕ v3 = v1 ⊕ (v2 ⊕ v3)
    /// let left = v1.combine(&v2).combine(&v3);
    /// let right = v1.combine(&v2.combine(&v3));
    /// assert_eq!(left, right);
    /// ```
    #[inline]
    fn combine(&self, other: &Self) -> Self {
        match &other.0 {
            Maybe::Just(_) => Last(other.0.clone()),
            Maybe::Nothing => Last(self.0.clone()),
        }
    }
}

impl<T: fmt::Display> fmt::Display for Last<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.0 {
            Maybe::Just(value) => write!(f, "Last(Maybe::Just({value}))"),
            Maybe::Nothing => write!(f, "Last(Maybe::Nothing)"),
        }
    }
}

impl<T: Clone> Monoid for Last<T> {
    /// Returns the identity element for the `Last` monoid, which is `Last(Maybe::Nothing)`.
    ///
    /// This method provides the identity element required by the `Monoid` type class.
    /// For `Last`, this is represented as `Maybe::Nothing`, such that combining any value with
    /// `Last(Maybe::Nothing)` returns the original value.
    ///
    /// # Performance
    ///
    /// - **Time Complexity**: O(1) - Creates a simple wrapper with Maybe::Nothing
    /// - **Memory Usage**: Minimal, just the space for the Maybe type
    /// - **Allocation**: No heap allocations required
    ///
    /// # Type Class Laws
    ///
    /// ## Left Identity
    ///
    /// ```rust
    /// use rustica::datatypes::maybe::Maybe;
    /// use rustica::datatypes::wrapper::last::Last;
    /// use rustica::traits::monoid::Monoid;
    /// use rustica::traits::semigroup::Semigroup;
    ///
    /// // For any Last(x), empty() ⊕ Last(x) = Last(x)
    /// let empty = Last::<i32>::empty();
    /// let value = Last(Maybe::Just(42));
    ///
    /// assert_eq!(empty.combine(&value), value);
    /// ```
    ///
    /// ## Right Identity
    ///
    /// ```rust
    /// use rustica::datatypes::maybe::Maybe;
    /// use rustica::datatypes::wrapper::last::Last;
    /// use rustica::traits::monoid::Monoid;
    /// use rustica::traits::semigroup::Semigroup;
    ///
    /// // For any Last(x), Last(x) ⊕ empty() = Last(x)
    /// let value = Last(Maybe::Just(42));
    /// let empty = Last::<i32>::empty();
    ///
    /// assert_eq!(value.combine(&empty), value);
    /// ```
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::maybe::Maybe;
    /// use rustica::datatypes::wrapper::last::Last;
    /// use rustica::traits::monoid::Monoid;
    ///
    /// // Create an identity element
    /// let empty = Last::<String>::empty();
    /// assert_eq!(empty, Last(Maybe::Nothing));
    /// ```
    #[inline]
    fn empty() -> Self {
        Last(Maybe::Nothing)
    }
}

impl<T> HKT for Last<T> {
    type Source = T;
    type Output<U> = Last<U>;
}

impl<T: Clone> Identity for Last<T> {
    fn value(&self) -> &Self::Source {
        self.0.as_ref().unwrap()
    }

    fn into_value(self) -> Self::Source {
        self.0.unwrap()
    }
}

impl<T: Clone> Functor for Last<T> {
    /// Maps a function over the inner value of this `Last` container, if it exists.
    ///
    /// This method applies the function `f` to the inner value if it's `Maybe::Just`,
    /// otherwise it returns `Last(Maybe::Nothing)`. This borrows the inner value during the mapping.
    ///
    /// # Performance
    ///
    /// - **Time Complexity**: O(1) plus the complexity of function `f`
    /// - **Memory Usage**: Creates a new `Last` wrapper with the transformed value
    /// - **Borrowing**: Takes a reference to the inner value, avoiding unnecessary clones
    ///
    /// # Type Class Laws
    ///
    /// ## Identity Law
    ///
    /// ```rust
    /// use rustica::datatypes::maybe::Maybe;
    /// use rustica::datatypes::wrapper::last::Last;
    /// use rustica::traits::functor::Functor;
    ///
    /// // For any Last(x), fmap(id) = id
    /// // where id is the identity function
    /// fn verify_identity_law<T: Clone + PartialEq>(x: Last<T>) -> bool {
    ///     let mapped = x.clone().fmap(|a| a.clone());
    ///     mapped == x
    /// }
    ///
    /// // Test with Maybe::Just value
    /// assert!(verify_identity_law(Last(Maybe::Just(42))));
    ///
    /// // Test with Maybe::Nothing value
    /// assert!(verify_identity_law(Last::<i32>(Maybe::Nothing)));
    /// ```
    ///
    /// ## Composition Law
    ///
    /// ```rust
    /// use rustica::datatypes::maybe::Maybe;
    /// use rustica::datatypes::wrapper::last::Last;
    /// use rustica::traits::functor::Functor;
    ///
    /// // For any Last(x) and functions f and g:
    /// // fmap(f . g) = fmap(f) . fmap(g)
    /// fn verify_composition_law<T>(x: Last<T>) -> bool
    /// where
    ///     T: Clone + PartialEq + std::fmt::Debug,
    ///     i32: From<T>,
    /// {
    ///     let f = |x: &i32| x * 2;
    ///     let g = |x: &T| i32::from(x.clone()) + 1;
    ///     
    ///     let left_side = x.clone().fmap(|a| f(&g(a)));
    ///     let right_side = x.clone().fmap(g).fmap(f);
    ///     
    ///     left_side == right_side
    /// }
    ///
    /// // Test with Maybe::Just value (using i32 which implements From<i32>)
    /// assert!(verify_composition_law(Last(Maybe::Just(5))));
    ///
    /// // Test with Maybe::Nothing value
    /// assert!(verify_composition_law(Last::<i32>(Maybe::Nothing)));
    /// ```
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::maybe::Maybe;
    /// use rustica::datatypes::wrapper::last::Last;
    /// use rustica::traits::functor::Functor;
    ///
    /// let a = Last(Maybe::Just(5));
    /// let b = a.fmap(|x| x * 2);  // Maps Maybe::Just(5) to Maybe::Just(10)
    /// assert_eq!(b, Last(Maybe::Just(10)));
    ///
    /// let c = Last::<i32>(Maybe::Nothing);
    /// let d = c.fmap(|x| x * 2);  // Maybe::Nothing remains Maybe::Nothing
    /// assert_eq!(d, Last(Maybe::Nothing));
    /// ```
    #[inline]
    fn fmap<U, F>(&self, f: F) -> Self::Output<U>
    where
        F: FnOnce(&Self::Source) -> U,
    {
        match &self.0 {
            Maybe::Just(value) => Last(Maybe::Just(f(value))),
            Maybe::Nothing => Last(Maybe::Nothing),
        }
    }

    /// Maps a function over the inner value of this `Last` container, consuming it.
    ///
    /// This method is similar to `fmap` but takes ownership of `self` and passes ownership
    /// of the inner value to the function `f`. This is more efficient when you don't need
    /// to preserve the original container.
    ///
    /// # Performance
    ///
    /// - **Time Complexity**: O(1) plus the complexity of function `f`
    /// - **Memory Usage**: Creates a new `Last` wrapper with the transformed value
    /// - **Ownership**: Consumes `self` and avoids unnecessary cloning of the inner value
    ///
    /// # Type Class Laws
    ///
    /// The same functor laws apply as for `fmap`, but with ownership semantics.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::maybe::Maybe;
    /// use rustica::datatypes::wrapper::last::Last;
    /// use rustica::traits::functor::Functor;
    ///
    /// let a = Last(Maybe::Just(String::from("hello")));
    /// let b = a.fmap_owned(|s| s.len());  // Consumes the string efficiently
    /// assert_eq!(b, Last(Maybe::Just(5)));
    ///
    /// // a is consumed and can't be used anymore
    /// ```
    #[inline]
    fn fmap_owned<U, F>(self, f: F) -> Self::Output<U>
    where
        F: FnOnce(Self::Source) -> U,
    {
        match self.0 {
            Maybe::Just(value) => Last(Maybe::Just(f(value))),
            Maybe::Nothing => Last(Maybe::Nothing),
        }
    }
}

impl<T> From<T> for Last<T> {
    fn from(value: T) -> Self {
        Last(Maybe::Just(value))
    }
}
