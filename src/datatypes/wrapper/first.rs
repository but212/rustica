//! This module provides the `First` wrapper type which forms a semigroup by taking the first non-Maybe::Nothing value.
//!
//! ## Functional Programming Context
//!
//! The `First` type is a wrapper around `Maybe<T>` that implements various type classes with specific semantics:
//!
//! - As a `Semigroup`, it combines values by keeping the first non-Maybe::Nothing value
//! - As a `Monoid`, it uses `Maybe::Nothing` as its identity element
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
//!   - Combining the identity element (`First(Maybe::Nothing)`) with any value gives the original value.
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
//! ## Performance Characteristics
//!
//! - Time Complexity: All operations (`combine`, `empty`, `fmap`, etc.) are O(1)
//! - Memory Usage: Stores exactly one `Maybe<T>` value with no additional overhead
//! - Clone Cost: Depends on the cost of cloning the inner type `T`
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
//! use rustica::datatypes::maybe::Maybe;
//!
//! // Create First wrappers
//! let a = First(Maybe::Just(42));
//! let b = First(Maybe::Just(10));
//! let nothing = First(Maybe::Nothing);
//!
//! // First non-Maybe::Nothing value wins
//! assert_eq!(a.combine(&b), First(Maybe::Just(42))); // First value wins
//! assert_eq!(nothing.combine(&b), First(Maybe::Just(10))); // Second value when first is Maybe::Nothing
//! assert_eq!(a.combine(&nothing), First(Maybe::Just(42))); // First value when second is Maybe::Nothing
//!
//! // Identity element
//! let empty = First::empty();
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

/// A wrapper type that forms a semigroup by taking the first non-Maybe::Nothing value.
///
/// The monoid instance uses `Maybe::Nothing` as the identity element.
///
/// # Examples
///
/// Basic usage with the `Semigroup` trait:
///
/// ```rust
/// use rustica::datatypes::maybe::Maybe;
/// use rustica::datatypes::wrapper::first::First;
/// use rustica::traits::semigroup::Semigroup;
/// use rustica::traits::monoid::Monoid;
///
/// let a = First(Maybe::Just(5));
/// let b = First(Maybe::Just(7));
/// let c = a.combine(&b);
/// assert_eq!(c, First(Maybe::Just(5)));
///
/// // First is associative
/// let x = First(Maybe::Just(1));
/// let y = First(Maybe::Nothing);
/// let z = First(Maybe::Just(3));
/// assert_eq!(x.clone().combine(&y.clone()).combine(&z.clone()),
///            x.clone().combine(&y.clone().combine(&z.clone())));
///
/// // Identity element
/// let id = First::empty();  // First(Maybe::Nothing)
/// assert_eq!(id, First(Maybe::Nothing));
/// assert_eq!(First(Maybe::Just(42)).combine(&id.clone()), First(Maybe::Just(42)));
/// assert_eq!(id.combine(&First(Maybe::Just(42))), First(Maybe::Just(42)));
/// ```
///
/// Using with `Functor` to transform the inner value:
///
/// ```rust
/// use rustica::datatypes::maybe::Maybe;
/// use rustica::datatypes::wrapper::first::First;
/// use rustica::traits::functor::Functor;
///
/// let a = First(Maybe::Just(5));
/// let b = a.fmap(|x| x * 2);
/// assert_eq!(b, First(Maybe::Just(10)));
///
/// let c = First(Maybe::Nothing);
/// let d = c.fmap(|x: &i32| x * 2);
/// assert_eq!(d, First(Maybe::Nothing));
/// ```
///
/// # Semigroup Laws
///
/// First satisfies the semigroup associativity law:
///
/// ```rust
/// use rustica::datatypes::maybe::Maybe;
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
/// assert!(verify_associativity(First(Maybe::Just(1)), First(Maybe::Just(2)), First(Maybe::Just(3))));
/// assert!(verify_associativity(First(Maybe::Nothing), First(Maybe::Just(2)), First(Maybe::Just(3))));
/// assert!(verify_associativity(First(Maybe::Just(1)), First(Maybe::Nothing), First(Maybe::Just(3))));
/// assert!(verify_associativity(First(Maybe::Just(1)), First(Maybe::Just(2)), First(Maybe::Nothing)));
/// ```
///
/// # Monoid Laws
///
/// First satisfies the monoid identity laws:
///
/// ```rust
/// use rustica::datatypes::maybe::Maybe;
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
/// // Test with Maybe::Just and Maybe::Nothing values
/// assert!(verify_left_identity(First(Maybe::Just(42))));
/// assert!(verify_left_identity::<i32>(First::empty()));
/// assert!(verify_right_identity(First(Maybe::Just(42))));
/// assert!(verify_right_identity::<i32>(First::empty()));
/// ```
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[repr(transparent)]
pub struct First<T>(pub Maybe<T>);

impl<T: Clone> First<T> {
    /// Unwraps the first value, panicking if Maybe::Nothing.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::maybe::Maybe;
    /// # use rustica::datatypes::wrapper::first::First;
    /// let first = First(Maybe::Just(42));
    /// assert_eq!(first.unwrap(), 42);
    ///
    /// let empty: First<i32> = First(Maybe::Nothing);
    /// // empty.unwrap() would panic
    /// ```
    ///
    /// # Panics
    ///
    /// Panics if the inner value is Maybe::Nothing.
    pub fn unwrap(&self) -> T {
        self.0.clone().unwrap()
    }

    /// Unwraps the first value or returns a default.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::maybe::Maybe;
    /// # use rustica::datatypes::wrapper::first::First;
    /// let first = First(Maybe::Just(42));
    /// let empty = First(Maybe::Nothing);
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

impl<T: Clone> Semigroup for First<T> {
    /// Combines two `First` values by taking the first non-Maybe::Nothing value, consuming both values.
    ///
    /// This is the owned version of the semigroup operation that takes ownership of both `self` and `other`.
    /// It returns the first value if it contains `Maybe::Just`, otherwise it returns the second value.
    ///
    /// # Performance
    ///
    /// - **Time Complexity**: O(1) - Simply checks if the first value is Maybe::Just
    /// - **Memory Usage**: No additional allocations, just pattern matching
    /// - **Ownership**: Consumes both values, avoiding unnecessary clones
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::maybe::Maybe;
    /// use rustica::datatypes::wrapper::first::First;
    /// use rustica::traits::semigroup::Semigroup;
    ///
    /// // When first value is Maybe::Just
    /// let a = First(Maybe::Just(5));
    /// let b = First(Maybe::Just(10));
    /// let c = a.combine_owned(b);
    /// assert_eq!(c, First(Maybe::Just(5)));
    ///
    /// // When first value is Maybe::Nothing
    /// let x = First(Maybe::Nothing);
    /// let y = First(Maybe::Just(7));
    /// let z = x.combine_owned(y);
    /// assert_eq!(z, First(Maybe::Just(7)));
    ///
    /// // When both values are Maybe::Nothing
    /// let p = First::<i32>(Maybe::Nothing);
    /// let q = First::<i32>(Maybe::Nothing);
    /// let r = p.combine_owned(q);
    /// assert_eq!(r, First(Maybe::Nothing));
    /// ```
    #[inline]
    fn combine_owned(self, other: Self) -> Self {
        match self.0 {
            Maybe::Just(_) => self,
            Maybe::Nothing => other,
        }
    }

    /// Combines two `First` values by taking the first non-Maybe::Nothing value, preserving the originals.
    ///
    /// This method implements the semigroup operation for `First` by returning a new `First`
    /// containing the first non-Maybe::Nothing value from either `self` or `other`. If both contain `Maybe::Nothing`,
    /// the result will be `First(Maybe::Nothing)`.
    ///
    /// # Performance
    ///
    /// - **Time Complexity**: O(1) - Simply checks if the first value is Maybe::Just
    /// - **Memory Usage**: Requires cloning the inner value when returning a result
    /// - **Borrowing**: Takes references to both values, requiring `T: Clone`
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::maybe::Maybe;
    /// use rustica::datatypes::wrapper::first::First;
    /// use rustica::traits::semigroup::Semigroup;
    ///
    /// // When first value is Maybe::Just
    /// let a = First(Maybe::Just(5));
    /// let b = First(Maybe::Just(10));
    /// let c = a.combine(&b);
    /// assert_eq!(c, First(Maybe::Just(5)));
    /// // Original values are preserved
    /// assert_eq!(a, First(Maybe::Just(5)));
    /// assert_eq!(b, First(Maybe::Just(10)));
    ///
    /// // When first value is Maybe::Nothing
    /// let x = First(Maybe::Nothing);
    /// let y = First(Maybe::Just(7));
    /// let z = x.combine(&y);
    /// assert_eq!(z, First(Maybe::Just(7)));
    ///
    /// // Demonstrating associativity
    /// let v1 = First(Maybe::Nothing);
    /// let v2 = First(Maybe::Just(10));
    /// let v3 = First(Maybe::Just(20));
    ///
    /// // (v1 ⊕ v2) ⊕ v3 = v1 ⊕ (v2 ⊕ v3)
    /// let left = v1.combine(&v2).combine(&v3);
    /// let right = v1.combine(&v2.combine(&v3));
    /// assert_eq!(left, right);
    /// ```
    #[inline]
    fn combine(&self, other: &Self) -> Self {
        match &self.0 {
            Maybe::Just(_) => First(self.0.clone()),
            Maybe::Nothing => First(other.0.clone()),
        }
    }
}

impl<T: fmt::Display> fmt::Display for First<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match &self.0 {
            Maybe::Just(value) => write!(f, "First(Maybe::Just({value}))"),
            Maybe::Nothing => write!(f, "First(Maybe::Nothing)"),
        }
    }
}

impl<T: Clone> Monoid for First<T> {
    /// Returns the identity element for the `First` monoid, which is `First(Maybe::Nothing)`.
    ///
    /// This method provides the identity element required by the `Monoid` type class.
    /// For `First`, this is represented as `Maybe::Nothing`, such that combining any value with
    /// `First(Maybe::Nothing)` returns the original value.
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
    /// use rustica::datatypes::wrapper::first::First;
    /// use rustica::traits::monoid::Monoid;
    /// use rustica::traits::semigroup::Semigroup;
    ///
    /// // For any First(x), empty() ⊕ First(x) = First(x)
    /// let empty = First::<i32>::empty();
    /// let value = First(Maybe::Just(42));
    ///
    /// assert_eq!(empty.combine(&value), value);
    /// ```
    ///
    /// ## Right Identity
    ///
    /// ```rust
    /// use rustica::datatypes::maybe::Maybe;
    /// use rustica::datatypes::wrapper::first::First;
    /// use rustica::traits::monoid::Monoid;
    /// use rustica::traits::semigroup::Semigroup;
    ///
    /// // For any First(x), First(x) ⊕ empty() = First(x)
    /// let value = First(Maybe::Just(42));
    /// let empty = First::<i32>::empty();
    ///
    /// assert_eq!(value.combine(&empty), value);
    /// ```
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::maybe::Maybe;
    /// use rustica::datatypes::wrapper::first::First;
    /// use rustica::traits::monoid::Monoid;
    ///
    /// // Create an identity element
    /// let empty = First::<String>::empty();
    /// assert_eq!(empty, First(Maybe::Nothing));
    /// ```
    #[inline]
    fn empty() -> Self {
        First(Maybe::Nothing)
    }
}

impl<T> HKT for First<T> {
    type Source = T;
    type Output<U> = First<U>;
}

impl<T: Clone> Identity for First<T> {
    fn value(&self) -> &Self::Source {
        self.0.as_ref().unwrap()
    }

    fn into_value(self) -> Self::Source {
        self.0.unwrap()
    }
}

impl<T: Clone> Functor for First<T> {
    /// Maps a function over the inner value of this `First` container, if it exists.
    ///
    /// This method applies the function `f` to the inner value if it's `Maybe::Just`,
    /// otherwise it returns `First(Maybe::Nothing)`. This borrows the inner value during the mapping.
    ///
    /// # Performance
    ///
    /// - **Time Complexity**: O(1) plus the complexity of function `f`
    /// - **Memory Usage**: Creates a new `First` wrapper with the transformed value
    /// - **Borrowing**: Takes a reference to the inner value, avoiding unnecessary clones
    ///
    /// # Type Class Laws
    ///
    /// ## Identity Law
    ///
    /// ```rust
    /// use rustica::datatypes::maybe::Maybe;
    /// use rustica::datatypes::wrapper::first::First;
    /// use rustica::traits::functor::Functor;
    ///
    /// // For any First(x), fmap(id) = id
    /// // where id is the identity function
    /// fn verify_identity_law<T: Clone + PartialEq>(x: First<T>) -> bool {
    ///     let mapped = x.clone().fmap(|a| a.clone());
    ///     mapped == x
    /// }
    ///
    /// // Test with Maybe::Just value
    /// assert!(verify_identity_law(First(Maybe::Just(42))));
    ///
    /// // Test with Maybe::Nothing value
    /// assert!(verify_identity_law(First::<i32>(Maybe::Nothing)));
    /// ```
    ///
    /// ## Composition Law
    ///
    /// ```rust
    /// use rustica::datatypes::maybe::Maybe;
    /// use rustica::datatypes::wrapper::first::First;
    /// use rustica::traits::functor::Functor;
    ///
    /// // For any First(x) and functions f and g:
    /// // fmap(f . g) = fmap(f) . fmap(g)
    /// fn verify_composition_law<T>(x: First<T>) -> bool
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
    /// assert!(verify_composition_law(First(Maybe::Just(5))));
    ///
    /// // Test with Maybe::Nothing value
    /// assert!(verify_composition_law(First::<i32>(Maybe::Nothing)));
    /// ```
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::maybe::Maybe;
    /// use rustica::datatypes::wrapper::first::First;
    /// use rustica::traits::functor::Functor;
    ///
    /// let a = First(Maybe::Just(5));
    /// let b = a.fmap(|x| x * 2);
    /// assert_eq!(b, First(Maybe::Just(10)));
    ///
    /// let c = First::<i32>(Maybe::Nothing);
    /// let d = c.fmap(|x| x * 2);
    /// assert_eq!(d, First(Maybe::Nothing));
    /// ```
    #[inline]
    fn fmap<U, F>(&self, f: F) -> Self::Output<U>
    where
        F: FnOnce(&Self::Source) -> U,
    {
        match &self.0 {
            Maybe::Just(value) => First(Maybe::Just(f(value))),
            Maybe::Nothing => First(Maybe::Nothing),
        }
    }

    /// Maps a function over the inner value of this `First` container, consuming it.
    ///
    /// This method is similar to `fmap` but takes ownership of `self` and passes ownership
    /// of the inner value to the function `f`. This is more efficient when you don't need
    /// to preserve the original container.
    ///
    /// # Performance
    ///
    /// - **Time Complexity**: O(1) plus the complexity of function `f`
    /// - **Memory Usage**: Creates a new `First` wrapper with the transformed value
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
    /// use rustica::datatypes::wrapper::first::First;
    /// use rustica::traits::functor::Functor;
    ///
    /// let a = First(Maybe::Just(String::from("hello")));
    /// let b = a.fmap_owned(|s| s.len());  // Consumes the string efficiently
    /// assert_eq!(b, First(Maybe::Just(5)));
    ///
    /// // a is consumed and can't be used anymore
    /// ```
    #[inline]
    fn fmap_owned<U, F>(self, f: F) -> Self::Output<U>
    where
        F: FnOnce(Self::Source) -> U,
    {
        match self.0 {
            Maybe::Just(value) => First(Maybe::Just(f(value))),
            Maybe::Nothing => First(Maybe::Nothing),
        }
    }
}

impl<T> From<T> for First<T> {
    fn from(value: T) -> Self {
        First(Maybe::Just(value))
    }
}
