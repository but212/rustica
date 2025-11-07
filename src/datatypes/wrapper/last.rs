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
//! ## Performance Characteristics
//!
//! - Time Complexity: All operations (`combine`, `empty`, `fmap`, etc.) are O(1)
//! - Memory Usage: Stores exactly one `Option<T>` value with no additional overhead
//! - Clone Cost: Depends on the cost of cloning the inner type `T`
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
//! assert_eq!(a.combine(&b), Last(Some(10))); // Second value wins
//! assert_eq!(none.combine(&b), Last(Some(10))); // Second value when first is None
//! assert_eq!(a.combine(&none), Last(Some(42))); // First value when second is None
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
/// // To create a Last value, use the constructor or Pure trait
/// let b = Last(Some(100));
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
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Last<T>(pub Option<T>);

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
    /// Combines two `Last` values by taking the last non-None value, consuming both values.
    ///
    /// This is the owned version of the semigroup operation that takes ownership of both `self` and `other`.
    /// It returns the second value if it contains `Some`, otherwise it returns the first value.
    ///
    /// # Performance
    ///
    /// - **Time Complexity**: O(1) - Simply checks if the second value is Some
    /// - **Memory Usage**: No additional allocations, just pattern matching
    /// - **Ownership**: Consumes both values, avoiding unnecessary clones
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::wrapper::last::Last;
    /// use rustica::traits::semigroup::Semigroup;
    ///
    /// // When second value is Some
    /// let a = Last(Some(5));
    /// let b = Last(Some(10));
    /// let c = a.combine_owned(b);
    /// assert_eq!(c, Last(Some(10)));
    ///
    /// // When second value is None
    /// let x = Last(Some(7));
    /// let y = Last(None);
    /// let z = x.combine_owned(y);
    /// assert_eq!(z, Last(Some(7)));
    ///
    /// // When both values are None
    /// let p = Last::<i32>(None);
    /// let q = Last::<i32>(None);
    /// let r = p.combine_owned(q);
    /// assert_eq!(r, Last(None));
    /// ```
    #[inline]
    fn combine_owned(self, other: Self) -> Self {
        match other.0 {
            Some(_) => other,
            None => self,
        }
    }

    /// Combines two `Last` values by taking the last non-None value, preserving the originals.
    ///
    /// This method implements the semigroup operation for `Last` by returning a new `Last`
    /// containing the last non-None value from either `self` or `other`. If both contain `None`,
    /// the result will be `Last(None)`.
    ///
    /// # Performance
    ///
    /// - **Time Complexity**: O(1) - Simply checks if the second value is Some
    /// - **Memory Usage**: Requires cloning the inner value when returning a result
    /// - **Borrowing**: Takes references to both values, requiring `T: Clone`
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::wrapper::last::Last;
    /// use rustica::traits::semigroup::Semigroup;
    ///
    /// // When second value is Some
    /// let a = Last(Some(5));
    /// let b = Last(Some(10));
    /// let c = a.combine(&b);
    /// assert_eq!(c, Last(Some(10)));
    /// // Original values are preserved
    /// assert_eq!(a, Last(Some(5)));
    /// assert_eq!(b, Last(Some(10)));
    ///
    /// // When second value is None
    /// let x = Last(Some(7));
    /// let y = Last(None);
    /// let z = x.combine(&y);
    /// assert_eq!(z, Last(Some(7)));
    ///
    /// // Demonstrating associativity
    /// let v1 = Last(None);
    /// let v2 = Last(Some(10));
    /// let v3 = Last(Some(20));
    ///
    /// // (v1 ⊕ v2) ⊕ v3 = v1 ⊕ (v2 ⊕ v3)
    /// let left = v1.combine(&v2).combine(&v3);
    /// let right = v1.combine(&v2.combine(&v3));
    /// assert_eq!(left, right);
    /// ```
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
    /// assert_eq!(empty.combine(&value), value);
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
    /// assert_eq!(value.combine(&empty), value);
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
    /// This method applies the function `f` to the inner value if it's `Some`,
    /// otherwise it returns `Last(None)`. This borrows the inner value during the mapping.
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
    /// // Test with Some value
    /// assert!(verify_identity_law(Last(Some(42))));
    ///
    /// // Test with None value
    /// assert!(verify_identity_law(Last::<i32>(None)));
    /// ```
    ///
    /// ## Composition Law
    ///
    /// ```rust
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
    /// // Test with Some value (using i32 which implements From<i32>)
    /// assert!(verify_composition_law(Last(Some(5))));
    ///
    /// // Test with None value
    /// assert!(verify_composition_law(Last::<i32>(None)));
    /// ```
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::wrapper::last::Last;
    /// use rustica::traits::functor::Functor;
    ///
    /// let a = Last(Some(5));
    /// let b = a.fmap(|x| x * 2);  // Maps Some(5) to Some(10)
    /// assert_eq!(b, Last(Some(10)));
    ///
    /// let c = Last::<i32>(None);
    /// let d = c.fmap(|x| x * 2);  // None remains None
    /// assert_eq!(d, Last(None));
    /// ```
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
    /// use rustica::datatypes::wrapper::last::Last;
    /// use rustica::traits::functor::Functor;
    ///
    /// let a = Last(Some(String::from("hello")));
    /// let b = a.fmap_owned(|s| s.len());  // Consumes the string efficiently
    /// assert_eq!(b, Last(Some(5)));
    ///
    /// // a is consumed and can't be used anymore
    /// ```
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

impl<T> From<T> for Last<T> {
    #[inline]
    fn from(value: T) -> Self {
        Last(Some(value))
    }
}
