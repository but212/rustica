//! This module provides the `First` wrapper type which forms a semigroup by taking the first non-None value.
//!
//! ## Functional Programming Context
//!
//! The `First` type is a wrapper around `Option<T>` that implements various type classes with specific semantics:
//!
//! - As a `Semigroup`, it combines values by keeping the first non-None value
//! - As a `Monoid`, it uses `None` as its identity element
//! - As a `Functor`, it maps functions over the inner value if present
//! - As a `Foldable`, it allows extraction and reduction of the inner value
//!
//! ## Basic Usage
//!
//! ```rust
//! use rustica::datatypes::wrapper::first::First;
//! use rustica::traits::semigroup::Semigroup;
//! use rustica::traits::monoid::Monoid;
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
//!
//! // Use the identity element from Monoid
//! let empty = First::<i32>::empty();  // First(None)
//! assert_eq!(empty.combine(&a), a);
//! ```
//!
//! ## Type Class Laws
//!
//! `First<T>` satisfies the semigroup associativity law:
//!
//! ```rust
//! use rustica::datatypes::wrapper::first::First;
//! use rustica::traits::semigroup::Semigroup;
//!
//! // Verify associativity: (a combine b) combine c = a combine (b combine c)
//! let a = First(Some(1));
//! let b = First(Some(2));
//! let c = First(Some(3));
//! assert_eq!(a.clone().combine(&b).combine(&c),
//!            a.combine(&b.combine(&c)));
//! ```
//!
//! `First<T>` also satisfies the monoid identity laws:
//!
//! ```rust
//! use rustica::datatypes::wrapper::first::First;
//! use rustica::traits::semigroup::Semigroup;
//! use rustica::traits::monoid::Monoid;
//!
//! let a = First(Some(42));
//! let id = First::empty();  // First(None)
//!
//! // Identity laws: id combine x = x combine id = x
//! assert_eq!(id.combine(&a), a);
//! assert_eq!(a.combine(&id), a);
//! ```
//!
//! ## Performance Characteristics
//!
//! - Time Complexity: All operations (`combine`, `empty`, `fmap`, etc.) are O(1)
//! - Memory Usage: Stores exactly one `Option<T>` value with no additional overhead
//! - Clone Cost: Depends on the cost of cloning the inner type `T`
//!
//! ## Type Class Implementations
//!
//! `First<T>` implements the following type classes:
//!
//! - `Semigroup`: For any `T` that implements `Clone`
//! - `Monoid`: For any `T` that implements `Clone`
//! - `Functor`: For mapping operations over the inner value
//! - `Foldable`: For extracting and processing the inner value

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
    /// Combines two `First` values by taking the first non-None value, consuming both values.
    ///
    /// This is the owned version of the semigroup operation that takes ownership of both `self` and `other`.
    /// It returns the first value if it contains `Some`, otherwise it returns the second value.
    ///
    /// # Performance
    ///
    /// - **Time Complexity**: O(1) - Simply checks if the first value is Some
    /// - **Memory Usage**: No additional allocations, just pattern matching
    /// - **Ownership**: Consumes both values, avoiding unnecessary clones
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::wrapper::first::First;
    /// use rustica::traits::semigroup::Semigroup;
    ///
    /// // When first value is Some
    /// let a = First(Some(5));
    /// let b = First(Some(10));
    /// let c = a.combine_owned(b);
    /// assert_eq!(c, First(Some(5)));
    ///
    /// // When first value is None
    /// let x = First(None);
    /// let y = First(Some(7));
    /// let z = x.combine_owned(y);
    /// assert_eq!(z, First(Some(7)));
    ///
    /// // When both values are None
    /// let p = First::<i32>(None);
    /// let q = First::<i32>(None);
    /// let r = p.combine_owned(q);
    /// assert_eq!(r, First(None));
    /// ```
    #[inline]
    fn combine_owned(self, other: Self) -> Self {
        match self.0 {
            Some(_) => self,
            None => other,
        }
    }

    /// Combines two `First` values by taking the first non-None value, preserving the originals.
    ///
    /// This method implements the semigroup operation for `First` by returning a new `First`
    /// containing the first non-None value from either `self` or `other`. If both contain `None`,
    /// the result will be `First(None)`.
    ///
    /// # Performance
    ///
    /// - **Time Complexity**: O(1) - Simply checks if the first value is Some
    /// - **Memory Usage**: Requires cloning the inner value when returning a result
    /// - **Borrowing**: Takes references to both values, requiring `T: Clone`
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::wrapper::first::First;
    /// use rustica::traits::semigroup::Semigroup;
    ///
    /// // When first value is Some
    /// let a = First(Some(5));
    /// let b = First(Some(10));
    /// let c = a.combine(&b);
    /// assert_eq!(c, First(Some(5)));
    /// // Original values are preserved
    /// assert_eq!(a, First(Some(5)));
    /// assert_eq!(b, First(Some(10)));
    ///
    /// // When first value is None
    /// let x = First(None);
    /// let y = First(Some(7));
    /// let z = x.combine(&y);
    /// assert_eq!(z, First(Some(7)));
    ///
    /// // Demonstrating associativity
    /// let v1 = First(None);
    /// let v2 = First(Some(10));
    /// let v3 = First(Some(20));
    ///
    /// // (v1 ⊕ v2) ⊕ v3 = v1 ⊕ (v2 ⊕ v3)
    /// let left = v1.combine(&v2).combine(&v3);
    /// let right = v1.combine(&v2.combine(&v3));
    /// assert_eq!(left, right);
    /// ```
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
    /// Returns the identity element for the `First` monoid, which is `First(None)`.
    ///
    /// This method provides the identity element required by the `Monoid` type class.
    /// For `First`, this is represented as `None`, such that combining any value with
    /// `First(None)` returns the original value.
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
    /// use rustica::datatypes::wrapper::first::First;
    /// use rustica::traits::monoid::Monoid;
    /// use rustica::traits::semigroup::Semigroup;
    ///
    /// // For any First(x), empty() ⊕ First(x) = First(x)
    /// let empty = First::<i32>::empty();
    /// let value = First(Some(42));
    ///
    /// assert_eq!(empty.combine(&value), value);
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
    /// assert_eq!(value.combine(&empty), value);
    /// ```
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```rust
    /// use rustica::datatypes::wrapper::first::First;
    /// use rustica::traits::monoid::Monoid;
    ///
    /// // Create an identity element
    /// let empty = First::<String>::empty();
    /// assert_eq!(empty, First(None));
    /// ```
    ///
    /// Combining with identity element:
    ///
    /// ```rust
    /// use rustica::datatypes::wrapper::first::First;
    /// use rustica::traits::monoid::Monoid;
    /// use rustica::traits::semigroup::Semigroup;
    ///
    /// // With Some value
    /// let value = First(Some("hello"));
    /// let empty = First::<&str>::empty();
    ///
    /// // Identity on right
    /// assert_eq!(value.clone().combine(&empty), value.clone());
    ///
    /// // Identity on left
    /// assert_eq!(empty.combine(&value), value);
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
    /// Maps a function over the inner value of this `First` container, if it exists.
    ///
    /// This method applies the function `f` to the inner value if it's `Some`,
    /// otherwise it returns `First(None)`. This borrows the inner value during the mapping.
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
    /// // Test with Some value
    /// assert!(verify_identity_law(First(Some(42))));
    ///
    /// // Test with None value
    /// assert!(verify_identity_law(First::<i32>(None)));
    /// ```
    ///
    /// ## Composition Law
    ///
    /// ```rust
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
    /// // Test with Some value (using i32 which implements From<i32>)
    /// assert!(verify_composition_law(First(Some(5))));
    ///
    /// // Test with None value
    /// assert!(verify_composition_law(First::<i32>(None)));
    /// ```
    ///
    /// # Examples
    ///
    /// Basic transformation:
    ///
    /// ```rust
    /// use rustica::datatypes::wrapper::first::First;
    /// use rustica::traits::functor::Functor;
    ///
    /// let a = First(Some(5));
    /// let b = a.fmap(|x| x * 2);  // Maps Some(5) to Some(10)
    /// assert_eq!(b, First(Some(10)));
    ///
    /// let c = First::<i32>(None);
    /// let d = c.fmap(|x| x * 2);  // None remains None
    /// assert_eq!(d, First(None));
    /// ```
    ///
    /// Chaining multiple transformations:
    ///
    /// ```rust
    /// use rustica::datatypes::wrapper::first::First;
    /// use rustica::traits::functor::Functor;
    ///
    /// let a = First(Some(5));
    /// let result = a
    ///     .fmap(|x| x * 2)     // Some(10)
    ///     .fmap(|x| x + 3)     // Some(13)
    ///     .fmap(|x| x.to_string()); // Some("13")
    ///
    /// assert_eq!(result, First(Some("13".to_string())));
    /// ```
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
    /// Basic transformation with ownership:
    ///
    /// ```rust
    /// use rustica::datatypes::wrapper::first::First;
    /// use rustica::traits::functor::Functor;
    ///
    /// let a = First(Some(String::from("hello")));
    /// let b = a.fmap_owned(|s| s.len());  // Consumes the string efficiently
    /// assert_eq!(b, First(Some(5)));
    ///
    /// // a is consumed and can't be used anymore
    /// ```
    ///
    /// With None value:
    ///
    /// ```rust
    /// use rustica::datatypes::wrapper::first::First;
    /// use rustica::traits::functor::Functor;
    ///
    /// let c = First::<String>(None);
    /// let d = c.fmap_owned(|s| s.len());  // None remains None
    /// assert_eq!(d, First(None));
    /// ```
    ///
    /// Transforming heap-allocated data efficiently:
    ///
    /// ```rust
    /// use rustica::datatypes::wrapper::first::First;
    /// use rustica::traits::functor::Functor;
    /// use std::collections::HashMap;
    ///
    /// // Create a First containing a heap-allocated HashMap
    /// let mut map = HashMap::new();
    /// map.insert("a", 1);
    /// map.insert("b", 2);
    ///
    /// let container = First(Some(map));
    ///
    /// // Transform it efficiently without cloning the HashMap
    /// let result = container.fmap_owned(|m| m.len());
    ///
    /// assert_eq!(result, First(Some(2)));
    /// ```
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
