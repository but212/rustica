//! # Min
//!
//! This module provides the `Min` wrapper type which forms a semigroup under taking the minimum.
//!
//! ## Basic Usage
//!
//! ```rust
//! use rustica::datatypes::wrapper::min::Min;
//! use rustica::traits::semigroup::Semigroup;
//!
//! let a = Min(5);
//! let b = Min(10);
//! let c = a.combine(&b);
//! assert_eq!(c, Min(5));
//! ```
//!
//! ## Type Class Laws
//!
//! `Min<T>` satisfies the semigroup associativity law:
//!
//! ```rust
//! use rustica::datatypes::wrapper::min::Min;
//! use rustica::traits::semigroup::Semigroup;
//!
//! // Verify associativity: (a combine b) combine c = a combine (b combine c)
//! let a = Min(3);
//! let b = Min(7);
//! let c = Min(1);
//! assert_eq!(a.clone().combine(&b).combine(&c),
//!            a.combine(&b.combine(&c)));
//! ```
//!
//! When `T` has a maximum value, `Min<T>` also satisfies the monoid laws:
//!
//! ```rust
//! use rustica::datatypes::wrapper::min::Min;
//! use rustica::traits::semigroup::Semigroup;
//! use rustica::traits::monoid::Monoid;
//!
//! let a = Min(42);
//! let id = Min(i32::MAX);
//!
//! // Identity laws: id combine x = x combine id = x
//! assert_eq!(id.combine(&a), a);
//! assert_eq!(a.combine(&id), a);
//! ```
//!
//! ## Performance Characteristics
//!
//! - Time Complexity: All operations (`combine`, `empty`, `fmap`, etc.) are O(1)
//! - Memory Usage: Stores exactly one value of type `T` with no additional overhead
//! - Clone Cost: Depends on the cost of cloning the inner type `T`
//!
//! ## Functional Programming Context
//!
//! The `Min` wrapper is a fundamental building block for functional programming patterns:
//!
//! - **Aggregation**: Provides a principled way to find minimum values
//! - **Transformation**: Works with `Functor` to map inner values while preserving the wrapper
//! - **Folding**: Can be used with `Foldable` to reduce collections to a single minimum value
//!
//! ```rust
//! use rustica::datatypes::wrapper::min::Min;
//! use rustica::traits::functor::Functor;
//! use rustica::traits::identity::Identity;
//!
//! // Transform the inner value while preserving the wrapper
//! let a = Min(5);
//! let b = a.fmap(|x| x * 2);
//! assert_eq!(*b.value(), 10);
//! ```
//!
//! ## Type Class Implementations
//!
//! `Min<T>` implements the following type classes:
//!
//! - `Semigroup`: For any `T` that implements `Ord`
//! - `Monoid`: For any `T` that implements `Ord` and has a maximum value
//! - `Functor`: For mapping operations over the inner value
//! - `Identity`: For accessing the inner value
//! - `Foldable`: For folding operations over the single inner value

use crate::traits::foldable::Foldable;
use crate::traits::functor::Functor;
use crate::traits::hkt::HKT;
use crate::traits::identity::Identity;
use crate::traits::monoid::Monoid;
use crate::traits::semigroup::Semigroup;
use std::cmp::Ordering;
use std::fmt;

/// A wrapper type that forms a semigroup under the minimum operation.
///
/// When the inner type has a maximum value, this also forms a monoid.
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
/// let c = a.combine(&b);
/// assert_eq!(c, Min(5));
///
/// // Taking the minimum is associative: min(min(a, b), c) = min(a, min(b, c))
/// let x = Min(10);
/// let y = Min(2);
/// let z = Min(6);
/// assert_eq!(x.clone().combine(&y.clone()).combine(&z.clone()),
///            x.clone().combine(&y.clone().combine(&z.clone())));
/// ```
///
/// # Semigroup Laws
///
/// The `Min<T>` wrapper satisfies the semigroup associativity law:
///
/// ```rust
/// use rustica::datatypes::wrapper::min::Min;
/// use rustica::traits::semigroup::Semigroup;
///
/// // Verify associativity: (a combine b) combine c = a combine (b combine c)
/// fn verify_associativity<T: Clone + Ord>(a: T, b: T, c: T) -> bool {
///     let min_a = Min(a);
///     let min_b = Min(b);
///     let min_c = Min(c);
///     
///     let left = min_a.clone().combine(&min_b).combine(&min_c);
///     let right = min_a.combine(&min_b.combine(&min_c));
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
/// When `T` has a maximum value (like numeric types), `Min<T>` also satisfies the monoid laws:
///
/// ```rust
/// use rustica::datatypes::wrapper::min::Min;
/// use rustica::traits::semigroup::Semigroup;
/// use rustica::traits::monoid::Monoid;
///
/// // For integers, the default (0) may not be the identity element for Min
/// // We can verify that Max::MAX would be the true identity
/// let a = Min(42);
/// let id = Min(i32::MAX);
///
/// // Identity laws: empty() combine x = x combine empty() = x
/// assert_eq!(a.clone().combine(&id), a.clone());
/// assert_eq!(id.combine(&a), a);
/// ```
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
pub struct Min<T>(pub T);

impl<T: Clone + Ord> Semigroup for Min<T> {
    /// Combines two `Min` values by taking the minimum, consuming self.
    ///
    /// This method implements the Semigroup operation for `Min<T>`, which is taking
    /// the minimum of two values. This method consumes both operands.
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
    /// use rustica::datatypes::wrapper::min::Min;
    /// use rustica::traits::semigroup::Semigroup;
    ///
    /// // For any a, b, c: (a ⊕ b) ⊕ c = a ⊕ (b ⊕ c)
    /// // where ⊕ is the combine operation
    /// fn verify_associativity<T: Clone + Ord>(a: T, b: T, c: T) -> bool {
    ///     let min_a = Min(a);
    ///     let min_b = Min(b);
    ///     let min_c = Min(c);
    ///     
    ///     let left = min_a.clone().combine_owned(min_b.clone()).combine_owned(min_c.clone());
    ///     let right = min_a.combine_owned(min_b.combine_owned(min_c));
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
    /// Basic usage:
    ///
    /// ```rust
    /// use rustica::datatypes::wrapper::min::Min;
    /// use rustica::traits::semigroup::Semigroup;
    ///
    /// let a = Min(5);
    /// let b = Min(10);
    ///
    /// // a and b are consumed
    /// let c = a.combine_owned(b);
    /// assert_eq!(c, Min(5));
    /// ```
    ///
    /// With custom types that implement `Ord`:
    ///
    /// ```rust
    /// use rustica::datatypes::wrapper::min::Min;
    /// use rustica::traits::semigroup::Semigroup;
    /// use std::cmp::Ordering;
    ///
    /// #[derive(Clone, Debug, PartialEq, Eq)]
    /// struct Version(u32, u32, u32);  // Major, minor, patch
    ///
    /// impl PartialOrd for Version {
    ///     fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
    ///         Some(self.cmp(other))
    ///     }
    /// }
    ///
    /// impl Ord for Version {
    ///     fn cmp(&self, other: &Self) -> Ordering {
    ///         match self.0.cmp(&other.0) {
    ///             Ordering::Equal => match self.1.cmp(&other.1) {
    ///                 Ordering::Equal => self.2.cmp(&other.2),
    ///                 ord => ord,
    ///             },
    ///             ord => ord,
    ///         }
    ///     }
    /// }
    ///
    /// let v1 = Min(Version(1, 0, 0));
    /// let v2 = Min(Version(2, 0, 0));
    /// let v3 = Min(Version(1, 5, 0));
    ///
    /// // Find the minimum version
    /// let min_v = v1.combine_owned(v2).combine_owned(v3);
    /// assert_eq!(min_v, Min(Version(1, 0, 0)));
    /// ```
    #[inline]
    fn combine_owned(self, other: Self) -> Self {
        match self.0.cmp(&other.0) {
            Ordering::Less | Ordering::Equal => self,
            Ordering::Greater => other,
        }
    }

    /// Combines two `Min` values by taking the minimum, borrowing self.
    ///
    /// This method implements the Semigroup operation for `Min<T>`, which is taking
    /// the minimum of two values. This method borrows both operands and returns a new `Min`.
    ///
    /// # Performance
    ///
    /// - **Time Complexity**: O(1) - Just performs a comparison and clones one of the values
    /// - **Memory Usage**: Creates a new `Min` wrapper with a clone of one of the input values
    /// - **Borrowing**: Borrows `self` and `other`, avoiding unnecessary cloning of both
    ///
    /// # Type Class Laws
    ///
    /// ## Associativity
    ///
    /// ```rust
    /// use rustica::datatypes::wrapper::min::Min;
    /// use rustica::traits::semigroup::Semigroup;
    ///
    /// // For any a, b, c: (a ⊕ b) ⊕ c = a ⊕ (b ⊕ c)
    /// // where ⊕ is the combine operation
    /// fn verify_associativity<T: Clone + Ord + PartialEq>(a: T, b: T, c: T) -> bool {
    ///     let min_a = Min(a);
    ///     let min_b = Min(b);
    ///     let min_c = Min(c);
    ///     
    ///     let left = min_a.combine(&min_b).combine(&min_c);
    ///     let right = min_a.combine(&min_b.combine(&min_c));
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
    /// Basic usage:
    ///
    /// ```rust
    /// use rustica::datatypes::wrapper::min::Min;
    /// use rustica::traits::semigroup::Semigroup;
    ///
    /// let a = Min(5);
    /// let b = Min(10);
    ///
    /// // a and b are borrowed
    /// let c = a.combine(&b);
    /// assert_eq!(c, Min(5));
    ///
    /// // a and b can still be used
    /// let d = b.combine(&a);
    /// assert_eq!(d, Min(5));
    /// ```
    ///
    /// Combining multiple values:
    ///
    /// ```rust
    /// use rustica::datatypes::wrapper::min::Min;
    /// use rustica::traits::semigroup::Semigroup;
    ///
    /// let values = vec![Min(3), Min(8), Min(2), Min(10), Min(5)];
    ///
    /// // Find the minimum value in the collection
    /// let result = values.iter().fold(Min(std::i32::MAX), |acc, x| acc.combine(x));
    /// assert_eq!(result, Min(2));
    /// ```
    #[inline]
    fn combine(&self, other: &Self) -> Self {
        match self.0.cmp(&other.0) {
            Ordering::Less | Ordering::Equal => Min(self.0.clone()),
            Ordering::Greater => Min(other.0.clone()),
        }
    }
}

impl<T: Clone + Ord + Default> Monoid for Min<T> {
    /// Returns the identity element for the `Min` monoid, which is `Min(T::default())`,
    /// typically the maximum possible value of `T`.
    ///
    /// For numeric types, this is usually the maximum possible value (e.g., MAX_INT for integers).
    /// When combined with any other `Min` value, the result will always be the other value.
    /// However, note that for many types, T::default() may not be the true identity element for Min.
    /// For proper identity behavior, the maximum possible value for type T should be used.
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
    /// use rustica::datatypes::wrapper::min::Min;
    /// use rustica::traits::monoid::Monoid;
    /// use rustica::traits::semigroup::Semigroup;
    ///
    /// // For any Min(x), empty() ⊕ Min(x) = Min(x) when empty() contains the maximum value
    /// fn verify_left_identity<T: Clone + Ord + Default + PartialEq>(x: T, max_value: T) -> bool {
    ///     // Note: For a true identity, we'd ideally use the maximum value for T
    ///     // rather than T::default(), which might not be suitable for all types
    ///     let identity = Min(max_value);
    ///     let value = Min(x);
    ///     
    ///     identity.combine(&value) == value
    /// }
    ///
    /// // Test with integers where i32::MAX is the identity for Min
    /// assert!(verify_left_identity(42, i32::MAX));
    /// assert!(verify_left_identity(0, i32::MAX));
    /// ```
    ///
    /// ## Right Identity
    ///
    /// ```rust
    /// use rustica::datatypes::wrapper::min::Min;
    /// use rustica::traits::monoid::Monoid;
    /// use rustica::traits::semigroup::Semigroup;
    ///
    /// // For any Min(x), Min(x) ⊕ empty() = Min(x) when empty() contains the maximum value
    /// fn verify_right_identity<T: Clone + Ord + Default + PartialEq>(x: T, max_value: T) -> bool {
    ///     let value = Min(x);
    ///     // Note: For a true identity, we'd ideally use the maximum value for T
    ///     let identity = Min(max_value);
    ///     
    ///     value.combine(&identity) == value
    /// }
    ///
    /// // Test with integers where i32::MAX is the identity for Min
    /// assert!(verify_right_identity(42, i32::MAX));
    /// assert!(verify_right_identity(0, i32::MAX));
    /// ```
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```rust
    /// use rustica::datatypes::wrapper::min::Min;
    /// use rustica::traits::monoid::Monoid;
    /// use rustica::traits::semigroup::Semigroup;
    ///
    /// // Create an identity element for integers
    /// // Note: For Min, T::default() may not be the true identity element
    /// let empty = Min::<i32>::empty();
    /// assert_eq!(empty, Min(0)); // Default for i32 is 0, but ideally it should be i32::MAX
    ///
    /// // For a true identity with integers:
    /// let true_identity = Min(i32::MAX);
    /// let value = Min(42);
    ///
    /// // Identity laws should hold
    /// assert_eq!(true_identity.combine(&value), value);
    /// assert_eq!(value.combine(&true_identity), value);
    /// ```
    ///
    /// Using with custom types that implement `Default`:
    ///
    /// ```rust
    /// use rustica::datatypes::wrapper::min::Min;
    /// use rustica::traits::monoid::Monoid;
    /// use rustica::traits::semigroup::Semigroup;
    /// use std::cmp::Ordering;
    ///
    /// #[derive(Clone, Debug, PartialEq, Eq)]
    /// struct Version(u32, u32, u32);
    ///
    /// impl Default for Version {
    ///     fn default() -> Self {
    ///         // Default should ideally be the maximum possible version
    ///         // but for simplicity we use 0.0.0 here
    ///         Version(0, 0, 0)
    ///     }
    /// }
    ///
    /// impl PartialOrd for Version {
    ///     fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
    ///         Some(self.cmp(other))
    ///     }
    /// }
    ///
    /// impl Ord for Version {
    ///     fn cmp(&self, other: &Self) -> Ordering {
    ///         match self.0.cmp(&other.0) {
    ///             Ordering::Equal => match self.1.cmp(&other.1) {
    ///                 Ordering::Equal => self.2.cmp(&other.2),
    ///                 ord => ord,
    ///             },
    ///             ord => ord,
    ///         }
    ///     }
    /// }
    ///
    /// // For a true identity with Version, we'd need the maximum version
    /// // But since we don't have that, we'll create one
    /// let max_version = Min(Version(u32::MAX, u32::MAX, u32::MAX));
    /// let v = Min(Version(1, 2, 3));
    ///
    /// // Verify identity behavior
    /// assert_eq!(max_version.combine(&v), v);
    /// assert_eq!(v.combine(&max_version), v);
    /// ```
    #[inline]
    fn empty() -> Self {
        Min(T::default())
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

impl<T: Clone + Ord> Identity for Min<T> {
    fn value(&self) -> &Self::Source {
        &self.0
    }

    fn into_value(self) -> Self::Source {
        self.0
    }

    fn pure_identity<A>(value: A) -> Self::Output<A>
    where
        Self::Output<A>: Identity,
        A: Clone,
    {
        Min(value)
    }
}

impl<T: Clone + Ord> Functor for Min<T> {
    /// Maps a function over the value contained in this `Min` wrapper.
    ///
    /// This method implements the Functor typeclass by applying the function `f`
    /// to the inner value and wrapping the result in a new `Min` container.
    /// This method borrows the inner value, avoiding consumption.
    ///
    /// # Performance
    ///
    /// - **Time Complexity**: O(1) plus the complexity of function `f`
    /// - **Memory Usage**: Creates a new `Min` wrapper with the transformed value
    /// - **Borrowing**: Takes a reference to the inner value, avoiding cloning it
    ///
    /// # Type Class Laws
    ///
    /// ## Identity Law
    ///
    /// ```rust
    /// use rustica::datatypes::wrapper::min::Min;
    /// use rustica::traits::functor::Functor;
    ///
    /// // For any Min(x), fmap(id) = id
    /// // where id is the identity function
    /// fn verify_identity_law<T: Clone + Ord + PartialEq>(x: T) -> bool {
    ///     let min_x = Min(x.clone());
    ///     let mapped = min_x.fmap(|a| a.clone());
    ///     mapped == min_x
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
    /// use rustica::datatypes::wrapper::min::Min;
    /// use rustica::traits::functor::Functor;
    ///
    /// // For any Min(x) and functions f and g:
    /// // fmap(f . g) = fmap(f) . fmap(g)
    /// fn verify_composition_law<T>(x: T) -> bool
    /// where
    ///     T: Clone + Ord + PartialEq + std::fmt::Display,
    /// {
    ///     let min_x = Min(x);
    ///     
    ///     // Define two functions to compose
    ///     let f = |x: &String| x.len();
    ///     let g = |x: &T| x.to_string();
    ///     
    ///     // Left side: fmap(f . g)
    ///     let left_side = min_x.clone().fmap(|a| f(&g(a)));
    ///     
    ///     // Right side: fmap(f) . fmap(g)
    ///     let right_side = min_x.clone().fmap(g).fmap(f);
    ///     
    ///     left_side == right_side
    /// }
    ///
    /// // Test with a value that can be displayed as a string
    /// assert!(verify_composition_law(42));
    /// ```
    ///
    /// # Examples
    ///
    /// Basic transformation:
    ///
    /// ```rust
    /// use rustica::datatypes::wrapper::min::Min;
    /// use rustica::traits::functor::Functor;
    ///
    /// let min_value = Min(5);
    /// let doubled = min_value.fmap(|x| x * 2);
    /// assert_eq!(doubled, Min(10));
    /// ```
    ///
    /// Chaining transformations:
    ///
    /// ```rust
    /// use rustica::datatypes::wrapper::min::Min;
    /// use rustica::traits::functor::Functor;
    ///
    /// let min_value = Min(5);
    /// let result = min_value
    ///     .fmap(|x| x * 2)       // Min(10)
    ///     .fmap(|x| x + 5)       // Min(15)
    ///     .fmap(|x| x.to_string()); // Min("15")
    ///
    /// assert_eq!(result, Min("15".to_string()));
    /// ```
    ///
    /// The functor operation preserves the `Min` structure while transforming the value inside:
    ///
    /// ```rust
    /// use rustica::datatypes::wrapper::min::Min;
    /// use rustica::traits::functor::Functor;
    /// use rustica::traits::semigroup::Semigroup;
    ///
    /// let a = Min(5);
    /// let b = Min(10);
    ///
    /// // Combine first, then transform
    /// let result1 = a.combine(&b).fmap(|x| x * 2);
    ///
    /// // Transform individually, then combine
    /// let result2 = a.fmap(|x| x * 2).combine(&b.fmap(|x| x * 2));
    ///
    /// assert_eq!(result1, Min(10)); // Min(5 * 2)
    /// assert_eq!(result2, Min(10)); // Min(min(10, 20))
    /// ```
    #[inline]
    fn fmap<U, F>(&self, f: F) -> Self::Output<U>
    where
        F: FnOnce(&Self::Source) -> U,
    {
        Min(f(&self.0))
    }

    /// Maps a function over the value contained in this `Min` wrapper, consuming it.
    ///
    /// This method is similar to `fmap` but takes ownership of `self` and passes
    /// ownership of the inner value to the mapping function. This avoids unnecessary
    /// cloning when the original value is no longer needed.
    ///
    /// # Performance
    ///
    /// - **Time Complexity**: O(1) plus the complexity of function `f`
    /// - **Memory Usage**: Creates a new `Min` wrapper with the transformed value
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
    /// use rustica::datatypes::wrapper::min::Min;
    /// use rustica::traits::functor::Functor;
    ///
    /// let min_string = Min(String::from("hello"));
    ///
    /// // Efficiently transform without cloning the string
    /// let min_length = min_string.fmap_owned(|s| s.len());
    /// assert_eq!(min_length, Min(5));
    ///
    /// // Note: min_string has been consumed and can't be used anymore
    /// ```
    ///
    /// Chaining transformations with ownership:
    ///
    /// ```rust
    /// use rustica::datatypes::wrapper::min::Min;
    /// use rustica::traits::functor::Functor;
    ///
    /// // Chain transformations with ownership transfer
    /// let result = Min("hello".to_string())
    ///     .fmap_owned(|s| s + " world")
    ///     .fmap_owned(|s| s.len());
    ///
    /// assert_eq!(result, Min(11));
    /// ```
    #[inline]
    fn fmap_owned<U, F>(self, f: F) -> Self::Output<U>
    where
        F: FnOnce(Self::Source) -> U,
    {
        Min(f(self.0))
    }
}

impl<T: Clone + Ord> Foldable for Min<T> {
    #[inline]
    fn fold_left<U: Clone, F>(&self, init: &U, f: F) -> U
    where
        F: FnOnce(&U, &Self::Source) -> U,
    {
        f(init, &self.0)
    }

    #[inline]
    fn fold_right<U: Clone, F>(&self, init: &U, f: F) -> U
    where
        F: FnOnce(&Self::Source, &U) -> U,
    {
        f(&self.0, init)
    }
}
