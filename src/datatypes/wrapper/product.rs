//! # Product
//!
//! This module provides the `Product` wrapper type which forms a semigroup under multiplication.
//!
//! ## Functional Programming Context
//!
//! The `Product` wrapper is a fundamental building block for functional programming patterns:
//!
//! - **Aggregation**: Provides a principled way to combine values through multiplication
//! - **Transformation**: Works with `Functor` to map inner values while preserving the wrapper
//!
//! ## Type Class Laws
//!
//! ### Semigroup Laws
//!
//! `Product<T>` satisfies the semigroup associativity law:
//!
//! - **Associativity**: `(a ⊕ b) ⊕ c = a ⊕ (b ⊕ c)`
//!   - For all values a, b, and c, combining a and b and then combining the result with c
//!     yields the same result as combining a with the combination of b and c.
//!
//! ### Monoid Laws
//!
//! `Product<T>` satisfies the monoid identity laws when the inner type has a multiplicative identity:
//!
//! - **Left Identity**: `empty() ⊕ a = a`
//!   - Combining the identity element (typically 1) with any value gives the original value.
//!
//! - **Right Identity**: `a ⊕ empty() = a`
//!   - Combining any value with the identity element gives the original value.
//!
//! ### Functor Laws
//!
//! `Product<T>` satisfies the functor laws:
//!
//! - **Identity**: `fmap(id) = id`
//!   - Mapping the identity function over a `Product` value gives the same value.
//!
//! - **Composition**: `fmap(f . g) = fmap(f) . fmap(g)`
//!   - Mapping a composed function is the same as mapping each function in sequence.
//!
//! ## Type Class Implementations
//!
//! `Product<T>` implements the following type classes:
//!
//! - `Semigroup`: For any `T` that implements `Mul`
//! - `Monoid`: For any `T` that implements `Mul` and `From<u8>` (for the identity element)
//! - `Functor`: For mapping operations over the inner value
//! - `HKT`: For higher-kinded type operations
//!
//! ## Quick Start
//!
//! ```rust
//! use rustica::datatypes::wrapper::product::Product;
//! use rustica::traits::{semigroup::Semigroup, monoid::Monoid};
//!
//! // Create Product wrappers
//! let a = Product(3);
//! let b = Product(4);
//! let c = Product(5);
//!
//! // Values are combined by multiplication
//! assert_eq!(a.combine(b), Product(12)); // 3 * 4 = 12
//! assert_eq!(b.combine(c), Product(20)); // 4 * 5 = 20
//!
//! // Chaining multiplications
//! let result = a.combine(b).combine(c);
//! assert_eq!(result, Product(60)); // 3 * 4 * 5 = 60
//!
//! // Identity element (multiplicative identity: 1)
//! let empty = Product::empty();
//! assert_eq!(a.combine(empty), a); // 3 * 1 = 3
//! ```
use crate::traits::functor::Functor;
use crate::traits::hkt::HKT;
use crate::traits::monoid::Monoid;
use crate::traits::one::One;
use crate::traits::semigroup::Semigroup;
use std::fmt;
use std::ops::Mul;

/// A wrapper type that forms a semigroup under multiplication.
///
/// `Product<T>` wraps a value of type `T` that can be multiplied with other values of the same type.
/// When the inner type also has a multiplicative identity of 1, `Product<T>` forms a complete monoid.
///
/// # Type Parameters
///
/// * `T`: The inner type that supports multiplication via the `Mul` trait
///
/// # Properties
///
/// For `Product<T>` to work correctly, the multiplication operation of `T` should satisfy:
///
/// - **Associativity**: `(a * b) * c = a * (b * c)`
/// - **Identity** (for Monoid): `1 * a = a * 1 = a`
///
/// # Examples
///
/// ```rust
/// use rustica::datatypes::wrapper::product::Product;
/// use rustica::traits::semigroup::Semigroup;
/// use rustica::traits::monoid::Monoid;
///
/// // Create Product values
/// let a = Product(5);
/// let b = Product(7);
///
/// // Combine them (multiplication)
/// let c = a.combine(b);
/// assert_eq!(c, Product(35));
///
/// // Multiplication is associative: (a * b) * c = a * (b * c)
/// let x = Product(2);
/// let y = Product(3);
/// let z = Product(4);
///
/// let result1 = x.clone().combine(y).combine(z.clone());
/// let result2 = x.combine(y.combine(z));
/// assert_eq!(result1, result2);
///
/// // Identity element
/// let id = Product::empty();  // Product(1)
/// assert_eq!(id, Product(1));
/// assert_eq!(Product(42).combine(id), Product(42));
/// assert_eq!(id.combine(Product(42)), Product(42));
/// ```
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Product<T>(pub T);

impl<T> Product<T> {
    /// Creates a new `Product` wrapping the given value.
    #[inline]
    pub const fn new(value: T) -> Self {
        Product(value)
    }

    /// Consumes the wrapper and returns the contained value.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::wrapper::product::Product;
    /// let product = Product(42);
    /// assert_eq!(product.into_inner(), 42);
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
    /// use rustica::datatypes::wrapper::product::Product;
    /// let product = Product(42);
    /// assert_eq!(*product.get(), 42);
    /// ```
    #[inline]
    pub fn get(&self) -> &T {
        &self.0
    }
}

impl<T: Clone> Product<T> {
    /// Unwraps the product value.
    #[deprecated(since = "0.15.0", note = "use `into_inner()` or `get()` instead")]
    #[inline]
    pub fn unwrap(&self) -> T {
        self.0.clone()
    }

    /// Unwraps the product value or returns a default.
    #[deprecated(since = "0.15.0", note = "use `into_inner()` or `get()` instead")]
    #[inline]
    pub fn unwrap_or(&self, _default: T) -> T {
        self.0.clone()
    }
}

impl<T> AsRef<T> for Product<T> {
    #[inline]
    fn as_ref(&self) -> &T {
        &self.0
    }
}

impl<T: Mul<Output = T>> Semigroup for Product<T> {
    /// Combines two `Product` values through multiplication, consuming self.
    ///
    /// # Examples
    /// ```rust
    /// use rustica::datatypes::wrapper::product::Product;
    /// use rustica::traits::semigroup::Semigroup;
    ///
    /// let a = Product(5);
    /// let b = Product(10);
    /// let c = a.combine(b);
    /// assert_eq!(c, Product(50));
    /// ```
    #[inline]
    fn combine(self, other: Self) -> Self {
        Product(self.0 * other.0)
    }
}

impl<T: fmt::Debug> fmt::Debug for Product<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Product({:?})", self.0)
    }
}

impl<T: fmt::Display> fmt::Display for Product<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Product({})", self.0)
    }
}

impl<T: Clone + Mul<Output = T> + One> Monoid for Product<T> {
    /// Returns the identity element for the multiplication operation.
    ///
    /// This method creates a `Product` that contains the value `1` of type `T`,
    /// which is expected to be an identity element for multiplication.
    /// Any `Product` combined with this identity element should remain unchanged.
    ///
    /// # Performance
    ///
    /// - **Time Complexity**: O(1) plus the complexity of `T::one()`
    /// - **Memory Usage**: Creates a single new `Product` wrapper with the multiplicative identity
    /// - **Note**: For primitive numeric types, `T::one()` returns the value 1
    ///
    /// # Type Class Laws
    ///
    /// ## Left Identity
    ///
    ///
    /// Algebraic laws for this wrapper are verified by unit tests.
    ///
    /// ## Right Identity
    ///
    ///
    /// Algebraic laws for this wrapper are verified by unit tests.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::wrapper::product::Product;
    /// use rustica::traits::monoid::Monoid;
    /// use rustica::traits::semigroup::Semigroup;
    ///
    /// // Create the identity element (Product(1))
    /// let identity: Product<i32> = Product::empty();
    /// assert_eq!(*identity.get(), 1);
    ///
    /// // Identity property demonstration
    /// let a = Product(42);
    /// assert_eq!(a.combine(identity), a);  // a * 1 = a
    /// assert_eq!(identity.combine(a), a);  // 1 * a = a
    /// ```
    #[inline]
    fn empty() -> Self {
        Product(T::one())
    }
}

impl<T> HKT for Product<T> {
    type Source = T;
    type Output<U> = Product<U>;
}

impl<T: Mul<Output = T>> Functor for Product<T> {
    #[inline]
    fn fmap<U, F>(self, mut f: F) -> Self::Output<U>
    where
        F: FnMut(Self::Source) -> U,
    {
        Product(f(self.0))
    }
}

impl<T> From<T> for Product<T> {
    #[inline]
    fn from(value: T) -> Self {
        Product(value)
    }
}
