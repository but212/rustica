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
//! - `Identity`: For accessing the wrapped value
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
//! assert_eq!(a.combine(&b), Product(12)); // 3 * 4 = 12
//! assert_eq!(b.combine(&c), Product(20)); // 4 * 5 = 20
//!
//! // Chaining multiplications
//! let result = a.combine(&b).combine(&c);
//! assert_eq!(result, Product(60)); // 3 * 4 * 5 = 60
//!
//! // Identity element (multiplicative identity: 1)
//! let empty = Product::empty();
//! assert_eq!(a.combine(&empty), a); // 3 * 1 = 3
//! ```
use crate::traits::functor::Functor;
use crate::traits::hkt::HKT;
use crate::traits::monoid::Monoid;
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
/// let c = a.combine(&b);
/// assert_eq!(c, Product(35));
///
/// // Multiplication is associative: (a * b) * c = a * (b * c)
/// let x = Product(2);
/// let y = Product(3);
/// let z = Product(4);
///
/// let result1 = x.clone().combine(&y).combine(&z.clone());
/// let result2 = x.combine(&y.combine(&z));
/// assert_eq!(result1, result2);
///
/// // Identity element
/// let id = Product::empty();  // Product(1)
/// assert_eq!(id, Product(1));
/// assert_eq!(Product(42).combine(&id), Product(42));
/// assert_eq!(id.combine(&Product(42)), Product(42));
/// ```
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub struct Product<T>(pub T);

impl<T: Clone> Product<T> {
    /// Unwraps the product value.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use rustica::datatypes::wrapper::product::Product;
    /// let product = Product(42);
    /// assert_eq!(product.unwrap(), 42);
    /// ```
    #[inline]
    pub fn unwrap(&self) -> T {
        self.0.clone()
    }

    /// Unwraps the product value or returns a default.
    ///
    /// Since `Product` always contains a value, this method simply returns the contained value.
    /// The `default` parameter is ignored.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use rustica::datatypes::wrapper::product::Product;
    /// let product = Product(42);
    /// assert_eq!(product.unwrap_or(0), 42);
    /// ```
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

impl<T: Clone + Mul<Output = T>> Semigroup for Product<T> {
    /// Combines two `Product` values through multiplication, consuming self.
    ///
    /// This method implements the Semigroup operation for `Product<T>`, which is multiplying
    /// two values. This method consumes both operands and returns a new `Product`.
    ///
    /// # Performance
    ///
    /// - **Time Complexity**: O(1) plus the complexity of `T`'s multiplication operation
    /// - **Memory Usage**: Creates a new `Product` wrapper with the result of the multiplication
    /// - **Ownership**: Takes ownership of both `self` and `other`
    ///
    /// # Type Class Laws
    ///
    /// ## Associativity
    ///
    /// ```rust
    /// use rustica::datatypes::wrapper::product::Product;
    /// use rustica::traits::semigroup::Semigroup;
    ///
    /// // For any a, b, c: (a ⊕ b) ⊕ c = a ⊕ (b ⊕ c)
    /// // where ⊕ is the combine operation (multiplication)
    /// fn verify_associativity<T: Clone + std::ops::Mul<Output = T> + PartialEq>(a: T, b: T, c: T) -> bool {
    ///     let product_a = Product(a);
    ///     let product_b = Product(b);
    ///     let product_c = Product(c);
    ///     
    ///     let left = product_a.clone().combine_owned(product_b.clone()).combine_owned(product_c.clone());
    ///     let right = product_a.combine_owned(product_b.combine_owned(product_c));
    ///     
    ///     left == right
    /// }
    ///
    /// assert!(verify_associativity(2, 3, 4));
    /// assert!(verify_associativity(2.5, 3.0, 4.0));
    /// ```
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::wrapper::product::Product;
    /// use rustica::traits::semigroup::Semigroup;
    ///
    /// let a = Product(5);
    /// let b = Product(10);
    ///
    /// // a and b are consumed
    /// let c = a.combine_owned(b);
    /// assert_eq!(c, Product(50));
    /// ```
    #[inline]
    fn combine_owned(self, other: Self) -> Self {
        Product(self.0 * other.0)
    }

    /// Combines two `Product` values through multiplication, borrowing self.
    ///
    /// This method implements the Semigroup operation for `Product<T>`, which is multiplying
    /// two values. This method borrows both operands and returns a new `Product`.
    ///
    /// # Performance
    ///
    /// - **Time Complexity**: O(1) plus the complexity of `T`'s multiplication operation
    /// - **Memory Usage**: Creates a new `Product` wrapper with the result of the multiplication
    /// - **Borrowing**: Clones both values before performing the multiplication
    ///
    /// # Type Class Laws
    ///
    /// ## Associativity
    ///
    /// ```rust
    /// use rustica::datatypes::wrapper::product::Product;
    /// use rustica::traits::semigroup::Semigroup;
    ///
    /// // For any a, b, c: (a ⊕ b) ⊕ c = a ⊕ (b ⊕ c)
    /// // where ⊕ is the combine operation (multiplication)
    /// fn verify_associativity<T: Clone + std::ops::Mul<Output = T> + PartialEq>(a: T, b: T, c: T) -> bool {
    ///     let product_a = Product(a);
    ///     let product_b = Product(b);
    ///     let product_c = Product(c);
    ///     
    ///     let left = product_a.combine(&product_b).combine(&product_c);
    ///     let right = product_a.combine(&product_b.combine(&product_c));
    ///     
    ///     left == right
    /// }
    ///
    /// assert!(verify_associativity(2, 3, 4));
    /// assert!(verify_associativity(2.5, 3.0, 4.0));
    /// ```
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::wrapper::product::Product;
    /// use rustica::traits::semigroup::Semigroup;
    ///
    /// let a = Product(5);
    /// let b = Product(10);
    ///
    /// // a and b are borrowed
    /// let c = a.combine(&b);
    /// assert_eq!(c, Product(50));
    ///
    /// // a and b can still be used
    /// let d = b.combine(&a);
    /// assert_eq!(d, Product(50));
    /// ```
    #[inline]
    fn combine(&self, other: &Self) -> Self {
        Product(self.0.clone() * other.0.clone())
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

impl<T: Clone + Mul<Output = T> + From<u8>> Monoid for Product<T> {
    /// Returns the identity element for the multiplication operation.
    ///
    /// This method creates a `Product` that contains the value `1` of type `T`,
    /// which is expected to be an identity element for multiplication.
    /// Any `Product` combined with this identity element should remain unchanged.
    ///
    /// # Performance
    ///
    /// - **Time Complexity**: O(1) plus the complexity of `T::from(1)`
    /// - **Memory Usage**: Creates a single new `Product` wrapper with the multiplicative identity
    /// - **Note**: For primitive numeric types, `T::from(1)` returns the value 1
    ///
    /// # Type Class Laws
    ///
    /// ## Left Identity
    ///
    /// ```rust
    /// use rustica::datatypes::wrapper::product::Product;
    /// use rustica::traits::monoid::Monoid;
    /// use rustica::traits::semigroup::Semigroup;
    ///
    /// // For any a: empty() ⊕ a = a, where ⊕ is the combine operation
    /// fn verify_left_identity<T: Clone + From<u8> + std::ops::Mul<Output = T> + PartialEq>(a: T) -> bool {
    ///     let product_a = Product(a.clone());
    ///     let id = Product::<T>::empty();
    ///     
    ///     id.combine(&product_a) == product_a
    /// }
    ///
    /// assert!(verify_left_identity(42));
    /// assert!(verify_left_identity(3.14));
    /// ```
    ///
    /// ## Right Identity
    ///
    /// ```rust
    /// use rustica::datatypes::wrapper::product::Product;
    /// use rustica::traits::monoid::Monoid;
    /// use rustica::traits::semigroup::Semigroup;
    ///
    /// // For any a: a ⊕ empty() = a, where ⊕ is the combine operation
    /// fn verify_right_identity<T: Clone + From<u8> + std::ops::Mul<Output = T> + PartialEq>(a: T) -> bool {
    ///     let product_a = Product(a.clone());
    ///     let id = Product::<T>::empty();
    ///     
    ///     product_a.combine(&id) == product_a
    /// }
    ///
    /// assert!(verify_right_identity(42));
    /// assert!(verify_right_identity(3.14));
    /// ```
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
    /// assert_eq!(identity.unwrap(), 1);
    ///
    /// // Identity property demonstration
    /// let a = Product(42);
    /// assert_eq!(a.combine(&identity), a);  // a * 1 = a
    /// assert_eq!(identity.combine(&a), a);  // 1 * a = a
    /// ```
    #[inline]
    fn empty() -> Self {
        Product(T::from(1))
    }
}

impl<T> HKT for Product<T> {
    type Source = T;
    type Output<U> = Product<U>;
}

impl<T: Clone + Mul<Output = T>> Functor for Product<T> {
    /// Maps a function over the wrapped value, borrowing self.
    ///
    /// This method applies the function `f` to the value inside the `Product` wrapper,
    /// returning a new `Product` containing the result. The original `Product` is preserved.
    ///
    /// # Performance
    ///
    /// - **Time Complexity**: O(1) plus the complexity of the function `f`
    /// - **Memory Usage**: Creates a new `Product` wrapper with the result of `f`
    /// - **Borrowing**: Borrows the inner value without cloning it
    ///
    /// # Type Class Laws
    ///
    /// ## Identity Law
    ///
    /// ```rust
    /// use rustica::datatypes::wrapper::product::Product;
    /// use rustica::traits::functor::Functor;
    ///
    /// // For any Product(x): fmap(id) == id
    /// // where id is the identity function
    /// fn verify_identity_law<T: Clone + std::ops::Mul<Output = T> + PartialEq>(x: T) -> bool {
    ///     let product_x = Product(x.clone());
    ///     
    ///     // Apply identity function
    ///     let mapped = product_x.fmap(|val| val.clone());
    ///     
    ///     mapped == product_x
    /// }
    ///
    /// assert!(verify_identity_law(42));
    /// assert!(verify_identity_law(3.14));
    /// ```
    ///
    /// ## Composition Law
    ///
    /// ```rust
    /// use rustica::datatypes::wrapper::product::Product;
    /// use rustica::traits::functor::Functor;
    ///
    /// // For any Product(x) and functions f and g:
    /// // fmap(f . g) == fmap(f) . fmap(g)
    /// fn verify_composition_law() -> bool {
    ///     let product_x = Product(5);
    ///     
    ///     // Define two functions
    ///     let f = |x: &i32| x * 2;
    ///     let g = |x: &i32| x + 1;
    ///     
    ///     // Apply the functions in two different ways
    ///     let result1 = product_x.clone().fmap(|x| f(&g(x)));
    ///     let result2 = product_x.fmap(g).fmap(f);
    ///     
    ///     result1 == result2
    /// }
    ///
    /// assert!(verify_composition_law());
    /// ```
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::wrapper::product::Product;
    /// use rustica::traits::functor::Functor;
    ///
    /// let num = Product(5);
    ///
    /// // Double the value
    /// let doubled = num.fmap(|x| x * 2);
    /// assert_eq!(doubled, Product(10));
    ///
    /// // Chain transformations
    /// let result = num
    ///     .fmap(|x| x * 3)      // Product(15)
    ///     .fmap(|x| x + 5)      // Product(20)
    ///     .fmap(|x| x.to_string()); // Product("20")
    ///
    /// assert_eq!(result, Product("20".to_string()));
    /// ```
    #[inline]
    fn fmap<U, F>(&self, f: F) -> Self::Output<U>
    where
        F: FnOnce(&Self::Source) -> U,
    {
        Product(f(&self.0))
    }

    /// Maps a function over the wrapped value, consuming self.
    ///
    /// This method applies the function `f` to the value inside the `Product` wrapper,
    /// consuming the original `Product` and returning a new `Product` containing the result.
    /// This is more efficient than `fmap` when you no longer need the original `Product`.
    ///
    /// # Performance
    ///
    /// - **Time Complexity**: O(1) plus the complexity of the function `f`
    /// - **Memory Usage**: Creates a new `Product` wrapper with the result of `f`
    /// - **Ownership**: Takes ownership of the inner value, avoiding clones
    ///
    /// # Type Class Laws
    ///
    /// ## Identity Law
    ///
    /// ```rust
    /// use rustica::datatypes::wrapper::product::Product;
    /// use rustica::traits::functor::Functor;
    ///
    /// // For any Product(x): fmap_owned(id) == id
    /// // where id is the identity function
    /// fn verify_identity_law<T: Clone + std::ops::Mul<Output = T> + PartialEq>(x: T) -> bool {
    ///     let product_x = Product(x.clone());
    ///     
    ///     // Apply identity function
    ///     let mapped = product_x.fmap_owned(|val| val);
    ///     
    ///     mapped == Product(x)
    /// }
    ///
    /// assert!(verify_identity_law(42));
    /// assert!(verify_identity_law(3.14));
    /// ```
    ///
    /// ## Composition Law
    ///
    /// ```rust
    /// use rustica::datatypes::wrapper::product::Product;
    /// use rustica::traits::functor::Functor;
    ///
    /// // For any Product(x) and functions f and g:
    /// // fmap_owned(f . g) == fmap_owned(g) . fmap_owned(f)
    /// fn verify_composition_law() -> bool {
    ///     let x = 5;
    ///     
    ///     // Define two functions
    ///     let f = |x: i32| x * 2;
    ///     let g = |x: i32| x + 1;
    ///     
    ///     // Compose the functions (g then f)
    ///     let fg = |x: i32| f(g(x));
    ///     
    ///     // Apply the functions in two different ways
    ///     let result1 = Product(x).fmap_owned(fg);
    ///     let result2 = Product(x).fmap_owned(g).fmap_owned(f);
    ///     
    ///     result1 == result2
    /// }
    ///
    /// assert!(verify_composition_law());
    /// ```
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::wrapper::product::Product;
    /// use rustica::traits::functor::Functor;
    ///
    /// let num = Product(5);
    ///
    /// // Consume num and double the value
    /// let doubled = num.fmap_owned(|x| x * 2);
    /// assert_eq!(doubled, Product(10));
    /// ```
    #[inline]
    fn fmap_owned<U, F>(self, f: F) -> Self::Output<U>
    where
        F: FnOnce(Self::Source) -> U,
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
