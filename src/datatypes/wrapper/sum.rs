//! # Sum Wrapper
//!
//! This module provides the `Sum<T>` wrapper type which forms a semigroup under addition.
//! It enables treating values as summable entities regardless of context.
//!
//! ## Key Features
//!
//! - Implements `Semigroup` for any type implementing `Add`
//! - Implements Monoid when the inner type also has a zero value (`Default`)
//! - Provides a consistent way to combine values via addition
//! - Useful for aggregating collections of numeric values
//!
//! ## Performance Characteristics
//!
//! - Time Complexity: All operations (`combine`, `empty`, `fmap`, etc.) are O(1)
//! - Memory Usage: Stores exactly one value of type `T` with no additional overhead
//! - Clone Cost: Depends on the cost of cloning the inner type `T`
//!
//! ## Basic Usage
//!
//! ```rust
//! use rustica::datatypes::wrapper::sum::Sum;
//! use rustica::traits::semigroup::Semigroup;
//! use rustica::traits::monoid::Monoid;
//! use rustica::traits::identity::Identity;
//!
//! // Create Sum values with explicit type annotation
//! let a: Sum<i32> = Sum(5);
//! let b: Sum<i32> = Sum(10);
//!
//! // Combine them using the Semigroup trait
//! let c = a.combine(&b);
//! assert_eq!(*c.value(), 15);
//!
//! // Use the identity element from Monoid
//! let zero: Sum<i32> = Sum::empty();  // Sum(0)
//! assert_eq!(*zero.value(), 0);
//! assert_eq!(*a.combine(&zero).value(), 5);
//! assert_eq!(*zero.combine(&a).value(), 5);
//! ```
//!
//! ## With Collections
//!
//! ```rust
//! use rustica::datatypes::wrapper::sum::Sum;
//! use rustica::traits::semigroup::Semigroup;
//! use rustica::traits::monoid::Monoid;
//! use rustica::traits::identity::Identity;
//!
//! // Sum a collection of values
//! let numbers: Vec<i32> = vec![1, 2, 3, 4, 5];
//! let sum: Sum<i32> = numbers.iter()
//!     .map(|&n| Sum(n))
//!     .fold(Sum::empty(), |acc, x| acc.combine(&x));
//!
//! assert_eq!(*sum.value(), 15); // 1 + 2 + 3 + 4 + 5 = 15
//! ```
//!
//! ## Functional Programming Context
//!
//! The `Sum` wrapper is a fundamental building block for functional programming patterns:
//!
//! - **Aggregation**: Provides a principled way to combine values
//! - **Transformation**: Works with `Functor` to map inner values while preserving the wrapper
//! - **Folding**: Can be used with `Foldable` to reduce collections to a single value
//! - **Composition**: Combines with other algebraic structures for complex operations
//!
//! ```rust
//! use rustica::datatypes::wrapper::sum::Sum;
//! use rustica::traits::functor::Functor;
//! use rustica::traits::identity::Identity;
//!
//! // Transform the inner value while preserving the wrapper
//! let a = Sum(5);
//! let b = a.fmap(|x| x * 2);
//! assert_eq!(*b.value(), 10);
//! ```
//!
//! ## Type Class Implementations
//!
//! `Sum<T>` implements the following type classes:
//!
//! - `Semigroup`: For any `T` that implements `Add`
//! - `Monoid`: For any `T` that implements `Add` and `Default`
//! - `Functor`: For mapping operations over the inner value
//! - `Identity`: For accessing the wrapped value
//! - `HKT`: For higher-kinded type operations
//! - `Foldable`: For folding operations
//!
//! ## Type Class Laws
//!
//! ### Semigroup Laws
//!
//! ```rust
//! use rustica::datatypes::wrapper::sum::Sum;
//! use rustica::traits::semigroup::Semigroup;
//!
//! // Associativity: (a + b) + c = a + (b + c)
//! fn verify_associativity<T>(a: T, b: T, c: T) -> bool
//! where T: Clone + PartialEq + std::ops::Add<Output = T>
//! {
//!     let sum_a = Sum(a.clone());
//!     let sum_b = Sum(b.clone());
//!     let sum_c = Sum(c.clone());
//!
//!     let left = sum_a.clone().combine(&sum_b).combine(&sum_c.clone());
//!     let right = sum_a.combine(&sum_b.combine(&sum_c));
//!
//!     left == right
//! }
//!
//! assert!(verify_associativity(1, 2, 3));
//! assert!(verify_associativity(1.5, 2.5, 3.5));
//! ```
//!
//! ### Monoid Laws
//!
//! ```rust
//! use rustica::datatypes::wrapper::sum::Sum;
//! use rustica::traits::monoid::Monoid;
//! use rustica::traits::semigroup::Semigroup;
//!
//! // Left identity: empty() + a = a
//! // Right identity: a + empty() = a
//! fn verify_identity<T>(a: T) -> bool
//! where T: Clone + PartialEq + std::ops::Add<Output = T> + Default
//! {
//!     let sum_a = Sum(a.clone());
//!     let empty = Sum::<T>::empty();
//!
//!     let left_id = empty.clone().combine(&sum_a.clone());
//!     let right_id = sum_a.clone().combine(&empty);
//!
//!     left_id == sum_a.clone() && right_id == sum_a
//! }
//!
//! assert!(verify_identity(42));
//! assert!(verify_identity(3.14));
//! ```
//!
//! ### Functor Laws
//!
//! ```rust
//! use rustica::datatypes::wrapper::sum::Sum;
//! use rustica::traits::functor::Functor;
//!
//! // Identity: fmap(id) = id
//! // Composition: fmap(f . g) = fmap(f) . fmap(g)
//! fn verify_functor_laws<T>(value: T)
//! where T: Clone + PartialEq + std::ops::Add<Output = T> + std::fmt::Debug
//! {
//!     let sum = Sum(value);
//!     
//!     // Identity law
//!     let id_mapped = sum.clone().fmap(|x| x.clone());
//!     assert_eq!(id_mapped, sum);
//!     
//!     // Composition law
//!     let f = |x: &T| x.clone() + x.clone();
//!     let g = |x: &T| x.clone() + x.clone() + x.clone();
//!     
//!     let left = sum.clone().fmap(|x| f(&g(x)));
//!     let right = sum.fmap(g).fmap(f);
//!     
//!     assert_eq!(left, right);
//! }
//! ```

use crate::traits::foldable::Foldable;
use crate::traits::functor::Functor;
use crate::traits::hkt::HKT;
use crate::traits::identity::Identity;
use crate::traits::monoid::Monoid;
use crate::traits::semigroup::Semigroup;
use std::fmt;
use std::ops::Add;

/// A wrapper type that forms a semigroup under addition.
///
/// `Sum<T>` wraps a value of type `T` that can be added to other values of the same type.
/// When the inner type also implements `Default`, `Sum<T>` forms a complete monoid with
/// a zero identity element.
///
/// # Type Parameters
///
/// * `T`: The inner type that supports addition via the `Add` trait
///
/// # Properties
///
/// For `Sum<T>` to work correctly, the addition operation of `T` should satisfy:
///
/// - **Associativity**: `(a + b) + c = a + (b + c)`
/// - **Identity** (for Monoid): `0 + a = a + 0 = a`
///
/// # Performance
///
/// - Time Complexity: All operations are O(1)
/// - Memory Usage: Stores exactly one value of type `T`
///
/// # Examples
///
/// Basic usage with integers:
///
/// ```rust
/// use rustica::datatypes::wrapper::sum::Sum;
/// use rustica::traits::semigroup::Semigroup;
/// use rustica::traits::monoid::Monoid;
/// use rustica::traits::identity::Identity;
///
/// // Create Sum values
/// let a: Sum<i32> = Sum(5);
/// let b: Sum<i32> = Sum(7);
///
/// // Combine them (addition)
/// let c = a.combine(&b);
/// assert_eq!(*c.value(), 12);
///
/// // Addition is associative: (a + b) + c = a + (b + c)
/// let x: Sum<i32> = Sum(1);
/// let y: Sum<i32> = Sum(2);
/// let z: Sum<i32> = Sum(3);
///
/// let result1 = x.clone().combine(&y).combine(&z.clone());
/// let result2 = x.combine(&y.combine(&z));
/// assert_eq!(*result1.value(), *result2.value());
///
/// // Identity element
/// let id: Sum<i32> = Sum(0);
/// assert_eq!(*id.value(), 0);
/// assert_eq!(*Sum(42).combine(&id).value(), 42);
/// assert_eq!(*id.combine(&Sum(42)).value(), 42);
/// ```
///
/// Working with floating-point numbers:
///
/// ```rust
/// use rustica::datatypes::wrapper::sum::Sum;
/// use rustica::traits::semigroup::Semigroup;
/// use rustica::traits::identity::Identity;
///
/// let a: Sum<f64> = Sum(2.5);
/// let b: Sum<f64> = Sum(3.7);
/// let c = a.combine(&b);
/// assert_eq!(*c.value(), 6.2);
/// ```
///
/// Custom types that implement `Add`:
///
/// ```rust
/// use rustica::datatypes::wrapper::sum::Sum;
/// use rustica::traits::semigroup::Semigroup;
/// use rustica::traits::identity::Identity;
/// use std::ops::Add;
///
/// #[derive(Debug, Clone, PartialEq)]
/// struct Vector2D {
///     x: f64,
///     y: f64,
/// }
///
/// impl Add for Vector2D {
///     type Output = Self;
///
///     fn add(self, other: Self) -> Self {
///         Vector2D {
///             x: self.x + other.x,
///             y: self.y + other.y,
///         }
///     }
/// }
///
/// // Now we can use Sum with our custom type
/// let v1: Sum<Vector2D> = Sum(Vector2D { x: 1.0, y: 2.0 });
/// let v2: Sum<Vector2D> = Sum(Vector2D { x: 3.0, y: 4.0 });
/// let v3 = v1.combine(&v2);
///
/// assert_eq!(*v3.value(), Vector2D { x: 4.0, y: 6.0 });
/// ```
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Sum<T>(pub T);

impl<T: Clone + Add<Output = T>> Semigroup for Sum<T> {
    /// Combines two `Sum` values through addition, consuming self.
    ///
    /// This method implements the Semigroup operation for `Sum<T>`, which is adding
    /// two values. This method consumes both operands and returns a new `Sum`.
    ///
    /// # Performance
    ///
    /// - **Time Complexity**: O(1) plus the complexity of `T`'s addition operation
    /// - **Memory Usage**: Creates a new `Sum` wrapper with the result of the addition
    /// - **Ownership**: Takes ownership of both `self` and `other`
    ///
    /// # Type Class Laws
    ///
    /// ## Associativity
    ///
    /// ```rust
    /// use rustica::datatypes::wrapper::sum::Sum;
    /// use rustica::traits::semigroup::Semigroup;
    ///
    /// // For any a, b, c: (a ⊕ b) ⊕ c = a ⊕ (b ⊕ c)
    /// // where ⊕ is the combine operation
    /// fn verify_associativity<T: Clone + std::ops::Add<Output = T> + PartialEq>(a: T, b: T, c: T) -> bool {
    ///     let sum_a = Sum(a);
    ///     let sum_b = Sum(b);
    ///     let sum_c = Sum(c);
    ///     
    ///     let left = sum_a.clone().combine_owned(sum_b.clone()).combine_owned(sum_c.clone());
    ///     let right = sum_a.combine_owned(sum_b.combine_owned(sum_c));
    ///     
    ///     left == right
    /// }
    ///
    /// assert!(verify_associativity(1, 5, 3));
    /// assert!(verify_associativity(10, 2, 7));
    /// ```
    ///
    /// # Examples
    ///
    /// Basic usage with integers:
    ///
    /// ```rust
    /// use rustica::datatypes::wrapper::sum::Sum;
    /// use rustica::traits::semigroup::Semigroup;
    ///
    /// let a = Sum(5);
    /// let b = Sum(10);
    ///
    /// // a and b are consumed
    /// let c = a.combine_owned(b);
    /// assert_eq!(c, Sum(15));
    /// ```
    ///
    /// With custom types that implement `Add`:
    ///
    /// ```rust
    /// use rustica::datatypes::wrapper::sum::Sum;
    /// use rustica::traits::semigroup::Semigroup;
    /// use std::ops::Add;
    ///
    /// #[derive(Clone, Debug, PartialEq)]
    /// struct Vector2D {
    ///     x: f64,
    ///     y: f64,
    /// }
    ///
    /// impl Add for Vector2D {
    ///     type Output = Self;
    ///
    ///     fn add(self, other: Self) -> Self {
    ///         Vector2D {
    ///             x: self.x + other.x,
    ///             y: self.y + other.y,
    ///         }
    ///     }
    /// }
    ///
    /// let v1 = Sum(Vector2D { x: 1.0, y: 2.0 });
    /// let v2 = Sum(Vector2D { x: 3.0, y: 4.0 });
    ///
    /// let v3 = v1.combine_owned(v2);
    /// assert_eq!(v3, Sum(Vector2D { x: 4.0, y: 6.0 }));
    /// ```
    #[inline]
    fn combine_owned(self, other: Self) -> Self {
        Sum(self.0 + other.0)
    }

    /// Combines two `Sum` values through addition, borrowing self.
    ///
    /// This method implements the Semigroup operation for `Sum<T>`, which is adding
    /// two values. This method borrows both operands and returns a new `Sum`.
    ///
    /// # Performance
    ///
    /// - **Time Complexity**: O(1) plus the complexity of `T`'s addition operation
    /// - **Memory Usage**: Creates a new `Sum` wrapper with the result of the addition
    /// - **Borrowing**: Clones both values before performing the addition
    ///
    /// # Type Class Laws
    ///
    /// ## Associativity
    ///
    /// ```rust
    /// use rustica::datatypes::wrapper::sum::Sum;
    /// use rustica::traits::semigroup::Semigroup;
    ///
    /// // For any a, b, c: (a ⊕ b) ⊕ c = a ⊕ (b ⊕ c)
    /// // where ⊕ is the combine operation
    /// fn verify_associativity<T: Clone + std::ops::Add<Output = T> + PartialEq>(a: T, b: T, c: T) -> bool {
    ///     let sum_a = Sum(a);
    ///     let sum_b = Sum(b);
    ///     let sum_c = Sum(c);
    ///     
    ///     let left = sum_a.clone().combine(&sum_b).combine(&sum_c);
    ///     let right = sum_a.combine(&sum_b.combine(&sum_c));
    ///     
    ///     left == right
    /// }
    ///
    /// assert!(verify_associativity(1, 5, 3));
    /// assert!(verify_associativity(10, 2, 7));
    /// ```
    ///
    /// # Examples
    ///
    /// Basic usage with integers:
    ///
    /// ```rust
    /// use rustica::datatypes::wrapper::sum::Sum;
    /// use rustica::traits::semigroup::Semigroup;
    ///
    /// let a = Sum(5);
    /// let b = Sum(10);
    ///
    /// // a and b are borrowed
    /// let c = a.combine(&b);
    /// assert_eq!(c, Sum(15));
    ///
    /// // a and b can still be used
    /// let d = b.combine(&a);
    /// assert_eq!(d, Sum(15));
    /// ```
    ///
    /// Combining multiple values in a collection:
    ///
    /// ```rust
    /// use rustica::datatypes::wrapper::sum::Sum;
    /// use rustica::traits::semigroup::Semigroup;
    /// use rustica::traits::monoid::Monoid;
    ///
    /// let values = vec![Sum(1), Sum(2), Sum(3), Sum(4), Sum(5)];
    ///
    /// // Sum all values in the collection
    /// let result = values.iter().fold(Sum::empty(), |acc, x| acc.combine(x));
    /// assert_eq!(result, Sum(15));
    /// ```
    #[inline]
    fn combine(&self, other: &Self) -> Self {
        Sum(self.0.clone() + other.0.clone())
    }
}

impl<T: fmt::Debug> fmt::Debug for Sum<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Sum({:?})", self.0)
    }
}

impl<T: fmt::Display> fmt::Display for Sum<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Sum({})", self.0)
    }
}

impl<T: Clone + Add<Output = T> + Default> Monoid for Sum<T> {
    /// Returns the identity element for the addition operation.
    ///
    /// This method creates a `Sum` that contains the default value of type `T`,
    /// which is expected to be an identity element for addition (typically zero).
    /// Any `Sum` combined with this identity element should remain unchanged.
    ///
    /// # Performance
    ///
    /// - **Time Complexity**: O(1) plus the complexity of `T::default()`
    /// - **Memory Usage**: Creates a single new `Sum` wrapper with the default value of `T`
    /// - **Note**: For primitive numeric types, `T::default()` returns zero
    ///
    /// # Type Class Laws
    ///
    /// ## Left Identity
    ///
    /// ```rust
    /// use rustica::datatypes::wrapper::sum::Sum;
    /// use rustica::traits::monoid::Monoid;
    /// use rustica::traits::semigroup::Semigroup;
    ///
    /// // For any a: empty() ⊕ a = a, where ⊕ is the combine operation
    /// fn verify_left_identity<T: Clone + Default + std::ops::Add<Output = T> + PartialEq>(a: T) -> bool {
    ///     let sum_a = Sum(a.clone());
    ///     let id = Sum::<T>::empty();
    ///     
    ///     id.combine(&sum_a) == sum_a
    /// }
    ///
    /// assert!(verify_left_identity(42));
    /// assert!(verify_left_identity(3.14));
    /// ```
    ///
    /// ## Right Identity
    ///
    /// ```rust
    /// use rustica::datatypes::wrapper::sum::Sum;
    /// use rustica::traits::monoid::Monoid;
    /// use rustica::traits::semigroup::Semigroup;
    ///
    /// // For any a: a ⊕ empty() = a, where ⊕ is the combine operation
    /// fn verify_right_identity<T: Clone + Default + std::ops::Add<Output = T> + PartialEq>(a: T) -> bool {
    ///     let sum_a = Sum(a.clone());
    ///     let id = Sum::<T>::empty();
    ///     
    ///     sum_a.combine(&id) == sum_a
    /// }
    ///
    /// assert!(verify_right_identity(42));
    /// assert!(verify_right_identity(3.14));
    /// ```
    ///
    /// # Examples
    ///
    /// Basic usage with integers:
    ///
    /// ```rust
    /// use rustica::datatypes::wrapper::sum::Sum;
    /// use rustica::traits::monoid::Monoid;
    /// use rustica::traits::semigroup::Semigroup;
    /// use rustica::traits::identity::Identity;
    ///
    /// // Create the identity element (Sum(0))
    /// let identity: Sum<i32> = Sum::empty();
    /// assert_eq!(*identity.value(), 0);
    ///
    /// // Identity property demonstration
    /// let a = Sum(42);
    /// assert_eq!(a.combine(&identity), a);  // a + 0 = a
    /// assert_eq!(identity.combine(&a), a);  // 0 + a = a
    /// ```
    ///
    /// With floating point numbers:
    ///
    /// ```rust
    /// use rustica::datatypes::wrapper::sum::Sum;
    /// use rustica::traits::monoid::Monoid;
    /// use rustica::traits::semigroup::Semigroup;
    ///
    /// let identity: Sum<f64> = Sum::empty();  // Sum(0.0)
    /// let value = Sum(3.14);
    ///
    /// assert_eq!(value.combine(&identity), value);  // 3.14 + 0.0 = 3.14
    /// ```
    ///
    /// Using `empty()` with custom types:
    ///
    /// ```rust
    /// use rustica::datatypes::wrapper::sum::Sum;
    /// use rustica::traits::monoid::Monoid;
    /// use rustica::traits::semigroup::Semigroup;
    /// use std::ops::Add;
    ///
    /// #[derive(Clone, Debug, Default, PartialEq)]
    /// struct Counter {
    ///     count: i32,
    /// }
    ///
    /// impl Add for Counter {
    ///     type Output = Self;
    ///
    ///     fn add(self, other: Self) -> Self {
    ///         Counter {
    ///             count: self.count + other.count,
    ///         }
    ///     }
    /// }
    ///
    /// // Create the identity element (Sum(Counter { count: 0 }))
    /// let identity: Sum<Counter> = Sum::empty();
    /// assert_eq!(identity, Sum(Counter { count: 0 }));
    ///
    /// let counter = Sum(Counter { count: 5 });
    /// assert_eq!(counter.combine(&identity), counter);  // Identity law
    /// ```
    #[inline]
    fn empty() -> Self {
        Sum(T::default())
    }
}

impl<T> HKT for Sum<T> {
    type Source = T;
    type Output<U> = Sum<U>;
}

impl<T: Clone + Add<Output = T>> Identity for Sum<T> {
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
        Sum(value)
    }
}

impl<T: Clone + Add<Output = T>> Functor for Sum<T> {
    /// Maps a function over the wrapped value, borrowing self.
    ///
    /// This method applies the function `f` to the value inside the `Sum` wrapper,
    /// returning a new `Sum` containing the result. The original `Sum` is preserved.
    ///
    /// # Performance
    ///
    /// - **Time Complexity**: O(1) plus the complexity of the function `f`
    /// - **Memory Usage**: Creates a new `Sum` wrapper with the result of `f`
    /// - **Borrowing**: Borrows the inner value without cloning it
    ///
    /// # Type Class Laws
    ///
    /// ## Identity Law
    ///
    /// ```rust
    /// use rustica::datatypes::wrapper::sum::Sum;
    /// use rustica::traits::functor::Functor;
    ///
    /// // For any Sum(x): fmap(id) == id
    /// // where id is the identity function
    /// fn verify_identity_law<T: Clone + std::ops::Add<Output = T> + PartialEq>(x: T) -> bool {
    ///     let sum_x = Sum(x.clone());
    ///     
    ///     // Apply identity function
    ///     let mapped = sum_x.fmap(|val| val.clone());
    ///     
    ///     mapped == sum_x
    /// }
    ///
    /// assert!(verify_identity_law(42));
    /// assert!(verify_identity_law(3.14));
    /// ```
    ///
    /// ## Composition Law
    ///
    /// ```rust
    /// use rustica::datatypes::wrapper::sum::Sum;
    /// use rustica::traits::functor::Functor;
    ///
    /// // For any Sum(x) and functions f and g:
    /// // fmap(f . g) == fmap(f) . fmap(g)
    /// fn verify_composition_law() -> bool {
    ///     let sum_x = Sum(5);
    ///     
    ///     // Define two functions
    ///     let f = |x: i32| x * 2;
    ///     let g = |x: i32| x + 1;
    ///     
    ///     // Apply the functions in two different ways
    ///     let result1 = sum_x.clone().fmap(|x| f(g(*x)));
    ///     let result2 = sum_x.fmap(|x| g(*x)).fmap(|x| f(*x));
    ///     
    ///     result1 == result2
    /// }
    ///
    /// assert!(verify_composition_law());
    /// ```
    ///
    /// # Examples
    ///
    /// Basic usage with integers:
    ///
    /// ```rust
    /// use rustica::datatypes::wrapper::sum::Sum;
    /// use rustica::traits::functor::Functor;
    ///
    /// let num = Sum(5);
    ///
    /// // Double the value
    /// let doubled = num.fmap(|x| x * 2);
    /// assert_eq!(doubled, Sum(10));
    ///
    /// // Chain transformations
    /// let result = num
    ///     .fmap(|x| x * 3)     // Sum(15)
    ///     .fmap(|x| x + 5)     // Sum(20)
    ///     .fmap(|x| x.to_string()); // Sum("20")
    ///
    /// assert_eq!(result, Sum("20".to_string()));
    /// ```
    ///
    /// Interaction with Semigroup operations:
    ///
    /// ```rust
    /// use rustica::datatypes::wrapper::sum::Sum;
    /// use rustica::traits::functor::Functor;
    /// use rustica::traits::semigroup::Semigroup;
    ///
    /// let a = Sum(10);
    /// let b = Sum(20);
    ///
    /// // Apply a transformation after combining values
    /// let result1 = a.clone().combine(&b).fmap(|x| x * 2);
    /// assert_eq!(result1, Sum(60));  // (10 + 20) * 2 = 60
    ///
    /// // Apply a transformation before combining values
    /// let result2 = a.fmap(|x| x * 2).combine(&b.fmap(|x| x * 2));
    /// assert_eq!(result2, Sum(60));  // (10 * 2) + (20 * 2) = 60
    /// ```
    #[inline]
    fn fmap<U, F>(&self, f: F) -> Self::Output<U>
    where
        F: Fn(&Self::Source) -> U,
    {
        Sum(f(&self.0))
    }

    /// Maps a function over the wrapped value, consuming self.
    ///
    /// This method applies the function `f` to the value inside the `Sum` wrapper,
    /// consuming the original `Sum` and returning a new `Sum` containing the result.
    /// This is more efficient than `fmap` when you no longer need the original `Sum`.
    ///
    /// # Performance
    ///
    /// - **Time Complexity**: O(1) plus the complexity of the function `f`
    /// - **Memory Usage**: Creates a new `Sum` wrapper with the result of `f`
    /// - **Ownership**: Takes ownership of the inner value, avoiding clones
    ///
    /// # Type Class Laws
    ///
    /// ## Identity Law
    ///
    /// ```rust
    /// use rustica::datatypes::wrapper::sum::Sum;
    /// use rustica::traits::functor::Functor;
    ///
    /// // For any Sum(x): fmap_owned(id) == id
    /// // where id is the identity function
    /// fn verify_identity_law<T: Clone + std::ops::Add<Output = T> + PartialEq>(x: T) -> bool {
    ///     let sum_x = Sum(x.clone());
    ///     
    ///     // Apply identity function
    ///     let mapped = sum_x.fmap_owned(|val| val);
    ///     
    ///     mapped == Sum(x)
    /// }
    ///
    /// assert!(verify_identity_law(42));
    /// assert!(verify_identity_law(3.14));
    /// ```
    ///
    /// ## Composition Law
    ///
    /// ```rust
    /// use rustica::datatypes::wrapper::sum::Sum;
    /// use rustica::traits::functor::Functor;
    ///
    /// // For any Sum(x) and functions f and g:
    /// // fmap_owned(f . g) == fmap_owned(g) . fmap_owned(f)
    /// fn verify_composition_law() -> bool {
    ///     let sum_x = Sum(5);
    ///     
    ///     // Define two functions
    ///     let f = |x: i32| x * 2;
    ///     let g = |x: i32| x + 1;
    ///     
    ///     // Compose the functions (g then f)
    ///     let fg = |x: i32| f(g(x));
    ///     
    ///     // Apply the functions in two different ways
    ///     let result1 = Sum(5).fmap_owned(fg);
    ///     let result2 = Sum(5).fmap_owned(g).fmap_owned(f);
    ///     
    ///     result1 == result2
    /// }
    ///
    /// assert!(verify_composition_law());
    /// ```
    ///
    /// # Examples
    ///
    /// Basic usage with integers:
    ///
    /// ```rust
    /// use rustica::datatypes::wrapper::sum::Sum;
    /// use rustica::traits::functor::Functor;
    ///
    /// let num = Sum(5);
    ///
    /// // Consume num and double the value
    /// let doubled = num.fmap_owned(|x| x * 2);
    /// assert_eq!(doubled, Sum(10));
    /// ```
    ///
    /// Chaining transformations with ownership transfer:
    ///
    /// ```rust
    /// use rustica::datatypes::wrapper::sum::Sum;
    /// use rustica::traits::functor::Functor;
    ///
    /// let result = Sum(5)
    ///     .fmap_owned(|n| n * 2)
    ///     .fmap_owned(|n| n + 5)
    ///     .fmap_owned(|n| n.to_string());
    ///
    /// assert_eq!(result, Sum("15".to_string()));  // 5*2=10, 10+5=15
    /// ```
    #[inline]
    fn fmap_owned<U, F>(self, f: F) -> Self::Output<U>
    where
        F: FnOnce(Self::Source) -> U,
        Self::Source: Add<Output = Self::Source>,
    {
        Sum(f(self.0))
    }
}

impl<T: Clone + Add<Output = T>> Foldable for Sum<T> {
    fn fold_left<U, F>(&self, init: &U, f: F) -> U
    where
        F: Fn(&U, &Self::Source) -> U,
        U: Clone,
    {
        f(init, &self.0)
    }

    fn fold_right<U, F>(&self, init: &U, f: F) -> U
    where
        F: Fn(&Self::Source, &U) -> U,
        U: Clone,
    {
        f(&self.0, init)
    }
}
