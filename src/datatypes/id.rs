//! # Identity Monad
//!
//! The `Id` datatype represents the identity monad, which is the simplest possible monad - it just wraps a value
//! without adding any additional context or effects. While it might seem trivial, it serves several important purposes
//! in functional programming.
//!
//! ## Functional Programming Context
//!
//! In functional programming, the identity monad is often used as:
//!
//! - A baseline for understanding how monads work
//! - A way to work with pure values in a monadic context
//! - A useful tool for testing and prototyping monadic code
//!
//! The identity monad is found in many functional programming languages:
//!
//! - `Id` in Cats (Scala)
//! - `Identity` in Arrow (Kotlin)
//! - `Identity` in fp-ts (TypeScript)
//! - `Identity` in Haskell
//!
//! ## Performance Characteristics
//!
//! The `Id` monad has optimal performance characteristics as it adds minimal overhead:
//!
//! - **Time Complexity**: All operations are O(1) as they simply manipulate the wrapped value directly
//! - **Memory Usage**: Uses only the memory required by the wrapped value plus a constant small overhead
//! - **Stack Usage**: No additional stack frames beyond the function calls themselves
//!
//! This makes `Id` ideal for situations where you need monadic interfaces without performance penalties.
//!
//! ## Type Class Implementations
//!
//! The `Id` type implements several important type classes:
//!
//! - `Functor`: Allows mapping functions over the wrapped value
//! - `Applicative`: Enables applying functions wrapped in `Id` to values wrapped in `Id`
//! - `Monad`: Provides sequencing of operations and context-sensitive computations
//! - `Comonad`: Provides operations to extract values and extend computations
//! - `Semigroup`: Combines two Id values when the inner type is a Semigroup
//! - `Monoid`: Provides an empty value when the inner type is a Monoid
//! - `Foldable`: Enables folding operations over the contained value
//!
//! These implementations follow the standard laws for each type class, making `Id` a lawful
//! instance of these abstractions.
//!
//! ## Type Class Laws
//!
//! The `Id` type implements the following type class laws. See the documentation for
//! the specific functions (`fmap`, `apply`, `bind`) for examples demonstrating these laws.
//!
//! ### Functor Laws
//!
//! The `Id` type satisfies the functor laws:
//!
//! 1. **Identity Law**: `fmap(id) = id`
//!    - Mapping the identity function over an `Id` returns the original `Id` unchanged.
//!
//! 2. **Composition Law**: `fmap(f . g) = fmap(f) . fmap(g)`
//!    - Mapping a composed function is the same as mapping each function in sequence.
//!
//! ### Applicative Laws
//!
//! The `Id` type satisfies the applicative laws:
//!
//! 1. **Identity Law**: `pure(id) <*> v = v`
//!    - Applying the pure identity function to any value returns the original value.
//!
//! 2. **Homomorphism Law**: `pure(f) <*> pure(x) = pure(f(x))`
//!    - Applying a pure function to a pure value is the same as applying the function to the value and then wrapping in `pure`.
//!
//! 3. **Interchange Law**: `u <*> pure(y) = pure($ y) <*> u`
//!    - Where `$ y` is a function that applies its argument to y.
//!
//! 4. **Composition Law**: `pure(.) <*> u <*> v <*> w = u <*> (v <*> w)`
//!    - Composing applicative functions is associative.
//!
//! ### Monad Laws
//!
//! The `Id` type satisfies the monad laws:
//!
//! 1. **Left Identity**: `return a >>= f = f a`
//!    - Binding a function to a pure value is the same as applying the function directly.
//!
//! 2. **Right Identity**: `m >>= return = m`
//!    - Binding the pure function to a monad returns the original monad.
//!
//! 3. **Associativity**: `(m >>= f) >>= g = m >>= (\x -> f x >>= g)`
//!    - Sequential binds can be nested in either direction with the same result.
//!
//! ## Basic Usage
//!
//! ```rust
//! use rustica::prelude::*;
//! use rustica::datatypes::id::Id;
//! use rustica::traits::identity::Identity;
//!
//! // Create an Id value
//! let x: Id<i32> = Id::new(42);
//!
//! // Access the inner value
//! assert_eq!(*x.value(), 42);
//!
//! // Map a function over the value (Functor)
//! let doubled = x.fmap(|n| n * 2);
//! assert_eq!(*doubled.value(), 84);
//!
//! // Lift a value into Id context (Pure)
//! let pure_value = Id::<i32>::pure(&100);
//! assert_eq!(*pure_value.value(), 100);
//! ```
//!
//! ## Iterator Example
//!
//! Iterating over an `Id` yields its value exactly once. `Id` supports iteration for owned, shared, and mutable references.
//!
//! ```rust
//! use rustica::datatypes::id::Id;
//! let id = Id::new(42);
//! // Owned iterator
//! let mut iter = id.into_iter();
//! assert_eq!(iter.next(), Some(42));
//! assert_eq!(iter.next(), None);
//!
//! // Shared reference iterator
//! let id = Id::new(42);
//! let mut iter = (&id).into_iter();
//! assert_eq!(iter.next(), Some(&42));
//! assert_eq!(iter.next(), None);
//!
//! // Mutable reference iterator
//! let mut id = Id::new(42);
//! let mut iter = (&mut id).into_iter();
//! assert_eq!(iter.next(), Some(&mut 42));
//! assert_eq!(iter.next(), None);
//! ```
use crate::traits::{
    applicative::Applicative, comonad::Comonad, composable::Composable, foldable::Foldable,
    functor::Functor, hkt::HKT, identity::Identity, monad::Monad, monoid::Monoid, pure::Pure,
    semigroup::Semigroup,
};
use quickcheck::{Arbitrary, Gen};

/// The identity monad, which represents a computation that simply wraps a value.
///
/// The `Id` type is the simplest possible monad - it just wraps a value without adding any
/// additional context or effects. While it might seem trivial, it serves several important purposes:
///
/// 1. It provides a way to work with pure values in a monadic context
/// 2. It serves as a good example for understanding monad laws and behavior
/// 3. It's useful for testing and prototyping monadic code
/// 4. It serves as a base case for monad transformers
/// 5. It helps create a consistent API across different monadic types
///
/// # Performance Characteristics
///
/// * **Time Complexity**: O(1) for all operations
/// * **Memory Usage**: O(1) overhead beyond the wrapped value
/// * **Stack Usage**: No additional stack frames beyond the function calls themselves
///
/// # Type Parameters
///
/// * `T` - The type of the wrapped value
///
/// # Examples
///
/// ```rust
/// use rustica::prelude::*;
/// use rustica::datatypes::id::Id;
/// use rustica::traits::identity::Identity;
/// use rustica::traits::applicative::Applicative;
///
/// // Create Id values
/// let x = Id::new(5);
/// let y = Id::new(3);
/// let z = Id::new(2);
///
/// // Access the inner value using Identity trait's value() method
/// assert_eq!(*x.value(), 5);
///
/// // Using Functor to map over Id
/// let doubled = x.fmap(|n| n * 2);
/// assert_eq!(*doubled.value(), 10);
///
/// // Using Pure to lift a value into Id context
/// let pure_value = Id::<i32>::pure(&42);
/// assert_eq!(*pure_value.value(), 42);
///
/// // Using Applicative to apply functions
/// // 1. Apply a function wrapped in Id
/// let add_one = Id::new(|x: &i32| x + 1);
/// let result = add_one.apply(&x);
/// assert_eq!(*result.value(), 6);
///
/// // 2. Combine two Id values with lift2
/// let add = |a: &i32, b: &i32| a + b;
/// let sum = Id::<i32>::lift2(&add, &x, &y);
/// assert_eq!(*sum.value(), 8);
///
/// // 3. Combine three Id values with lift3
/// let multiply = |a: &i32, b: &i32, c: &i32| a * b * c;
/// let product = Id::<i32>::lift3(&multiply, &x, &y, &z);
/// assert_eq!(*product.value(), 30);
///
/// // Working with different types
/// let greeting = Id::new("Hello");
/// let count = Id::new(3_usize);
/// let repeat = |s: &&str, n: &usize| s.repeat(*n);
/// let repeated = Id::<&str>::lift2(&repeat, &greeting, &count);
/// assert_eq!(*repeated.value(), "HelloHelloHello");
///
/// // Chaining operations
/// let result = x
///     .fmap(|n| n + 1)     // 5 -> 6
///     .fmap(|n| n * 2)     // 6 -> 12
///     .fmap(|n| n.to_string());
/// assert_eq!(*result.value(), "12");
/// ```
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
#[must_use = "This is a pure value wrapper which does nothing unless used"]
pub struct Id<T> {
    value: T,
}

impl<T> Id<T> {
    /// Creates a new `Id` value wrapping the given value.
    ///
    /// This is the primary constructor for `Id` values. It takes any value
    /// and wraps it in the `Id` context.
    ///
    /// # Arguments
    ///
    /// * `x` - The value to wrap in `Id`
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::id::Id;
    /// use rustica::traits::identity::Identity;
    ///
    /// let x = Id::new(42);
    /// assert_eq!(*x.value(), 42);
    ///
    /// // Create Id with different types
    /// let s: Id<String> = Id::new("hello".to_string());
    /// assert_eq!(*s.value(), "hello");
    /// ```
    #[inline]
    pub const fn new(x: T) -> Self {
        Id { value: x }
    }

    /// Extracts the inner value from Id
    ///
    /// This consumes the Id and returns the contained value.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::id::Id;
    ///
    /// let x = Id::new(42);
    /// let value = x.into_inner();
    /// assert_eq!(value, 42);
    /// ```
    #[inline(always)]
    pub fn into_inner(self) -> T {
        self.value
    }

    /// Returns a mutable reference to the inner value.
    pub fn value_mut(&mut self) -> &mut T {
        &mut self.value
    }

    /// Sequences two Id operations, discarding the first result.
    ///
    /// # Arguments
    ///
    /// * `next` - The next Id operation to execute
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::id::Id;
    /// use rustica::prelude::*;
    ///
    /// let x = Id::new(42);
    /// let y = Id::new("hello");
    /// let result = x.then(y);
    /// assert_eq!(*result.value(), "hello");
    /// ```
    #[inline(always)]
    pub fn then<U>(self, next: Id<U>) -> Id<U> {
        Id { value: next.value }
    }
}

impl<T> std::convert::AsRef<T> for Id<T> {
    #[inline(always)]
    fn as_ref(&self) -> &T {
        &self.value
    }
}

impl<T: Clone> Id<T> {
    /// Creates a new `Id` value from a reference.
    ///
    /// This constructor clones the referenced value and wraps it in the `Id` context.
    ///
    /// # Arguments
    ///
    /// * `x` - The referenced value to clone and wrap in `Id`
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::id::Id;
    /// use rustica::traits::identity::Identity;
    ///
    /// let value = 42;
    /// let x = Id::from_ref(&value);
    /// assert_eq!(*x.value(), 42);
    /// ```
    #[inline]
    pub fn from_ref(x: &T) -> Self {
        Id { value: x.clone() }
    }
}

impl<T> HKT for Id<T> {
    type Source = T;
    type Output<U> = Id<U>;
}

impl<T> Identity for Id<T> {
    #[inline(always)]
    fn value(&self) -> &Self::Source {
        &self.value
    }

    #[inline]
    fn pure_identity<A>(value: A) -> Self::Output<A>
    where
        Self::Output<A>: Identity,
    {
        Id::new(value)
    }

    #[inline]
    fn into_value(self) -> Self::Source {
        self.value
    }
}

impl<T> Functor for Id<T> {
    #[inline]
    fn fmap<B, F>(&self, f: F) -> Self::Output<B>
    where
        F: Fn(&Self::Source) -> B,
    {
        Id::new(f(&self.value))
    }

    #[inline]
    fn fmap_owned<B, F>(self, f: F) -> Self::Output<B>
    where
        F: FnOnce(Self::Source) -> B,
    {
        Id::new(f(self.value))
    }
}

impl<T> Composable for Id<T> {}

impl<T: Clone> Pure for Id<T> {
    #[inline]
    fn pure<U: Clone>(x: &U) -> Self::Output<U> {
        Id::new(x.clone())
    }
}

impl<T: Clone> Applicative for Id<T> {
    #[inline]
    fn apply<A, B>(&self, value: &Self::Output<A>) -> Self::Output<B>
    where
        Self::Source: Fn(&A) -> B,
    {
        Id::new(self.value()(value.value()))
    }

    #[inline]
    fn lift2<A, B, C, F>(f: F, fa: &Self::Output<A>, fb: &Self::Output<B>) -> Self::Output<C>
    where
        F: Fn(&A, &B) -> C,
        A: Clone,
        B: Clone,
        C: Clone,
        Self: Sized,
    {
        Id::new(f(fa.value(), fb.value()))
    }

    #[inline]
    fn lift3<A, B, C, D, F>(
        f: F, fa: &Self::Output<A>, fb: &Self::Output<B>, fc: &Self::Output<C>,
    ) -> Self::Output<D>
    where
        F: Fn(&A, &B, &C) -> D,
        A: Clone,
        B: Clone,
        C: Clone,
        D: Clone,
        Self: Sized,
    {
        Id::new(f(fa.value(), fb.value(), fc.value()))
    }

    #[inline]
    fn apply_owned<U, B>(self, value: Self::Output<U>) -> Self::Output<B>
    where
        Self::Source: Fn(U) -> B,
        U: Clone,
        B: Clone,
    {
        Id::new((self.value)(value.value))
    }

    #[inline]
    fn lift2_owned<A, B, C, F>(f: F, fa: Self::Output<A>, fb: Self::Output<B>) -> Self::Output<C>
    where
        F: Fn(A, B) -> C,
        A: Clone,
        B: Clone,
        C: Clone,
        Self: Sized,
    {
        Id::new(f(fa.value, fb.value))
    }

    #[inline]
    fn lift3_owned<A, B, C, D, F>(
        f: F, fa: Self::Output<A>, fb: Self::Output<B>, fc: Self::Output<C>,
    ) -> Self::Output<D>
    where
        F: Fn(A, B, C) -> D,
        A: Clone,
        B: Clone,
        C: Clone,
        D: Clone,
        Self: Sized,
    {
        Id::new(f(fa.value, fb.value, fc.value))
    }
}

impl<T: Clone> Monad for Id<T> {
    /// Sequences two Id operations, with the second depending on the result of the first.
    ///
    /// This method implements the `bind` operation (also known as `flatMap` or `>>=`)
    /// from the Monad typeclass in functional programming. It allows you to sequence
    /// Id computations where the second computation depends on the value produced
    /// by the first.
    ///
    /// # Performance
    ///
    /// * Time Complexity: O(1) - Simply applies the function to the wrapped value
    /// * Memory Usage: Depends only on the function `f` and its output
    ///
    /// # Type Parameters
    ///
    /// * `U`: The type of the value produced by the second computation
    /// * `F`: The type of the function that produces the second computation
    ///
    /// # Arguments
    ///
    /// * `f` - Function that takes the value from the first computation and returns a new Id computation
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::id::Id;
    /// use rustica::traits::monad::Monad;
    /// use rustica::traits::identity::Identity;
    ///
    /// // Simple binding with a transformation
    /// let x = Id::new(5);
    /// let result = x.bind(|n| Id::new(n * 2));
    /// assert_eq!(*result.value(), 10);
    ///
    /// // Chaining multiple bind operations
    /// let result = Id::new(5)
    ///     .bind(|n| Id::new(n + 3))          // 5 -> 8
    ///     .bind(|n| Id::new(n * 2))          // 8 -> 16
    ///     .bind(|n| Id::new(format!("{}", n))); // 16 -> "16"
    /// assert_eq!(*result.value(), "16");
    ///
    /// // Conditional logic in bind
    /// let process = |n: &i32| {
    ///     if *n > 0 {
    ///         Id::new(format!("Positive: {}", n))
    ///     } else {
    ///         Id::new(format!("Non-positive: {}", n))
    ///     }
    /// };
    ///
    /// let pos = Id::new(42).bind(process);
    /// assert_eq!(*pos.value(), "Positive: 42");
    ///
    /// let neg = Id::new(-10).bind(process);
    /// assert_eq!(*neg.value(), "Non-positive: -10");
    /// ```
    #[inline]
    fn bind<U, F>(&self, f: F) -> Self::Output<U>
    where
        F: Fn(&Self::Source) -> Self::Output<U>,
    {
        f(&self.value)
    }

    #[inline]
    fn join<U>(&self) -> Self::Output<U>
    where
        Self::Source: Clone + Into<Self::Output<U>>,
    {
        self.value.clone().into()
    }

    #[inline]
    fn bind_owned<U, F>(self, f: F) -> Self::Output<U>
    where
        F: Fn(Self::Source) -> Self::Output<U>,
        U: Clone,
        Self: Sized,
    {
        f(self.value)
    }

    #[inline]
    fn join_owned<U>(self) -> Self::Output<U>
    where
        Self::Source: Into<Self::Output<U>>,
        U: Clone,
        Self: Sized,
    {
        self.value.into()
    }
}

impl<T: Clone> Comonad for Id<T> {
    /// Extracts the value from the Id context.
    ///
    /// The `extract` operation (also known as `counit`) is the dual to the `pure` operation
    /// in a Monad. It extracts the contained value from the `Id` context.
    ///
    /// # Performance
    ///
    /// * Time Complexity: O(1) - Simple clone operation
    /// * Memory Usage: Dependent on the size of the wrapped value
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::id::Id;
    /// use rustica::traits::comonad::Comonad;
    ///
    /// let id = Id::new(42);
    /// let value = id.extract();
    /// assert_eq!(value, 42);
    /// ```
    #[inline]
    fn extract(&self) -> Self::Source {
        self.value.clone()
    }

    /// Returns a copy of the current `Id` value.
    ///
    /// The `duplicate` operation is the dual of `join` in a Monad. For `Id`, it simply
    /// returns a clone of the current `Id` value, as there is no nested structure to create.
    ///
    /// # Performance
    ///
    /// * Time Complexity: O(1) - Simple clone operation
    /// * Memory Usage: Slight overhead from cloning the value
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::id::Id;
    /// use rustica::traits::comonad::Comonad;
    /// use rustica::traits::identity::Identity;
    ///
    /// let id = Id::new(42);
    /// let duplicated = id.duplicate();
    ///
    /// // The result is equivalent to id.clone()
    /// assert_eq!(*duplicated.value(), 42);
    /// ```
    #[inline]
    fn duplicate(&self) -> Self {
        self.clone()
    }

    /// Applies a function to the entire `Id` context and wraps the result in a new `Id`.
    ///
    /// The `extend` operation (also known as `cobind` or `=>>`) is the dual of `bind` in a Monad.
    /// It applies a function to the entire `Id` context, producing a new `Id` with the result.
    ///
    /// # Performance
    ///
    /// * Time Complexity: O(1) plus the complexity of function `f`
    /// * Memory Usage: Depends on the return type of function `f`
    ///
    /// # Type Parameters
    ///
    /// * `U`: The type of the value produced by the function
    /// * `F`: The type of the function that processes the context
    ///
    /// # Arguments
    ///
    /// * `f` - Function that takes the entire Id context and returns a value
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::id::Id;
    /// use rustica::traits::comonad::Comonad;
    /// use rustica::traits::identity::Identity;
    ///
    /// let id = Id::new(5);
    ///
    /// // Apply a function to the context, squaring the inner value
    /// let result = id.extend(|ctx| {
    ///     let inner_value = *ctx.value();
    ///     inner_value * inner_value  // Produces 25
    /// });
    ///
    /// assert_eq!(*result.value(), 25);
    /// ```
    #[inline]
    fn extend<U, F>(&self, f: F) -> Self::Output<U>
    where
        F: Fn(&Self) -> U,
    {
        Id::new(f(self))
    }
}

impl<T: Semigroup> Semigroup for Id<T> {
    /// Combines two `Id` values using the `combine` operation of the inner type.
    ///
    /// This operation is available when the wrapped type `T` implements the `Semigroup` trait.
    /// It combines the inner values using their `combine` operation and wraps the result in a new `Id`.
    ///
    /// # Performance
    ///
    /// * Time Complexity: O(1) plus the complexity of the inner type's `combine` operation
    /// * Memory Usage: Depends on the memory usage of the inner type's `combine` operation
    ///
    /// # Arguments
    ///
    /// * `other` - Another `Id` value to combine with this one
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::id::Id;
    /// use rustica::traits::semigroup::Semigroup;
    /// use rustica::traits::identity::Identity;
    ///
    /// // Combining two Id<String> values
    /// let a = Id::new("Hello, ".to_string());
    /// let b = Id::new("world!".to_string());
    ///
    /// let combined = a.combine(&b);
    /// assert_eq!(*combined.value(), "Hello, world!");
    ///
    /// // Combining two Id<Vec<i32>> values
    /// let v1 = Id::new(vec![1, 2]);
    /// let v2 = Id::new(vec![3, 4]);
    /// let combined_vec = v1.combine(&v2);
    /// assert_eq!(*combined_vec.value(), vec![1, 2, 3, 4]);
    /// ```
    #[inline]
    fn combine(&self, other: &Self) -> Self {
        Id::new(self.value.combine(&other.value))
    }

    /// Owned version of `combine` that consumes both values.
    ///
    /// This works the same as `combine` but takes ownership of both values, potentially
    /// avoiding unnecessary clones when the values are no longer needed separately.
    ///
    /// # Performance
    ///
    /// * Time Complexity: O(1) plus the complexity of the inner type's `combine_owned` operation
    /// * Memory Usage: Potentially more efficient than `combine` as it can avoid clones
    ///
    /// # Arguments
    ///
    /// * `other` - Another `Id` value to combine with this one
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::id::Id;
    /// use rustica::traits::semigroup::Semigroup;
    /// use rustica::traits::identity::Identity;
    ///
    /// // Combining two Id<Vec<i32>> values
    /// let a = Id::new(vec![1, 2, 3]);
    /// let b = Id::new(vec![4, 5, 6]);
    ///
    /// let combined = a.combine_owned(b);
    /// assert_eq!(*combined.value(), vec![1, 2, 3, 4, 5, 6]);
    /// ```
    #[inline]
    fn combine_owned(self, other: Self) -> Self {
        Id::new(self.value.combine_owned(other.value))
    }
}

impl<T: Monoid> Monoid for Id<T> {
    /// Returns an empty `Id` value using the `empty` operation of the inner type.
    ///
    /// This operation is available when the wrapped type `T` implements the `Monoid` trait.
    /// It creates an `Id` wrapping the `empty` value of the inner type.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::id::Id;
    /// use rustica::traits::monoid::Monoid;
    /// use rustica::traits::identity::Identity;
    ///
    /// // Empty Id<String>
    /// let empty_string = Id::<String>::empty();
    /// assert_eq!(*empty_string.value(), "");
    ///
    /// // Empty Id<Vec<i32>>
    /// let empty_vec = Id::<Vec<i32>>::empty();
    /// assert_eq!(*empty_vec.value(), vec![]);
    /// ```
    #[inline]
    fn empty() -> Self {
        Id::new(T::empty())
    }
}

impl<T: Clone> Foldable for Id<T> {
    #[inline]
    fn fold_left<U, F>(&self, init: &U, f: F) -> U
    where
        U: Clone,
        F: Fn(&U, &Self::Source) -> U,
    {
        f(init, &self.value)
    }

    #[inline]
    fn fold_right<U, F>(&self, init: &U, f: F) -> U
    where
        U: Clone,
        F: Fn(&Self::Source, &U) -> U,
    {
        f(&self.value, init)
    }
}

impl<T> From<T> for Id<T> {
    #[inline]
    fn from(value: T) -> Self {
        Id::new(value)
    }
}

impl<T: Default> Default for Id<T> {
    #[inline]
    fn default() -> Self {
        Id::new(T::default())
    }
}

// Iterator support: iterates over the value, always yields exactly one item.
impl<T> IntoIterator for Id<T> {
    type Item = T;
    type IntoIter = std::option::IntoIter<T>;

    fn into_iter(self) -> Self::IntoIter {
        Some(self.into_inner()).into_iter()
    }
}

impl<'a, T> IntoIterator for &'a Id<T> {
    type Item = &'a T;
    type IntoIter = std::slice::Iter<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        std::slice::from_ref(self.value()).iter()
    }
}

impl<'a, T> IntoIterator for &'a mut Id<T> {
    type Item = &'a mut T;
    type IntoIter = std::slice::IterMut<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        std::slice::from_mut(self.value_mut()).iter_mut()
    }
}

impl<T: Clone + Arbitrary> Arbitrary for Id<T> {
    fn arbitrary(g: &mut Gen) -> Self {
        Id::new(T::arbitrary(g))
    }
}
