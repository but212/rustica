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
//! ## Type Class Implementations
//!
//! The `Id` type implements several important type classes:
//!
//! - `Functor`: Allows mapping functions over the wrapped value
//! - `Applicative`: Enables applying functions wrapped in `Id` to values wrapped in `Id`
//! - `Monad`: Provides sequencing of operations and context-sensitive computations
//!
//! These implementations follow the standard laws for each type class, making `Id` a lawful
//! instance of these abstractions.
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
use crate::traits::{
    applicative::Applicative, composable::Composable, foldable::Foldable, functor::Functor,
    hkt::HKT, identity::Identity, monad::Monad, monoid::Monoid, pure::Pure, semigroup::Semigroup,
};

/// The identity monad, which represents a computation that simply wraps a value.
///
/// The `Id` type is the simplest possible monad - it just wraps a value without adding any
/// additional context or effects. While it might seem trivial, it serves several important purposes:
///
/// 1. It provides a way to work with pure values in a monadic context
/// 2. It serves as a good example for understanding monad laws and behavior
/// 3. It's useful for testing and prototyping monadic code
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
/// let result = x.apply(&add_one);
/// assert_eq!(*result.value(), 6);
///
/// // 2. Combine two Id values with lift2
/// let add = |a: &i32, b: &i32| a + b;
/// let sum = x.lift2(&y, &add);
/// assert_eq!(*sum.value(), 8);
///
/// // 3. Combine three Id values with lift3
/// let multiply = |a: &i32, b: &i32, c: &i32| a * b * c;
/// let product = x.lift3(&y, &z, &multiply);
/// assert_eq!(*product.value(), 30);
///
/// // Working with different types
/// let greeting = Id::new("Hello");
/// let count = Id::new(3_usize);
/// let repeat = |s: &&str, n: &usize| s.repeat(*n);
/// let repeated = greeting.lift2(&count, &repeat);
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
    #[inline]
    pub fn into_inner(self) -> T {
        self.value
    }

    /// Maps a function over the contained value, consuming self.
    ///
    /// This is an ownership-aware version of mapping that consumes the original `Id`
    /// and returns a new one containing the mapped value.
    ///
    /// # Arguments
    ///
    /// * `f` - Function to apply to the contained value
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::id::Id;
    /// use rustica::prelude::*;
    ///
    /// let x = Id::new(42);
    /// let mapped = x.map(|n| n.to_string());
    /// assert_eq!(*mapped.value(), "42");
    /// ```
    #[inline]
    pub fn map<U, F>(self, f: F) -> Id<U>
    where
        F: FnOnce(T) -> U,
    {
        Id::new(f(self.value))
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
    #[inline]
    pub fn then<U>(self, next: Id<U>) -> Id<U> {
        Id::new(next.value)
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
    #[inline]
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
        F: Fn(Self::Source) -> B,
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
    fn apply<B, F>(&self, f: &Self::Output<F>) -> Self::Output<B>
    where
        F: Fn(&Self::Source) -> B,
    {
        Id::new(f.value()(&self.value))
    }

    #[inline]
    fn lift2<B, C, F>(&self, b: &Self::Output<B>, f: F) -> Self::Output<C>
    where
        F: Fn(&Self::Source, &B) -> C,
    {
        Id::new(f(&self.value, b.value()))
    }

    #[inline]
    fn lift3<B, C, D, F>(&self, b: &Self::Output<B>, c: &Self::Output<C>, f: F) -> Self::Output<D>
    where
        F: Fn(&Self::Source, &B, &C) -> D,
    {
        Id::new(f(&self.value, b.value(), c.value()))
    }

    #[inline]
    fn apply_owned<B, F>(self, f: Self::Output<F>) -> Self::Output<B>
    where
        F: Fn(Self::Source) -> B,
        Self: Sized,
    {
        Id::new(f.value()(self.value))
    }

    #[inline]
    fn lift2_owned<B, C, F>(self, b: Self::Output<B>, f: F) -> Self::Output<C>
    where
        F: Fn(Self::Source, B) -> C,
        Self: Sized,
        B: Clone,
    {
        Id::new(f(self.value, b.value))
    }

    #[inline]
    fn lift3_owned<B, C, D, F>(
        self,
        b: Self::Output<B>,
        c: Self::Output<C>,
        f: F,
    ) -> Self::Output<D>
    where
        F: Fn(Self::Source, B, C) -> D,
        Self: Sized,
        B: Clone,
        C: Clone,
    {
        Id::new(f(self.value, b.value, c.value))
    }
}

impl<T: Clone> Monad for Id<T> {
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

impl<T: Semigroup> Semigroup for Id<T> {
    #[inline]
    fn combine(&self, other: &Self) -> Self {
        Id::new(self.value.combine(&other.value))
    }

    #[inline]
    fn combine_owned(self, other: Self) -> Self {
        Id::new(self.value.combine_owned(other.value))
    }
}

impl<T: Monoid> Monoid for Id<T> {
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
    /// Creates a new `Id` with the default value for type `T`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::id::Id;
    /// use rustica::traits::identity::Identity;
    /// use std::default::Default;
    ///
    /// let default_id: Id<i32> = Default::default();
    /// assert_eq!(*default_id.value(), 0); // i32's default is 0
    ///
    /// let default_string: Id<String> = Default::default();
    /// assert_eq!(*default_string.value(), ""); // String's default is empty string
    /// ```
    #[inline]
    fn default() -> Self {
        Id::new(T::default())
    }
}
