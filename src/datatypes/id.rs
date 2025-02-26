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
//! let doubled = x.fmap(&|n| n * 2);
//! assert_eq!(*doubled.value(), 84);
//! 
//! // Lift a value into Id context (Pure)
//! let pure_value = Id::<i32>::pure(100);
//! assert_eq!(*pure_value.value(), 100);
//! ```

use crate::traits::{
    hkt::HKT,
    identity::Identity,
    functor::Functor,
    pure::Pure,
    applicative::Applicative,
    monad::Monad,
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
/// let doubled = x.fmap(&|n| n * 2);
/// assert_eq!(*doubled.value(), 10);
///
/// // Using Pure to lift a value into Id context
/// let pure_value = Id::<i32>::pure(42);
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
///     .fmap(&|n| n + 1)     // 5 -> 6
///     .fmap(&|n| n * 2)     // 6 -> 12
///     .fmap(&|n| n.to_string());
/// assert_eq!(*result.value(), "12");
/// ```
#[derive(Clone)]
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
    pub fn new(x: T) -> Self {
        Id { value: x }
    }
}

impl<T> HKT for Id<T> {
    type Source = T;
    type Output<U> = Id<U>;
}

impl<T> Identity for Id<T> {
    /// Returns a reference to the wrapped value.
    /// 
    /// This method provides access to the inner value stored in the `Id` type.
    /// 
    /// # Examples
    /// 
    /// ```rust
    /// use rustica::datatypes::id::Id;
    /// use rustica::traits::identity::Identity;
    /// 
    /// let x = Id::new(42);
    /// assert_eq!(*x.value(), 42);
    /// ```
    fn value(&self) -> &Self::Source {
        &self.value
    }
}

impl<T> Functor for Id<T> {
    /// Maps a function over the wrapped value.
    /// 
    /// This implementation follows the functor laws:
    /// 1. Identity: `fmap(id) = id`
    /// 2. Composition: `fmap(f . g) = fmap(f) . fmap(g)`
    /// 
    /// # Arguments
    /// 
    /// * `f` - The function to apply to the wrapped value
    /// 
    /// # Examples
    /// 
    /// ```rust
    /// use rustica::datatypes::id::Id;
    /// use rustica::traits::functor::Functor;
    /// use rustica::traits::identity::Identity;
    /// 
    /// let x: Id<i32> = Id::new(5);
    /// 
    /// // Map a simple function
    /// let doubled = x.fmap(&|n| n * 2);
    /// assert_eq!(*doubled.value(), 10);
    /// 
    /// // Chain multiple transformations
    /// let result = x
    ///     .fmap(&|n| n + 3)       // 5 -> 8
    ///     .fmap(&|n| n.to_string()); // 8 -> "8"
    /// assert_eq!(*result.value(), "8");
    /// ```
    fn fmap<B>(&self, f: &dyn Fn(&Self::Source) -> B) -> Self::Output<B> {
        Id::new(f(&self.value))
    }
}

impl<T> Pure for Id<T> {
    /// Lifts a value into the `Id` context.
    /// 
    /// This is equivalent to `Id::new` but follows the `Pure` trait interface.
    /// 
    /// # Arguments
    /// 
    /// * `x` - The value to lift into `Id` context
    /// 
    /// # Examples
    /// 
    /// ```rust
    /// use rustica::datatypes::id::Id;
    /// use rustica::traits::pure::Pure;
    /// use rustica::traits::identity::Identity;
    /// 
    /// // Lift a value into Id context
    /// let pure_int = Id::<i32>::pure(42);
    /// assert_eq!(*pure_int.value(), 42);
    /// 
    /// // Lift a string into Id context
    /// let pure_str = Id::<&str>::pure("hello");
    /// assert_eq!(*pure_str.value(), "hello");
    /// ```
    fn pure<U>(x: U) -> Self::Output<U> {
        Id::new(x)
    }
}

impl<T> Applicative for Id<T> {
    /// Applies a function wrapped in `Id` to this value.
    /// 
    /// This allows you to apply functions that are themselves wrapped in the `Id` context.
    /// 
    /// # Arguments
    /// 
    /// * `f` - The wrapped function to apply
    /// 
    /// # Examples
    /// 
    /// ```rust
    /// use rustica::datatypes::id::Id;
    /// use rustica::traits::applicative::Applicative;
    /// use rustica::traits::identity::Identity;
    /// 
    /// let x: Id<i32> = Id::new(5);
    /// 
    /// // Create a function wrapped in Id
    /// let add_three: Id<fn(&i32) -> i32> = Id::new(|n| n + 3);
    /// 
    /// // Apply the wrapped function to the wrapped value
    /// let result = x.apply(&add_three);
    /// assert_eq!(*result.value(), 8);
    /// ```
    fn apply<B, F>(&self, f: &Self::Output<F>) -> Self::Output<B>
    where
        F: Fn(&Self::Source) -> B,
    {
        Id::new(f.value()(&self.value))
    }

    /// Combines two `Id` values using a binary function.
    /// 
    /// # Arguments
    /// 
    /// * `b` - The second `Id` value
    /// * `f` - The function to combine the values
    /// 
    /// # Examples
    /// 
    /// ```rust
    /// use rustica::datatypes::id::Id;
    /// use rustica::traits::applicative::Applicative;
    /// use rustica::traits::identity::Identity;
    /// 
    /// let x: Id<i32> = Id::new(5);
    /// let y: Id<i32> = Id::new(3);
    /// 
    /// // Combine two Id values with a binary function
    /// let add = |a: &i32, b: &i32| a + b;
    /// let sum = x.lift2(&y, &add);
    /// assert_eq!(*sum.value(), 8);
    /// 
    /// // Working with different types
    /// let greeting: Id<&str> = Id::new("Hello");
    /// let name: Id<&str> = Id::new("World");
    /// let combine = |a: &&str, b: &&str| format!("{} {}!", *a, *b);
    /// let message = greeting.lift2(&name, &combine);
    /// assert_eq!(*message.value(), "Hello World!");
    /// ```
    fn lift2<B, C>(
        &self,
        b: &Self::Output<B>,
        f: &dyn Fn(&Self::Source, &B) -> C,
    ) -> Self::Output<C> {
        Id::new(f(&self.value, b.value()))
    }

    /// Combines three `Id` values using a ternary function.
    /// 
    /// # Arguments
    /// 
    /// * `b` - The second `Id` value
    /// * `c` - The third `Id` value
    /// * `f` - The function to combine the values
    /// 
    /// # Examples
    /// 
    /// ```rust
    /// use rustica::datatypes::id::Id;
    /// use rustica::traits::applicative::Applicative;
    /// use rustica::traits::identity::Identity;
    /// 
    /// let x: Id<i32> = Id::new(5);
    /// let y: Id<i32> = Id::new(3);
    /// let z: Id<i32> = Id::new(2);
    /// 
    /// // Combine three Id values with a ternary function
    /// let multiply = |a: &i32, b: &i32, c: &i32| a * b * c;
    /// let product = x.lift3(&y, &z, &multiply);
    /// assert_eq!(*product.value(), 30);
    /// 
    /// // Format a string with three values
    /// let first: Id<&str> = Id::new("Hello");
    /// let second: Id<&str> = Id::new("functional");
    /// let third: Id<&str> = Id::new("world");
    /// let format_greeting = |a: &&str, b: &&str, c: &&str| format!("{} {} {}!", *a, *b, *c);
    /// let greeting = first.lift3(&second, &third, &format_greeting);
    /// assert_eq!(*greeting.value(), "Hello functional world!");
    /// ```
    fn lift3<B, C, D>(
        &self,
        b: &Self::Output<B>,
        c: &Self::Output<C>,
        f: &dyn Fn(&Self::Source, &B, &C) -> D,
    ) -> Self::Output<D> {
        Id::new(f(&self.value, b.value(), c.value()))
    }
}

impl<T> Monad for Id<T> {
    /// Binds a monadic function to the wrapped value.
    /// 
    /// This allows for sequencing operations that depend on the result of previous operations.
    /// 
    /// # Arguments
    /// 
    /// * `f` - The monadic function to apply
    /// 
    /// # Examples
    /// 
    /// ```rust
    /// use rustica::datatypes::id::Id;
    /// use rustica::traits::monad::Monad;
    /// use rustica::traits::identity::Identity;
    /// 
    /// let x: Id<i32> = Id::new(5);
    /// 
    /// // Define a monadic function
    /// let add_and_wrap = |n: &i32| Id::new(n + 3);
    /// 
    /// // Bind the monadic function to the Id value
    /// let result = x.bind(&add_and_wrap);
    /// assert_eq!(*result.value(), 8);
    /// 
    /// // Chain multiple bind operations
    /// let result = x
    ///     .bind(&|n| Id::new(n + 3))
    ///     .bind(&|n| Id::new(n * 2));
    /// assert_eq!(*result.value(), 16);
    /// ```
    fn bind<U: Clone>(&self, f: &dyn Fn(&Self::Source) -> Self::Output<U>) -> Self::Output<U> {
        f(&self.value)
    }

    /// Flattens a nested `Id` value.
    /// 
    /// This operation is used to flatten a nested monadic structure, turning `Id<Id<T>>` into `Id<T>`.
    /// 
    /// # Examples
    /// 
    /// ```rust
    /// use rustica::datatypes::id::Id;
    /// use rustica::traits::monad::Monad;
    /// use rustica::traits::identity::Identity;
    /// 
    /// // Create a nested Id value
    /// let nested: Id<Id<i32>> = Id::new(Id::new(42));
    /// 
    /// // Flatten the nested structure
    /// let flattened = nested.join();
    /// assert_eq!(*flattened.value(), 42);
    /// ```
    fn join<U>(&self) -> Self::Output<U>
        where
            Self::Source: Clone + Into<Self::Output<U>> {
        self.value.clone().into()
    }
}