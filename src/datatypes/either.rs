//! # Either Datatype
//! 
//! The `Either` datatype represents values with two possibilities: a value of type `L` (Left) or a value of type `R` (Right).
//! It is a fundamental functional programming construct that is similar to Rust's built-in `Result<T, E>` but without the 
//! semantic meaning of success/failure.
//! 
//! ## Functional Programming Context
//! 
//! In functional programming, the `Either` type is commonly used for:
//! 
//! - Representing computations that can produce one of two different types of values
//! - Handling branching logic in a composable way
//! - Implementing error handling without the success/failure semantics of `Result`
//! - Building more complex data structures and control flow mechanisms
//! 
//! Similar constructs in other functional programming languages include:
//! 
//! - `Either` in Haskell
//! - `Either` in Scala
//! - `Either` in fp-ts (TypeScript)
//! - `Either` in Arrow (Kotlin)
//! 
//! ## Type Class Implementations
//! 
//! The `Either` type implements several important functional programming abstractions:
//! 
//! - `Functor`: Maps over the right value with `fmap`
//! - `Applicative`: Applies functions wrapped in `Either` to values wrapped in `Either`
//! - `Monad`: Chains computations that may produce either left or right values
//! - `Pure`: Creates an `Either` containing a right value
//! - `Identity`: Accesses the right value when present
//! - `Composable`: Composes functions that work with `Either`
//! - `Transform`: Transforms the right value with `transform` and `transform_ref`
//! - `TransformExt`: Provides additional transformation methods for `Either`
//! 
//! ## Basic Usage
//! 
//! ```rust
//! use rustica::datatypes::either::Either;
//! use rustica::prelude::*;
//! 
//! fn example() {
//!     // Create Either values
//!     let left_value: Either<i32, &str> = Either::left(42);
//!     let right_value: Either<i32, &str> = Either::right("hello");
//!     
//!     // Pattern matching
//!     match left_value {
//!         Either::Left(n) => println!("Got left value: {}", n),
//!         Either::Right(s) => println!("Got right value: {}", s),
//!     }
//!     
//!     // Transform values using map_left and map_right
//!     let doubled = left_value.clone().map_left(|x| x * 2);  // Either::Left(84)
//!     let upper = right_value.map_right(|s| s.to_uppercase());  // Either::Right("HELLO")
//!     
//!     // Functor and Monad operations
//!     let right_val: Either<&str, i32> = Either::right(42);
//!     let mapped = right_val.clone().fmap(|x| x * 2);  // Either::Right(84)
//!     let chained = right_val.bind(|x| Either::right(x.to_string()));  // Either::Right("42")
//! }

use crate::traits::hkt::HKT;
use crate::traits::applicative::Applicative;
use crate::traits::monad::Monad;
use crate::traits::composable::Composable;
use crate::traits::identity::Identity;
use crate::traits::pure::Pure;
use crate::traits::functor::Functor;

/// The `Either` type represents values with two possibilities: a value of type `L` or a value of type `R`.
/// This is similar to `Result<T, E>` but without the semantic meaning of success/failure.
///
/// # Type Parameters
///
/// * `L`: The type of the left value
/// * `R`: The type of the right value
///
/// # Examples
///
/// ```rust
/// use rustica::datatypes::either::Either;
/// use rustica::prelude::*;
///
/// fn example() {
///     // Create Either values
///     let left: Either<i32, &str> = Either::left(42);
///     let right: Either<i32, &str> = Either::right("hello");
///
///     // Transform values using map_left and map_right
///     let doubled = left.clone().map_left(|x| x * 2);  // Either::Left(84)
///     let upper = right.map_right(|s| s.to_uppercase());  // Either::Right("HELLO")
///
///     // Pattern matching
///     match left {
///         Either::Left(n) => println!("Got left value: {}", n),
///         Either::Right(s) => println!("Got right value: {}", s),
///     }
/// }
/// ```
///
/// # Trait Implementations
///
/// `Either` implements several important traits:
///
/// * `HKT` (Higher Kinded Type): Allows type-level programming with `Either`
/// * `Functor`: Map over the right value with `fmap`
/// * `Applicative`: Apply functions wrapped in `Either` to values in `Either`
/// * `Monad`: Chain computations that may produce either left or right values
/// * `Pure`: Create an `Either` containing a right value
/// * `Identity`: Access the right value when present
/// * `Composable`: Compose functions that work with `Either`
/// * `Transform`: Transforms the right value with `transform` and `transform_ref`
/// * `TransformExt`: Provides additional transformation methods for `Either`
#[derive(Clone)]
pub enum Either<L, R> {
    /// Contains a value of type `L`
    Left(L),
    /// Contains a value of type `R`
    Right(R),
}

impl<L, R> Either<L, R> {
    /// Creates a new `Either::Left` containing the given value.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::either::Either;
    ///
    /// let left: Either<i32, &str> = Either::left(42);
    /// ```
    #[inline]
    pub fn left(l: L) -> Self {
        Either::Left(l)
    }

    /// Creates a new `Either::Right` containing the given value.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::either::Either;
    ///
    /// let right: Either<i32, &str> = Either::right("hello");
    /// ```
    #[inline]
    pub fn right(r: R) -> Self {
        Either::Right(r)
    }

    /// Returns `true` if this is a `Left` value.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::either::Either;
    ///
    /// let left: Either<i32, &str> = Either::left(42);
    /// assert!(left.is_left());
    /// ```
    #[inline]
    pub fn is_left(&self) -> bool {
        matches!(self, Either::Left(_))
    }

    /// Returns `true` if this is a `Right` value.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::either::Either;
    ///
    /// let right: Either<i32, &str> = Either::right("hello");
    /// assert!(right.is_right());
    /// ```
    #[inline]
    pub fn is_right(&self) -> bool {
        matches!(self, Either::Right(_))
    }

    /// Maps a function over the left value, leaving a right value unchanged.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::either::Either;
    ///
    /// let left: Either<i32, &str> = Either::left(42);
    /// let doubled = left.map_left(|x| x * 2);
    /// assert_eq!(match doubled { Either::Left(n) => n, _ => 0 }, 84);
    /// ```
    #[inline]
    pub fn map_left<T, F>(self, f: F) -> Either<T, R>
    where
        F: Fn(L) -> T,
    {
        match self {
            Either::Left(l) => Either::Left(f(l)),
            Either::Right(r) => Either::Right(r),
        }
    }

    /// Maps a function over the right value, leaving a left value unchanged.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::either::Either;
    ///
    /// let right: Either<i32, &str> = Either::right("hello");
    /// let upper = right.map_right(|s| s.to_uppercase());
    /// assert_eq!(match upper { Either::Right(s) => s, _ => String::new() }, "HELLO");
    /// ```
    #[inline]
    pub fn map_right<T, F>(self, f: F) -> Either<L, T>
    where
        F: Fn(&R) -> T,
    {
        match self {
            Either::Left(l) => Either::Left(l),
            Either::Right(r) => Either::Right(f(&r)),
        }
    }

    /// Extracts the left value, panicking if this is a `Right`.
    ///
    /// # Panics
    ///
    /// Panics if called on a `Right` value.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::either::Either;
    ///
    /// let left: Either<i32, &str> = Either::left(42);
    /// assert_eq!(left.unwrap_left(), 42);
    /// ```
    #[inline]
    pub fn unwrap_left(self) -> L {
        match self {
            Either::Left(l) => l,
            Either::Right(_) => panic!("called unwrap_left on Right value"),
        }
    }

    /// Extracts the right value, panicking if this is a `Left`.
    ///
    /// # Panics
    ///
    /// Panics if called on a `Left` value.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::either::Either;
    ///
    /// let right: Either<i32, &str> = Either::right("hello");
    /// assert_eq!(right.unwrap_right(), "hello");
    /// ```
    #[inline]
    pub fn unwrap_right(self) -> R {
        match self {
            Either::Left(_) => panic!("called unwrap_right on Left value"),
            Either::Right(r) => r,
        }
    }
}

impl<L, R> HKT for Either<L, R> {
    type Source = R;
    type Output<T> = Either<L, T>;
}

impl<L: Clone, R: Clone> Functor for Either<L, R> {
    #[inline]
    fn fmap<B, F>(&self, f: F) -> Self::Output<B>
    where
        F: Fn(&Self::Source) -> B,
    {
        match self {
            Either::Left(l) => Either::Left(l.clone()),
            Either::Right(r) => Either::Right(f(r)),
        }
    }

    #[inline]
    fn fmap_owned<B, F>(self, f: F) -> Self::Output<B>
    where
        F: Fn(Self::Source) -> B,
    {
        match self {
            Either::Left(l) => Either::Left(l),
            Either::Right(r) => Either::Right(f(r)),
        }
    }
}

impl<L, R> Pure for Either<L, R> {
    #[inline]
    fn pure<T: Clone>(value: &T) -> Self::Output<T> {
        Either::Right(value.clone())
    }
}

impl<L: Clone, R: Clone> Applicative for Either<L, R> {
    #[inline]
    fn apply<B, F>(&self, f: &Self::Output<F>) -> Self::Output<B>
    where
        F: Fn(&Self::Source) -> B,
    {
        match (self, f) {
            (Either::Right(x), Either::Right(f)) => Either::Right(f(x)),
            (Either::Left(l), _) => Either::Left(l.clone()),
            (_, Either::Left(l)) => Either::Left(l.clone()),
        }
    }

    #[inline]
    fn lift2<B, C, F>(&self, b: &Self::Output<B>, f: F) -> Self::Output<C>
    where
        F: Fn(&Self::Source, &B) -> C,
    {
        match (self, b) {
            (Either::Right(x), Either::Right(y)) => Either::Right(f(x, y)),
            (Either::Left(l), _) => Either::Left(l.clone()),
            (_, Either::Left(l)) => Either::Left(l.clone()),
        }
    }

    #[inline]
    fn lift3<B, C, D, F>(&self, b: &Self::Output<B>, c: &Self::Output<C>, f: F) -> Self::Output<D>
    where
        F: Fn(&Self::Source, &B, &C) -> D,
    {
        match (self, b, c) {
            (Either::Right(x), Either::Right(y), Either::Right(z)) => Either::Right(f(x, y, z)),
            (Either::Left(l), _, _) => Either::Left(l.clone()),
            (_, Either::Left(l), _) => Either::Left(l.clone()),
            (_, _, Either::Left(l)) => Either::Left(l.clone()),
        }
    }

    #[inline]
    fn apply_owned<B, F>(self, f: Self::Output<F>) -> Self::Output<B>
    where
        F: Fn(Self::Source) -> B,
        Self: Sized
    {
        match (self, f) {
            (Either::Right(x), Either::Right(f)) => Either::Right(f(x)),
            (Either::Left(l), _) => Either::Left(l.clone()),
            (_, Either::Left(l)) => Either::Left(l.clone()),
        }
    }

    #[inline]
    fn lift2_owned<B, C, F>(
            self,
            b: Self::Output<B>,
            f: F,
        ) -> Self::Output<C>
    where
        F: Fn(Self::Source, B) -> C,
        Self: Sized,
        B: Clone
    {
        match (self, b) {
            (Either::Right(x), Either::Right(y)) => Either::Right(f(x, y)),
            (Either::Left(l), _) => Either::Left(l.clone()),
            (_, Either::Left(l)) => Either::Left(l.clone()),
        }
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
            C: Clone 
    {
        match (self, b, c) {
            (Either::Right(x), Either::Right(y), Either::Right(z)) => Either::Right(f(x, y, z)),
            (Either::Left(l), _, _) => Either::Left(l.clone()),
            (_, Either::Left(l), _) => Either::Left(l.clone()),
            (_, _, Either::Left(l)) => Either::Left(l.clone()),
        }
    }
}

impl<L: Clone, R: Clone> Monad for Either<L, R> {
    #[inline]
    fn bind<B, F>(&self, f: F) -> Self::Output<B>
    where
        F: Fn(&Self::Source) -> Self::Output<B>,
    {
        match self {
            Either::Left(l) => Either::Left(l.clone()),
            Either::Right(r) => f(r),
        }
    }

    #[inline]
    fn join<B>(&self) -> Self::Output<B>
    where
        Self::Source: Into<Self::Output<B>>,
    {
        match self {
            Either::Left(l) => Either::Left(l.clone()),
            Either::Right(r) => r.clone().into(),
        }
    }

    #[inline]
    fn bind_owned<U, F>(self, f: F) -> Self::Output<U>
    where
        F: Fn(Self::Source) -> Self::Output<U>,
        U: Clone,
        Self: Sized
    {
        match self {
            Either::Left(l) => Either::Left(l.clone()),
            Either::Right(r) => f(r),
        }
    }

    #[inline]
    fn join_owned<U>(self) -> Self::Output<U>
    where
        Self::Source: Into<Self::Output<U>>,
        U: Clone,
        Self: Sized
    {
        match self {
            Either::Left(l) => Either::Left(l.clone()),
            Either::Right(r) => r.clone().into(),
        }
    }
}

impl<L: Clone, R: Clone> Identity for Either<L, R> {
    #[inline]
    fn value(&self) -> &Self::Source {
        match self {
            Either::Left(_) => panic!("Cannot get value from Left variant"),
            Either::Right(r) => r,
        }
    }

    #[inline]
    fn pure_identity<A>(value: A) -> Self::Output<A>
        where
            Self::Output<A>: Identity
        {
            Either::Right(value.into())
    }

    #[inline]
    fn into_value(self) -> Self::Source {
        match self {
            Either::Left(_) => panic!("Called into_value on an Either::Left"),
            Either::Right(r) => r,
        }
    }
}

impl<L, R> Composable for Either<L, R> {
    #[inline]
    fn compose<T, U, F, G>(f: F, g: G) -> impl Fn(Self::Source) -> U
    where
        F: Fn(Self::Source) -> T,
        G: Fn(T) -> U,
    {
        move |x| g(f(x))
    }
}