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
//!     let doubled = left_value.fmap_left(|x| x * 2);  // Either::Left(84)
//!     let upper = right_value.fmap_right(|s| s.to_uppercase());  // Either::Right("HELLO")
//!     
//!     // Functor and Monad operations
//!     let right_val: Either<&str, i32> = Either::right(42);
//!     let mapped = right_val.clone().fmap(|x| x * 2);  // Either::Right(84)
//!     let chained = right_val.bind(|x| Either::right(x.to_string()));  // Either::Right("42")
//! }

use crate::traits::alternative::Alternative;
use crate::traits::applicative::Applicative;
use crate::traits::composable::Composable;
use crate::traits::functor::Functor;
use crate::traits::hkt::HKT;
use crate::traits::identity::Identity;
use crate::traits::monad::Monad;
use crate::traits::monad_plus::MonadPlus;
use crate::traits::pure::Pure;
use crate::utils::error_utils;
#[cfg(feature = "develop")]
use quickcheck::{Arbitrary, Gen};

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
///     let doubled = left.fmap_left(|x| x * 2);  // Either::Left(84)
///     let upper = right.fmap_right(|s| s.to_uppercase());  // Either::Right("HELLO")
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
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
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
    pub const fn left(l: L) -> Self {
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
    pub const fn right(r: R) -> Self {
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
    pub const fn is_left(&self) -> bool {
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
    pub const fn is_right(&self) -> bool {
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
    /// let doubled = left.fmap_left(|x| x * 2);
    /// assert_eq!(match doubled { Either::Left(n) => n, _ => 0 }, 84);
    /// ```
    #[inline]
    pub fn fmap_left<T, F>(self, f: F) -> Either<T, R>
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
    /// let upper = right.fmap_right(|s| s.to_uppercase());
    /// assert_eq!(match upper { Either::Right(s) => s, _ => String::new() }, "HELLO");
    /// ```
    #[inline]
    pub fn fmap_right<T, F>(self, f: F) -> Either<L, T>
    where
        F: FnMut(R) -> T,
    {
        match self {
            Either::Left(l) => Either::Left(l),
            Either::Right(r) => Either::Right(std::iter::once(r).map(f).next().unwrap()),
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
        self.into_iter()
            .next()
            .expect("called unwrap_right on Left value")
    }

    /// Returns the contained `Left` value, consuming the `self` value.
    ///
    /// Because this function consumes the original Either, there is no need to clone
    /// the content, making this method more efficient than `unwrap_left`.
    ///
    /// # Panics
    ///
    /// Panics if the value is a `Right`.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::datatypes::either::Either;
    ///
    /// let x: Either<u32, &str> = Either::left(7);
    /// assert_eq!(x.left_value(), 7);
    /// ```
    #[inline]
    pub fn left_value(self) -> L
    where
        Self: Sized,
    {
        match self {
            Either::Left(l) => l,
            Either::Right(_) => panic!("Called left_value on an Either::Right"),
        }
    }

    /// Returns the contained `Right` value, consuming the `self` value.
    ///
    /// Because this function consumes the original Either, there is no need to clone
    /// the content, making this method more efficient than `unwrap_right`.
    ///
    /// # Panics
    ///
    /// Panics if the value is a `Left`.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::datatypes::either::Either;
    ///
    /// let x: Either<u32, &str> = Either::right("hello");
    /// assert_eq!(x.right_value(), "hello");
    /// ```
    #[inline]
    pub fn right_value(self) -> R {
        self.into_iter()
            .next()
            .expect("Called right_value() on a Left value")
    }

    /// Returns a reference to the `Left` value.
    ///
    /// # Panics
    ///
    /// Panics if the value is a `Right`.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::datatypes::either::Either;
    ///
    /// let x: Either<u32, &str> = Either::left(7);
    /// assert_eq!(*x.left_ref(), 7);
    /// ```
    #[inline]
    pub fn left_ref(&self) -> &L {
        match self {
            Either::Left(l) => l,
            Either::Right(_) => panic!("Called left_ref on an Either::Right"),
        }
    }

    /// Returns a reference to the `Right` value.
    ///
    /// # Panics
    ///
    /// Panics if the value is a `Left`.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::datatypes::either::Either;
    ///
    /// let x: Either<u32, &str> = Either::right("hello");
    /// assert_eq!(*x.right_ref(), "hello");
    /// ```
    #[inline]
    pub fn right_ref(&self) -> &R {
        self.into_iter()
            .next()
            .expect("Called right_ref() on a Left value")
    }

    /// Returns the contained `Right` value or a default.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::datatypes::either::Either;
    ///
    /// let right: Either<&str, u32> = Either::right(7);
    /// assert_eq!(right.right_or(42), 7);
    ///
    /// let left: Either<&str, u32> = Either::left("foo");
    /// assert_eq!(left.right_or(42), 42);
    /// ```
    #[inline]
    pub fn right_or(self, default: R) -> R {
        self.into_iter().next().unwrap_or(default)
    }

    /// Returns the contained `Left` value or a default.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::datatypes::either::Either;
    ///
    /// let right: Either<&str, u32> = Either::right(7);
    /// assert_eq!(right.left_or("default"), "default");
    ///
    /// let left: Either<&str, u32> = Either::left("foo");
    /// assert_eq!(left.left_or("default"), "foo");
    /// ```
    #[inline]
    pub fn left_or(self, default: L) -> L {
        match self {
            Either::Left(l) => l,
            Either::Right(_) => default,
        }
    }

    /// Returns the contained `Right` value as an Option.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::datatypes::either::Either;
    ///
    /// let right: Either<&str, u32> = Either::right(7);
    /// assert_eq!(right.right_option(), Some(7));
    ///
    /// let left: Either<&str, u32> = Either::left("foo");
    /// assert_eq!(left.right_option(), None);
    /// ```
    #[inline]
    pub fn right_option(self) -> Option<R> {
        self.into_iter().next()
    }

    /// Converts this `Either` to a `Result`.
    ///
    /// Left becomes `Err` and Right becomes `Ok`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::either::Either;
    ///
    /// let right: Either<&str, i32> = Either::right(42);
    /// assert_eq!(right.to_result(), Ok(42));
    ///
    /// let left: Either<&str, i32> = Either::left("error");
    /// assert_eq!(left.to_result(), Err("error"));
    /// ```
    #[inline]
    pub fn to_result(self) -> Result<R, L> {
        error_utils::either_to_result(self)
    }

    /// Creates an `Either` from a `Result`.
    ///
    /// `Err` becomes `Left` and `Ok` becomes `Right`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::either::Either;
    ///
    /// let ok_result: Result<i32, &str> = Ok(42);
    /// assert_eq!(Either::from_result(ok_result), Either::right(42));
    ///
    /// let err_result: Result<i32, &str> = Err("error");
    /// assert_eq!(Either::from_result(err_result), Either::left("error"));
    /// ```
    #[inline]
    pub fn from_result(result: Result<R, L>) -> Self {
        error_utils::result_to_either(result)
    }

    /// Returns an iterator over the left value, consuming self.
    pub fn left_iter(self) -> EitherLeftIter<L> {
        match self {
            Either::Left(l) => EitherLeftIter { left: Some(l) },
            Either::Right(_) => EitherLeftIter { left: None },
        }
    }

    /// Returns an iterator over a reference to the left value.
    pub fn left_iter_ref(&self) -> EitherLeftIterRef<'_, L> {
        match self {
            Either::Left(ref l) => EitherLeftIterRef { left: Some(l) },
            Either::Right(_) => EitherLeftIterRef { left: None },
        }
    }

    /// Returns an iterator over a mutable reference to the left value.
    pub fn left_iter_mut(&mut self) -> EitherLeftIterMut<'_, L> {
        match self {
            Either::Left(ref mut l) => EitherLeftIterMut { left: Some(l) },
            Either::Right(_) => EitherLeftIterMut { left: None },
        }
    }

    /// Returns the contained `Left` value as an Option.
    pub fn left_option(self) -> Option<L> {
        self.left_iter().next()
    }

    /// Returns a mutable reference to the `Left` value, panicking if not present.
    pub fn left_mut(&mut self) -> &mut L {
        self.left_iter_mut()
            .next()
            .expect("Called left_mut() on a Right value")
    }
}

/// An iterator over the left value of an `Either<L, R>`.
pub struct EitherLeftIter<L> {
    left: Option<L>,
}

impl<L> Iterator for EitherLeftIter<L> {
    type Item = L;
    fn next(&mut self) -> Option<L> {
        self.left.take()
    }
}

/// An iterator over a reference to the left value of an `Either<L, R>`.
pub struct EitherLeftIterRef<'a, L> {
    left: Option<&'a L>,
}

impl<'a, L> Iterator for EitherLeftIterRef<'a, L> {
    type Item = &'a L;
    fn next(&mut self) -> Option<&'a L> {
        self.left.take()
    }
}

/// An iterator over a mutable reference to the left value of an `Either<L, R>`.
pub struct EitherLeftIterMut<'a, L> {
    left: Option<&'a mut L>,
}

impl<'a, L> Iterator for EitherLeftIterMut<'a, L> {
    type Item = &'a mut L;
    fn next(&mut self) -> Option<&'a mut L> {
        self.left.take()
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
    fn apply<B, F>(&self, f: &Self::Output<F>) -> Self::Output<B>
    where
        F: Fn(&Self::Source) -> B,
    {
        match (self, f) {
            (Either::Right(r), Either::Right(func)) => Either::Right(func(r)),
            (Either::Left(l), _) => Either::Left(l.clone()),
            (_, Either::Left(l)) => Either::Left(l.clone()),
        }
    }

    fn lift2<B, C, F>(&self, b: &Self::Output<B>, f: F) -> Self::Output<C>
    where
        F: Fn(&Self::Source, &B) -> C,
    {
        match (self, b) {
            (Either::Right(r), Either::Right(b_val)) => Either::Right(f(r, b_val)),
            (Either::Left(l), _) => Either::Left(l.clone()),
            (_, Either::Left(l)) => Either::Left(l.clone()),
        }
    }

    fn lift3<B, C, D, F>(&self, b: &Self::Output<B>, c: &Self::Output<C>, f: F) -> Self::Output<D>
    where
        F: Fn(&Self::Source, &B, &C) -> D,
    {
        match (self, b, c) {
            (Either::Right(r), Either::Right(b_val), Either::Right(c_val)) => {
                Either::Right(f(r, b_val, c_val))
            },
            (Either::Left(l), _, _) => Either::Left(l.clone()),
            (_, Either::Left(l), _) => Either::Left(l.clone()),
            (_, _, Either::Left(l)) => Either::Left(l.clone()),
        }
    }

    fn apply_owned<B, F>(self, f: Self::Output<F>) -> Self::Output<B>
    where
        F: FnOnce(Self::Source) -> B,
        Self: Sized,
    {
        match (self, f) {
            (Either::Right(x), Either::Right(f)) => Either::Right(f(x)),
            (Either::Left(l), _) => Either::Left(l),
            (_, Either::Left(l)) => Either::Left(l),
        }
    }

    fn lift2_owned<B, C, F>(self, b: Self::Output<B>, f: F) -> Self::Output<C>
    where
        F: FnOnce(Self::Source, B) -> C,
        Self: Sized,
    {
        match (self, b) {
            (Either::Right(x), Either::Right(y)) => Either::Right(f(x, y)),
            (Either::Left(l), _) => Either::Left(l),
            (_, Either::Left(l)) => Either::Left(l),
        }
    }

    fn lift3_owned<B, C, D, F>(
        self, b: Self::Output<B>, c: Self::Output<C>, f: F,
    ) -> Self::Output<D>
    where
        F: FnOnce(Self::Source, B, C) -> D,
        Self: Sized,
    {
        match (self, b, c) {
            (Either::Right(x), Either::Right(y), Either::Right(z)) => Either::Right(f(x, y, z)),
            (Either::Left(l), _, _) => Either::Left(l),
            (_, Either::Left(l), _) => Either::Left(l),
            (_, _, Either::Left(l)) => Either::Left(l),
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
        F: FnOnce(Self::Source) -> Self::Output<U>,
        Self: Sized,
    {
        match self {
            Either::Left(l) => Either::Left(l),
            Either::Right(r) => f(r),
        }
    }

    #[inline]
    fn join_owned<U>(self) -> Self::Output<U>
    where
        Self::Source: Into<Self::Output<U>>,
        Self: Sized,
    {
        match self {
            Either::Left(l) => Either::Left(l),
            Either::Right(r) => r.into(),
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
        Self::Output<A>: Identity,
    {
        Either::Right(value)
    }

    #[inline]
    fn into_value(self) -> Self::Source {
        match self {
            Either::Left(_) => panic!("Called into_value on an Either::Left"),
            Either::Right(r) => r,
        }
    }
}

impl<L, R> Composable for Either<L, R> {}

impl<L: Default + Clone, R: Clone> MonadPlus for Either<L, R> {
    fn mzero<U: Clone>() -> Self::Output<U> {
        Either::Left(L::default().clone())
    }

    fn mplus(&self, other: &Self) -> Self {
        match (self, other) {
            (Either::Right(_), _) => self.clone(),
            (Either::Left(_), Either::Right(_)) => other.clone(),
            (Either::Left(_), Either::Left(_)) => self.clone(),
        }
    }

    fn mplus_owned(self, other: Self) -> Self
    where
        Self: Sized,
    {
        match (&self, &other) {
            (Either::Right(_), _) => self,
            (Either::Left(_), Either::Right(_)) => other,
            (Either::Left(_), Either::Left(_)) => self,
        }
    }
}

impl<L: Default + Clone, R: Clone> Alternative for Either<L, R> {
    #[inline]
    fn empty_alt<B>() -> Self::Output<B> {
        Either::Left(L::default())
    }

    #[inline]
    fn alt(&self, other: &Self) -> Self {
        match self {
            Either::Right(_) => self.clone(),
            Either::Left(_) => other.clone(),
        }
    }

    fn guard(condition: bool) -> Self::Output<()> {
        if condition {
            Either::Right(())
        } else {
            Either::Left(L::default())
        }
    }

    #[inline]
    fn many(&self) -> Self::Output<Vec<Self::Source>>
    where
        Self::Source: Clone,
    {
        match self {
            Either::Right(x) => Either::Right(vec![x.clone()]),
            Either::Left(_) => Either::Left(L::default()),
        }
    }
}

// Iterator support for Either
/// An iterator over the right value of an `Either<L, R>`.
pub struct EitherIter<R> {
    inner: Option<R>,
}

impl<L, R> IntoIterator for Either<L, R> {
    type Item = R;
    type IntoIter = EitherIter<R>;
    /// Converts the `Either` into an iterator over the right value.
    ///
    /// If the value is `Right`, yields the contained value. If `Left`, yields nothing.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::either::Either;
    /// let e: Either<&str, i32> = Either::right(42);
    /// let v: Vec<_> = e.into_iter().collect();
    /// assert_eq!(v, vec![42]);
    /// let e: Either<&str, i32> = Either::left("err");
    /// let v: Vec<_> = e.into_iter().collect();
    /// assert!(v.is_empty());
    /// ```
    fn into_iter(self) -> Self::IntoIter {
        match self {
            Either::Right(r) => EitherIter { inner: Some(r) },
            Either::Left(_) => EitherIter { inner: None },
        }
    }
}

impl<R> Iterator for EitherIter<R> {
    type Item = R;
    fn next(&mut self) -> Option<R> {
        self.inner.take()
    }
}

/// An iterator over a reference to the right value of an `Either<L, R>`.
pub struct EitherIterRef<'a, R> {
    inner: Option<&'a R>,
}

impl<'a, L, R> IntoIterator for &'a Either<L, R> {
    type Item = &'a R;
    type IntoIter = EitherIterRef<'a, R>;
    /// Converts a reference to `Either` into an iterator over a reference to the right value.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::either::Either;
    /// let e: Either<&str, i32> = Either::right(42);
    /// let v: Vec<_> = (&e).into_iter().collect();
    /// assert_eq!(v, vec![&42]);
    /// let e: Either<&str, i32> = Either::left("err");
    /// let v: Vec<_> = (&e).into_iter().collect::<Vec<_>>();
    /// assert!(v.is_empty());
    /// ```
    fn into_iter(self) -> Self::IntoIter {
        match self {
            Either::Right(r) => EitherIterRef { inner: Some(r) },
            Either::Left(_) => EitherIterRef { inner: None },
        }
    }
}

impl<'a, R> Iterator for EitherIterRef<'a, R> {
    type Item = &'a R;
    fn next(&mut self) -> Option<&'a R> {
        self.inner.take()
    }
}

/// An iterator over a mutable reference to the right value of an `Either<L, R>`.
pub struct EitherIterMut<'a, R> {
    inner: Option<&'a mut R>,
}

impl<'a, L, R> IntoIterator for &'a mut Either<L, R> {
    type Item = &'a mut R;
    type IntoIter = EitherIterMut<'a, R>;
    /// Converts a mutable reference to `Either` into an iterator over a mutable reference to the right value.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::either::Either;
    /// let mut e: Either<&str, i32> = Either::right(42);
    /// for v in &mut e {
    ///     *v += 1;
    /// }
    /// assert_eq!(e, Either::right(43));
    /// ```
    fn into_iter(self) -> Self::IntoIter {
        match self {
            Either::Right(r) => EitherIterMut { inner: Some(r) },
            Either::Left(_) => EitherIterMut { inner: None },
        }
    }
}

impl<'a, R> Iterator for EitherIterMut<'a, R> {
    type Item = &'a mut R;
    fn next(&mut self) -> Option<&'a mut R> {
        self.inner.take()
    }
}

#[cfg(feature = "develop")]
impl<L, R> Arbitrary for Either<L, R>
where
    L: Arbitrary,
    R: Arbitrary,
{
    fn arbitrary(g: &mut Gen) -> Self {
        let left = L::arbitrary(g);
        let right = R::arbitrary(g);
        if bool::arbitrary(g) {
            Either::Left(left)
        } else {
            Either::Right(right)
        }
    }
}
