use std::fmt::Debug;

use crate::traits::hkt::{HKT, TypeConstraints};
use crate::traits::functor::Functor;
use crate::traits::applicative::Applicative;
use crate::traits::monad::Monad;
use crate::traits::pure::Pure;
use crate::traits::bifunctor::Bifunctor;
use crate::traits::category::Category;
use crate::traits::arrow::Arrow;
use crate::traits::composable::Composable;
use crate::traits::identity::Identity;
use crate::fntype::{FnTrait, FnType};

/// A type that represents one of two possible values.
/// 
/// # Type Parameters
/// * `L` - The left value type
/// * `R` - The right value type
/// 
/// # Laws
/// An `Either` instance must satisfy these laws in addition to the standard Monad laws:
/// 1. Left Identity: For any value `x`,
///    `Either::Left(x).map_right(f) = Either::Left(x)`
/// 2. Right Identity: For any value `x`,
///    `Either::Right(x).map_left(f) = Either::Right(x)`
/// 3. Left Absorption: For any value `x` and function `f`,
///    `Either::Left(x).bind(f) = Either::Left(x)`
/// 4. Right Distribution: For any value `x` and function `f`,
///    `Either::Right(x).bind(f) = f(x)`
/// 
/// # Examples
/// ```
/// use rustica::datatypes::either::Either;
/// use rustica::fntype::{FnType, FnTrait};
/// 
/// let left: Either<i32, String> = Either::Left(42);
/// let right: Either<i32, String> = Either::Right("Hello".to_string());
/// 
/// assert!(left.is_left());
/// assert!(right.is_right());
/// 
/// let mapped_left = left.map_left(FnType::new(|x| x + 1));
/// assert_eq!(mapped_left.unwrap_left(), 43);
/// 
/// let mapped_right = right.map_right(FnType::new(|s: String| s.len()));
/// assert_eq!(mapped_right.unwrap_right(), 5);
/// ```
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Either<L, R>
where
    L: TypeConstraints,
    R: TypeConstraints,
{
    /// The left variant of the `Either` type.
    Left(L),
    /// The right variant of the `Either` type.
    Right(R),
}

impl<L, R> Default for Either<L, R>
where
    L: TypeConstraints,
    R: TypeConstraints,
{
    fn default() -> Self {
        Either::Right(R::default())
    }
}

impl<L, R> Either<L, R>
where
    L: TypeConstraints,
    R: TypeConstraints,
{
    /// Constructs an `Either` instance from a `Left` value.
    ///
    /// # Parameters
    /// * `l` - The value to be contained in the `Left` variant
    ///
    /// # Returns
    /// A new `Either` instance containing the given value as a `Left` variant
    pub fn make_left(l: L) -> Self {
        Either::Left(l)
    }

    /// Constructs an `Either` instance from a `Right` value.
    ///
    /// # Parameters
    /// * `r` - The value to be contained in the `Right` variant
    ///
    /// # Returns
    /// A new `Either` instance containing the given value as a `Right` variant
    pub fn make_right(r: R) -> Self {
        Either::Right(r)
    }

    /// Returns `true` if the `Either` instance is a `Left` variant.
    pub fn is_left(&self) -> bool {
        matches!(self, Either::Left(_))
    }

    /// Returns `true` if the `Either` instance is a `Right` variant.
    pub fn is_right(&self) -> bool {
        matches!(self, Either::Right(_))
    }

    /// Maps a function over the `Left` value of an `Either`.
    ///
    /// If this `Either` is a `Left`, it applies the function to the contained value.
    /// If it's a `Right`, it returns the `Either` unchanged.
    ///
    /// # Type Parameters
    /// * `T`: The new type for the `Left` variant after mapping.
    /// * `F`: The type of the function to apply.
    ///
    /// # Parameters
    /// * `self`: The `Either` to map over.
    /// * `f`: The function to apply to the `Left` value.
    ///
    /// # Returns
    /// A new `Either` with the function applied to the `Left` value if it was a `Left`,
    /// or the original `Right` value if it was a `Right`.
    pub fn map_left<T, F>(self, f: F) -> Either<T, R>
    where
        T: TypeConstraints,
        F: FnTrait<L, T>,
    {
        match self {
            Either::Left(l) => Either::Left(f.call(l)),
            Either::Right(r) => Either::Right(r),
        }
    }

    /// Maps a function over the `Right` value of an `Either`.
    ///
    /// If this `Either` is a `Right`, it applies the function to the contained value.
    /// If it's a `Left`, it returns the `Either` unchanged.
    ///
    /// # Type Parameters
    /// * `T`: The new type for the `Right` variant after mapping.
    /// * `F`: The type of the function to apply.
    ///
    /// # Parameters
    /// * `self`: The `Either` to map over.
    /// * `f`: The function to apply to the `Right` value.
    ///
    /// # Returns
    /// A new `Either` with the function applied to the `Right` value if it was a `Right`,
    /// or the original `Left` value if it was a `Left`.
    pub fn map_right<T, F>(self, f: F) -> Either<L, T>
    where
        T: TypeConstraints,
        F: FnTrait<R, T>,
    {
        match self {
            Either::Left(l) => Either::Left(l),
            Either::Right(r) => Either::Right(f.call(r)),
        }
    }

    /// Unwraps the `Left` value from an `Either`.
    ///
    /// # Returns
    /// The contained `Left` value.
    ///
    /// # Panics
    /// Panics if the `Either` is a `Right` variant.
    ///
    /// # Examples
    /// ```
    /// use rustica::datatypes::either::Either;
    ///
    /// let left: Either<i32, String> = Either::Left(42);
    /// assert_eq!(left.unwrap_left(), 42);
    ///
    /// let right: Either<i32, String> = Either::Right("Hello".to_string());
    /// // The following line would panic:
    /// // right.unwrap_left();
    /// ```
    pub fn unwrap_left(self) -> L
    where
        L: TypeConstraints,
    {
        match self {
            Either::Left(l) => l,
            Either::Right(_) => panic!("Called `unwrap_left` on a `Right` value"),
        }
    }

    /// Unwraps the `Right` value from an `Either`.
    ///
    /// # Returns
    /// The contained `Right` value.
    ///
    /// # Panics
    /// Panics if the `Either` is a `Left` variant.
    ///
    /// # Examples
    /// ```
    /// use rustica::datatypes::either::Either;
    ///
    /// let right: Either<i32, String> = Either::Right("Hello".to_string());
    /// assert_eq!(right.unwrap_right(), "Hello");
    ///
    /// let left: Either<i32, String> = Either::Left(42);
    /// // The following line would panic:
    /// // left.unwrap_right();
    /// ```
    pub fn unwrap_right(self) -> R
    where
        R: TypeConstraints,
    {
        match self {
            Either::Left(_) => panic!("Called `unwrap_right` on a `Left` value"),
            Either::Right(r) => r,
        }
    }
}

impl<L: TypeConstraints, R: TypeConstraints> HKT for Either<L, R> {
    type Output<T> = Either<L, T> where T: TypeConstraints;
}

impl<L: TypeConstraints, R: TypeConstraints> Pure<R> for Either<L, R> {
    fn pure(value: R) -> Self::Output<R> {
        Either::Right(value)
    }
}

impl<L: TypeConstraints, R: TypeConstraints> Functor<R> for Either<L, R> {
    fn fmap<T: TypeConstraints, F: FnTrait<R, T>>(self, f: F) -> Either<L, T> {
        match self {
            Either::Left(l) => Either::Left(l),
            Either::Right(r) => Either::Right(f.call(r)),
        }
    }
}

impl<L: TypeConstraints, R: TypeConstraints> Applicative<R> for Either<L, R> {
    fn apply<T: TypeConstraints, F: FnTrait<R, T>>(self, g: Either<L, F>) -> Either<L, T> {
        match (self, g) {
            (Either::Right(x), Either::Right(f)) => Either::Right(f.call(x)),
            (Either::Left(l), _) => Either::Left(l),
            (_, Either::Left(l)) => Either::Left(l),
        }
    }

    fn lift2<T, U, F>(self, b: Either<L, T>, f: F) -> Either<L, U>
    where
        T: TypeConstraints,
        U: TypeConstraints,
        F: FnTrait<(R, T), U>,
    {
        match (self, b) {
            (Either::Right(x), Either::Right(y)) => Either::Right(f.call((x, y))),
            (Either::Left(l), _) => Either::Left(l),
            (_, Either::Left(l)) => Either::Left(l),
        }
    }

    fn lift3<T, U, V, F>(
        self,
        b: Either<L, T>,
        c: Either<L, U>,
        f: F,
    ) -> Either<L, V>
    where
        T: TypeConstraints,
        U: TypeConstraints,
        V: TypeConstraints,
        F: FnTrait<(R, T, U), V>,
    {
        match (self, b, c) {
            (Either::Right(x), Either::Right(y), Either::Right(z)) => Either::Right(f.call((x, y, z))),
            (Either::Left(l), _, _) => Either::Left(l),
            (_, Either::Left(l), _) => Either::Left(l),
            (_, _, Either::Left(l)) => Either::Left(l),
        }
    }
}

impl<L, T> Monad<T> for Either<L, T>
where
    L: TypeConstraints,
    T: TypeConstraints,
{
    fn bind<U: TypeConstraints, F: FnTrait<T, Self::Output<U>>>(self, f: F) -> Self::Output<U> {
        match self {
            Either::Left(l) => Either::Left(l),
            Either::Right(r) => f.call(r),
        }
    }

    fn join<U>(self) -> Self::Output<U>
    where
        U: TypeConstraints,
        T: Into<Self::Output<U>>,
    {
        match self {
            Either::Left(l) => Either::Left(l),
            Either::Right(r) => r.into(),
        }
    }
}

impl<L, R> Bifunctor<L, R> for Either<L, R>
where
    L: TypeConstraints,
    R: TypeConstraints,
{
    type Output<T, U> = Either<T, U> where 
        T: TypeConstraints,
        U: TypeConstraints;

    fn first<T: TypeConstraints, F: FnTrait<L, T>>(self, f: F) -> Self::Output<T, R> {
        match self {
            Either::Left(l) => Either::Left(f.call(l)),
            Either::Right(r) => Either::Right(r),
        }
    }

    fn second<T: TypeConstraints, F: FnTrait<R, T>>(self, f: F) -> Self::Output<L, T> {
        match self {
            Either::Left(l) => Either::Left(l),
            Either::Right(r) => Either::Right(f.call(r)),
        }
    }

    fn bimap<T, U, F, G>(self, f: F, g: G) -> Self::Output<T, U>
    where
        T: TypeConstraints,
        U: TypeConstraints,
        F: FnTrait<L, T>,
        G: FnTrait<R, U>,
    {
        match self {
            Either::Left(l) => Either::Left(f.call(l)),
            Either::Right(r) => Either::Right(g.call(r)),
        }
    }
}

impl<L, R> Category for Either<L, R>
where
    L: TypeConstraints,
    R: TypeConstraints,
{
    type Morphism<B, C> = FnType<B, C>
    where
        B: TypeConstraints,
        C: TypeConstraints;
}

impl<L: TypeConstraints, R: TypeConstraints> Arrow for Either<L, R> {}

impl<L: TypeConstraints, R: TypeConstraints> Identity for Either<L, R> {}

impl<L: TypeConstraints, R: TypeConstraints> Composable for Either<L, R> {}