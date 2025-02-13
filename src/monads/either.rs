use std::fmt::Debug;

use crate::category::hkt::{HKT, ReturnTypeConstraints};
use crate::category::functor::Functor;
use crate::category::applicative::Applicative;
use crate::category::monad::Monad;
use crate::category::pure::Pure;
use crate::category::bifunctor::Bifunctor;
use crate::category::category::Category;
use crate::category::arrow::Arrow;
use crate::category::composable::Composable;
use crate::category::identity::Identity;
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
/// use rustica::monads::either::Either;
/// 
/// let left_value: Either<i32, i32> = Either::Left(42);
/// let right_value: Either<i32, i32> = Either::Right(42);
/// 
/// assert!(left_value.is_left());
/// assert!(right_value.is_right());
/// 
/// assert_eq!(left_value.unwrap_left(), 42);
/// assert_eq!(right_value.unwrap_right(), 42);
/// ```
#[derive(Debug, Clone)]
pub enum Either<L, R>
where
    L: ReturnTypeConstraints,
    R: ReturnTypeConstraints,
{
    /// The left value
    Left(L),
    /// The right value
    Right(R),
}

impl<L, R> Either<L, R>
where
    L: ReturnTypeConstraints,
    R: ReturnTypeConstraints,
{
    /// Returns true if this is a Left value.
    /// 
    /// Returns
    /// * `bool` - True if this is a Left value, false otherwise.
    pub fn is_left(&self) -> bool {
        matches!(self, Either::Left(_))
    }

    /// Returns true if this is a Right value.
    /// 
    /// Returns
    /// * `bool` - True if this is a Right value, false otherwise.
    pub fn is_right(&self) -> bool {
        matches!(self, Either::Right(_))
    }

    /// Maps a function over the left value.
    /// 
    /// # Type Parameters
    /// * `T` - The type of the left value.
    /// * `F` - The type of the function.
    /// 
    /// Returns
    /// * `Either<T, R>` - The new `Either` value.
    ///
    /// # Examples
    /// ```
    /// use rustica::monads::either::Either;
    /// use rustica::fntype::FnType;
    /// 
    /// let left_value: Either<i32, i32> = Either::Left(42);
    /// let mapped_left = left_value.map_left(FnType::new(|x| x + 1));
    /// assert_eq!(mapped_left.unwrap_left(), 43);
    /// ```
    pub fn map_left<T, F>(self, f: F) -> Either<T, R>
    where
        T: ReturnTypeConstraints,
        F: FnTrait<L, T>,
    {
        match self {
            Either::Left(l) => Either::Left(f.call(l)),
            Either::Right(r) => Either::Right(r),
        }
    }

    /// Maps a function over the right value.
    ///
    /// # Type Parameters
    /// * `T` - The type of the right value.
    /// * `F` - The type of the function.
    ///
    /// Returns
    /// * `Either<L, T>` - The new `Either` value.
    ///
    /// # Examples
    /// ```
    /// use rustica::monads::either::Either;
    /// use rustica::fntype::FnType;
    /// 
    /// let right_value: Either<i32, i32> = Either::Right(42);
    /// let mapped_right = right_value.map_right(FnType::new(|x| x + 1));
    /// assert_eq!(mapped_right.unwrap_right(), 43);
    /// ```
    pub fn map_right<T, F>(self, f: F) -> Either<L, T>
    where
        T: ReturnTypeConstraints,
        F: FnTrait<R, T>,
    {
        match self {
            Either::Left(l) => Either::Left(l),
            Either::Right(r) => Either::Right(f.call(r)),
        }
    }

    /// Unwraps the left value, panicking if this is a Right value.
    /// 
    /// # Type Parameters
    /// * `L` - The type of the left value.
    ///
    /// Returns
    /// * `L` - The left value.
    ///
    /// # Panics
    /// * If this is a Right value, this function will panic.
    pub fn unwrap_left(self) -> L
    where
        L: ReturnTypeConstraints,
    {
        match self {
            Either::Left(l) => l,
            Either::Right(_) => panic!("Called `unwrap_left` on a `Right` value"),
        }
    }

    /// Unwraps the right value, panicking if this is a Left value.
    /// 
    /// # Type Parameters
    /// * `R` - The type of the right value.
    ///
    /// Returns
    /// * `R` - The right value.
    ///
    /// # Panics
    /// * If this is a Left value, this function will panic.
    pub fn unwrap_right(self) -> R
    where
        R: ReturnTypeConstraints,
    {
        match self {
            Either::Left(_) => panic!("Called `unwrap_right` on a `Left` value"),
            Either::Right(r) => r,
        }
    }
}

impl<L, R> HKT for Either<L, R>
where
    L: ReturnTypeConstraints,
    R: ReturnTypeConstraints,
{
    type Output<T> = Either<L, T> where T: ReturnTypeConstraints;
}

impl<L, R> Pure<R> for Either<L, R>
where
    L: ReturnTypeConstraints,
    R: ReturnTypeConstraints,
{
    /// Returns a Right value with the given value.
    /// 
    /// Returns
    /// * `Either<L, R>` - A Right value with the given value.
    ///
    /// # Examples
    /// ```
    /// use rustica::monads::either::Either;
    /// 
    /// let right_value: Either<i32, i32> = Either::Right(42);
    /// assert_eq!(right_value.unwrap_right(), 42);
    /// ```
    fn pure(value: R) -> Self::Output<R>
    {
        Either::Right(value)
    }
}

impl<L, R> Functor<R> for Either<L, R>
where
    L: ReturnTypeConstraints,
    R: ReturnTypeConstraints,
{
    /// Maps a function over the right value.
    /// 
    /// # Type Parameters
    /// * `T` - The type of the mapped value.
    /// * `F` - The function to map with.
    /// 
    /// Returns
    /// * `Either<L, T>` - The mapped value.
    fn fmap<T, F>(self, f: F) -> Either<L, T>
    where
        T: ReturnTypeConstraints,
        F: FnTrait<R, T>,
    {
        match self {
            Either::Left(l) => Either::Left(l),
            Either::Right(r) => Either::Right(f.call(r)),
        }
    }
}

impl<L, R> Applicative<R> for Either<L, R>
where
    L: ReturnTypeConstraints,
    R: ReturnTypeConstraints,
{
    /// Applies a function to the right value.
    /// 
    /// # Type Parameters
    /// * `T` - The type of the mapped value.
    /// * `F` - The function to map with.
    /// 
    /// Returns
    /// * `Either<L, T>` - The mapped value.
    fn apply<T, F>(self, g: Either<L, F>) -> Either<L, T>
    where
        T: ReturnTypeConstraints,
        F: FnTrait<R, T>,
    {
        match (self, g) {
            (Either::Right(x), Either::Right(f)) => Either::Right(f.call(x)),
            (Either::Left(l), _) => Either::Left(l),
            (_, Either::Left(l)) => Either::Left(l),
        }
    }

    /// Lifts a function from (R, R) to R.
    /// 
    /// # Type Parameters
    /// * `T` - The type of the first argument.
    /// * `U` - The type of the second argument.
    /// * `F` - The function to lift.
    /// 
    /// Returns
    /// * `Either<L, U>` - The lifted value.
    fn lift2<T, U, F>(self, b: Either<L, T>, f: F) -> Either<L, U>
    where
        T: ReturnTypeConstraints,
        U: ReturnTypeConstraints,
        F: FnTrait<(R, T), U>,
    {
        match (self, b) {
            (Either::Right(x), Either::Right(y)) => Either::Right(f.call((x, y))),
            (Either::Left(l), _) => Either::Left(l),
            (_, Either::Left(l)) => Either::Left(l),
        }
    }

    /// Lifts a function from (R, R, R) to R.
    /// 
    /// # Type Parameters
    /// * `T` - The type of the first argument.
    /// * `U` - The type of the second argument.
    /// * `V` - The type of the third argument.
    /// * `F` - The function to lift.
    /// 
    /// Returns
    /// * `Either<L, V>` - The lifted value.
    fn lift3<T, U, V, F>(
        self,
        b: Either<L, T>,
        c: Either<L, U>,
        f: F,
    ) -> Either<L, V>
    where
        T: ReturnTypeConstraints,
        U: ReturnTypeConstraints,
        V: ReturnTypeConstraints,
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
    L: ReturnTypeConstraints,
    T: ReturnTypeConstraints,
{
    /// Binds a function over the right value.
    /// 
    /// # Type Parameters
    /// * `U` - The type of the bound value.
    /// * `F` - The function to bind with.
    /// 
    /// Returns
    /// * `Either<L, U>` - The bound value.
    fn bind<U, F>(self, f: F) -> Self::Output<U>
    where
        U: ReturnTypeConstraints,
        F: FnTrait<T, Self::Output<U>>,
    {
        match self {
            Either::Left(l) => Either::Left(l),
            Either::Right(r) => f.call(r),
        }
    }

    /// Joins a chain of `Either`s into a single `Either`.
    /// 
    /// # Type Parameters
    /// * `U` - The type of the joined value.
    /// 
    /// Returns
    /// * `Either<L, U>` - The joined value.
    fn join<U>(self) -> Self::Output<U>
    where
        U: ReturnTypeConstraints,
        T: Into<Self::Output<U>>,
    {
        match self {
            Either::Left(l) => Either::Left(l),
            Either::Right(r) => r.into(),
        }
    }

    /// Composes two monadic functions.
    /// 
    /// # Type Parameters
    /// * `B` - The type of the first argument.
    /// * `C` - The type of the second argument.
    /// * `G` - The type of the first monadic function.
    /// * `H` - The type of the second monadic function.
    /// 
    /// Returns
    /// * `FnType<T, Self::Output<C>>` - The new computation.
    fn kleisli_compose<B, C, G, H>(g: G, h: H) -> FnType<T, Self::Output<C>>
    where
        B: ReturnTypeConstraints,
        C: ReturnTypeConstraints,
        G: FnTrait<T, Self::Output<B>>,
        H: FnTrait<B, Self::Output<C>>,
    {
        FnType::new(move |x| -> Self::Output<C> {
            g.call(x).bind(h.clone())
        })
    }
}

impl<L, R> Bifunctor<L, R> for Either<L, R>
where
    L: ReturnTypeConstraints,
    R: ReturnTypeConstraints,
{
    type Output<T, U> = Either<T, U> where 
        T: ReturnTypeConstraints,
        U: ReturnTypeConstraints;

    /// Maps a function over the left value
    /// 
    /// # Type Parameters
    /// * `T` - The type of the mapped value.
    /// * `F` - The function to map with.
    /// 
    /// Returns
    /// * `Either<T, R>` - The mapped value.
    fn first<T, F>(self, f: F) -> Self::Output<T, R>
    where
        T: ReturnTypeConstraints,
        F: FnTrait<L, T>,
    {
        match self {
            Either::Left(l) => Either::Left(f.call(l)),
            Either::Right(r) => Either::Right(r),
        }
    }

    /// Maps a function over the right value
    /// 
    /// # Type Parameters
    /// * `T` - The type of the mapped value.
    /// * `F` - The function to map with.
    /// 
    /// Returns
    /// * `Either<L, T>` - The mapped value.
    fn second<T, F>(self, f: F) -> Self::Output<L, T>
    where
        T: ReturnTypeConstraints,
        F: FnTrait<R, T>,
    {
        match self {
            Either::Left(l) => Either::Left(l),
            Either::Right(r) => Either::Right(f.call(r)),
        }
    }

    /// Maps a function over both left and right values
    /// 
    /// # Type Parameters
    /// * `T` - The type of the mapped value.
    /// * `U` - The type of the mapped value.
    /// * `F` - The function to map with.
    /// 
    /// Returns
    /// * `Either<T, U>` - The mapped value.
    fn bimap<T, U, F, G>(self, f: F, g: G) -> Self::Output<T, U>
    where
        T: ReturnTypeConstraints,
        U: ReturnTypeConstraints,
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
    L: ReturnTypeConstraints,
    R: ReturnTypeConstraints,
{
    type Morphism<B, C> = FnType<B, C>
    where
        B: ReturnTypeConstraints,
        C: ReturnTypeConstraints;

    fn identity_morphism<B>() -> Self::Morphism<B, B>
    where
        B: ReturnTypeConstraints,
    {
        FnType::new(|x| x)
    }

    fn compose_morphisms<B, C, D>(
        f: Self::Morphism<B, C>,
        g: Self::Morphism<C, D>
    ) -> Self::Morphism<B, D>
    where
        B: ReturnTypeConstraints,
        C: ReturnTypeConstraints,
        D: ReturnTypeConstraints,
    {
        FnType::new(move |x| g.call(f.call(x)))
    }
}

impl<L, R> Arrow for Either<L, R>
where
    L: ReturnTypeConstraints,
    R: ReturnTypeConstraints,
{
    fn arrow<B, C, F>(f: F) -> Self::Morphism<B, C>
    where
        B: ReturnTypeConstraints,
        C: ReturnTypeConstraints,
        F: FnTrait<B, C> + Clone,
    {
        FnType::new(move |x| f.call(x))
    }

    fn first<B, C, D>(f: Self::Morphism<B, C>) -> Self::Morphism<(B, D), (C, D)>
    where
        B: ReturnTypeConstraints,
        C: ReturnTypeConstraints,
        D: ReturnTypeConstraints,
    {
        FnType::new(move |(x, y)| (f.call(x), y))
    }
}

impl<L, R> Identity for Either<L, R>
where
    L: ReturnTypeConstraints,
    R: ReturnTypeConstraints,
{
    fn identity<T>(x: T) -> T
    where
        T: ReturnTypeConstraints,
    {
        x
    }
}

impl<L, R> Composable for Either<L, R>
where
    L: ReturnTypeConstraints,
    R: ReturnTypeConstraints,
{
    fn compose<T, U, V, F, G>(f: F, g: G) -> FnType<T, V>
    where
        T: ReturnTypeConstraints,
        U: ReturnTypeConstraints,
        V: ReturnTypeConstraints,
        F: FnTrait<T, U>,
        G: FnTrait<U, V>,
    {
        FnType::new(move |x| g.call(f.call(x)))
    }
}
