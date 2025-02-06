use std::fmt::Debug;

use crate::category::{Applicative, Bifunctor, Functor, HKT, Monad, Pure, ReturnTypeConstraints};
use crate::fntype::{SendSyncFn, SendSyncFnTrait, ApplyFn, MonadFn};

/// A type that represents one of two possible values.
/// 
/// # Type Parameters
/// * `L` - The left value type
/// * `R` - The right value type
/// 
/// # Laws
/// An `Either` instance must satisfy these laws:
/// 1. Identity: `either.map(|x| x) = either`
/// 2. Composition: `either.map(f).map(g) = either.map(|x| g(f(x)))`
/// 3. Applicative: Errors are accumulated when combining multiple `Either` values
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
#[derive(Debug, Clone, PartialEq, Eq)]
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
    pub fn is_left(&self) -> bool {
        matches!(self, Either::Left(_))
    }

    /// Returns true if this is a Right value.
    pub fn is_right(&self) -> bool {
        matches!(self, Either::Right(_))
    }

    /// Maps a function over the left value.
    ///
    /// # Examples
    /// ```
    /// use rustica::monads::either::Either;
    /// use rustica::fntype::SendSyncFn;
    /// 
    /// let left_value: Either<i32, i32> = Either::Left(42);
    /// let mapped_left = left_value.map_left(SendSyncFn::new(|x| x + 1));
    /// assert_eq!(mapped_left.unwrap_left(), 43);
    /// ```
    pub fn map_left<T, F>(self, f: F) -> Either<T, R>
    where
        T: ReturnTypeConstraints,
        F: SendSyncFnTrait<L, T>,
    {
        match self {
            Either::Left(l) => Either::Left(f.call(l)),
            Either::Right(r) => Either::Right(r),
        }
    }

    /// Maps a function over the right value.
    ///
    /// # Examples
    /// ```
    /// use rustica::monads::either::Either;
    /// use rustica::fntype::SendSyncFn;
    /// 
    /// let right_value: Either<i32, i32> = Either::Right(42);
    /// let mapped_right = right_value.map_right(SendSyncFn::new(|x| x + 1));
    /// assert_eq!(mapped_right.unwrap_right(), 43);
    /// ```
    pub fn map_right<T, F>(self, f: F) -> Either<L, T>
    where
        T: ReturnTypeConstraints,
        F: SendSyncFnTrait<R, T>,
    {
        match self {
            Either::Left(l) => Either::Left(l),
            Either::Right(r) => Either::Right(f.call(r)),
        }
    }

    /// Unwraps the left value, panicking if this is a Right value.
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

impl<L, R> Default for Either<L, R>
where
    L: ReturnTypeConstraints,
    R: ReturnTypeConstraints,
{
    fn default() -> Self {
        Either::Left(L::default())
    }
}

impl<L, R> Pure<R> for Either<L, R>
where
    L: ReturnTypeConstraints,
    R: ReturnTypeConstraints,
{
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
    fn map<T, F>(self, f: F) -> Either<L, T>
    where
        T: ReturnTypeConstraints,
        F: SendSyncFnTrait<R, T>,
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
    fn apply<T, F>(self, g: Either<L, F>) -> Either<L, T>
    where
        T: ReturnTypeConstraints,
        F: ApplyFn<R, T> + Default,
    {
        match (self, g) {
            (Either::Right(x), Either::Right(f)) => Either::Right(f.call(x)),
            (Either::Left(l), _) => Either::Left(l),
            (_, Either::Left(l)) => Either::Left(l),
        }
    }

    fn lift2<T, U, F>(self, b: Either<L, T>, f: F) -> Either<L, U>
    where
        T: ReturnTypeConstraints,
        U: ReturnTypeConstraints,
        F: ApplyFn<R, SendSyncFn<T, U>> + Default,
    {
        match (self, b) {
            (Either::Right(a), Either::Right(b)) => Either::Right(f.call(a).call(b)),
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
        T: ReturnTypeConstraints,
        U: ReturnTypeConstraints,
        V: ReturnTypeConstraints,
        F: ApplyFn<R, SendSyncFn<T, SendSyncFn<U, V>>>,
    {
        match (self, b, c) {
            (Either::Right(a), Either::Right(b), Either::Right(c)) => {
                Either::Right(f.call(a).call(b).call(c))
            }
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
    fn bind<U, F>(self, f: F) -> Self::Output<U>
    where
        U: ReturnTypeConstraints,
        F: SendSyncFnTrait<T, Self::Output<U>>,
    {
        match self {
            Either::Left(l) => Either::Left(l),
            Either::Right(r) => f.call(r),
        }
    }

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

    fn kleisli_compose<B, C, G, H>(g: G, h: H) -> SendSyncFn<T, Self::Output<C>>
    where
        B: ReturnTypeConstraints,
        C: ReturnTypeConstraints,
        G: MonadFn<T, B, Self::Output<B>>,
        H: MonadFn<B, C, Self::Output<C>>,
    {
        SendSyncFn::new(move |x| -> Self::Output<C> {
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
    fn first<T, F>(self, f: F) -> Self::Output<T, R>
    where
        T: ReturnTypeConstraints,
        F: SendSyncFnTrait<L, T>,
    {
        match self {
            Either::Left(l) => Either::Left(f.call(l)),
            Either::Right(r) => Either::Right(r),
        }
    }

    fn second<T, F>(self, f: F) -> Self::Output<L, T>
    where
        T: ReturnTypeConstraints,
        F: SendSyncFnTrait<R, T>,
    {
        match self {
            Either::Left(l) => Either::Left(l),
            Either::Right(r) => Either::Right(f.call(r)),
        }
    }

    fn bimap<T, U, F, G>(self, f: F, g: G) -> Self::Output<T, U>
    where
        T: ReturnTypeConstraints,
        U: ReturnTypeConstraints,
        F: SendSyncFnTrait<L, T>,
        G: SendSyncFnTrait<R, U>,
    {
        match self {
            Either::Left(l) => Either::Left(f.call(l)),
            Either::Right(r) => Either::Right(g.call(r)),
        }
    }
}
