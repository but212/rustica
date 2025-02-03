use std::fmt::Debug;

use crate::category::{Applicative, Functor, HKT, Monad, Pure, ReturnTypeConstraints};
use crate::fntype::{SendSyncFn, SendSyncFnTrait, ApplyFn, BindFn, MonadFn};

/// A type that represents an optional value.
///
/// The `Maybe` type is used to represent an optional value that can either be `Just`
/// containing a value of type `T`, or `Nothing` indicating the absence of a value.
///
/// # Examples
///
/// ```
/// use rustica::category::hkt::ReturnTypeConstraints;
/// use rustica::monads::maybe::Maybe;
///
/// let just_value: Maybe<i32> = Maybe::Just(42);
/// let nothing_value: Maybe<i32> = Maybe::Nothing;
///
/// assert!(just_value.is_just());
/// assert!(!nothing_value.is_just());
///
/// assert_eq!(just_value.unwrap(), 42);
/// ```
#[derive(Debug, Clone, PartialEq)]
pub enum Maybe<T>
where
    T: ReturnTypeConstraints,
{
    /// Some value
    Just(T),
    /// No value
    Nothing,
}

impl<T> Maybe<T>
where
    T: ReturnTypeConstraints,
{
    /// Returns true if the maybe is Just
    pub fn is_just(&self) -> bool {
        matches!(self, Maybe::Just(_))
    }

    /// Returns true if the maybe is Nothing
    pub fn is_nothing(&self) -> bool {
        matches!(self, Maybe::Nothing)
    }

    /// Converts from Option<T> to Maybe<T>
    pub fn from_option(opt: Option<T>) -> Self {
        match opt {
            Some(x) => Maybe::Just(x),
            None => Maybe::Nothing,
        }
    }

    /// Converts from Maybe<T> to Option<T>
    pub fn to_option(self) -> Option<T> {
        match self {
            Maybe::Just(x) => Some(x),
            Maybe::Nothing => None,
        }
    }

    pub fn unwrap(self) -> T {
        match self {
            Maybe::Just(x) => x,
            Maybe::Nothing => panic!("Tried to unwrap a Nothing value!"),
        }
    }
}

impl<T> Default for Maybe<T>
where
    T: ReturnTypeConstraints,
{
    fn default() -> Self {
        Maybe::Nothing
    }
}

impl<T> HKT for Maybe<T>
where
    T: ReturnTypeConstraints,
{
    type Output<U> = Maybe<U> where U: ReturnTypeConstraints;
}

impl<T> Pure<T> for Maybe<T>
where
    T: ReturnTypeConstraints,
{
    fn pure(value: T) -> Self::Output<T> {
        Maybe::Just(value)
    }
}

impl<T> Functor<T> for Maybe<T>
where
    T: ReturnTypeConstraints,
{
    fn map<U, F>(self, f: F) -> Self::Output<U>
    where
        U: ReturnTypeConstraints,
        F: SendSyncFnTrait<T, U>,
    {
        match self {
            Maybe::Just(x) => Maybe::Just(f.call(x)),
            Maybe::Nothing => Maybe::Nothing,
        }
    }
}

impl<T> Applicative<T> for Maybe<T>
where
    T: ReturnTypeConstraints,
{
    fn apply<U, F>(self, g: Self::Output<F>) -> Self::Output<U>
    where
        U: ReturnTypeConstraints,
        F: ApplyFn<T, U> + Default,
    {
        match (self, g) {
            (Maybe::Just(x), Maybe::Just(f)) => Maybe::Just(f.call(x)),
            _ => Maybe::Nothing,
        }
    }

    fn lift2<U, V, F>(self, b: Self::Output<U>, f: F) -> Self::Output<V>
    where
        U: ReturnTypeConstraints,
        V: ReturnTypeConstraints,
        F: ApplyFn<T, SendSyncFn<U, V>>,
    {
        match (self, b) {
            (Maybe::Just(a), Maybe::Just(b)) => Maybe::Just(f.call(a).call(b)),
            _ => Maybe::Nothing,
        }
    }

    fn lift3<U, V, W, F>(
        self,
        b: Self::Output<U>,
        c: Self::Output<V>,
        f: F,
    ) -> Self::Output<W>
    where
        U: ReturnTypeConstraints,
        V: ReturnTypeConstraints,
        W: ReturnTypeConstraints,
        F: ApplyFn<T, SendSyncFn<U, SendSyncFn<V, W>>>,
    {
        match (self, b, c) {
            (Maybe::Just(a), Maybe::Just(b), Maybe::Just(c)) => {
                Maybe::Just(f.call(a).call(b).call(c))
            }
            _ => Maybe::Nothing,
        }
    }
}

impl<T> Monad<T> for Maybe<T>
where
    T: ReturnTypeConstraints,
{
    fn bind<U, F>(self, f: F) -> Self::Output<U>
    where
        U: ReturnTypeConstraints,
        F: BindFn<T, U, Self::Output<U>>,
    {
        match self {
            Maybe::Just(x) => f.call(x),
            Maybe::Nothing => Maybe::Nothing,
        }
    }

    fn join<U>(self) -> Self::Output<U>
    where
        U: ReturnTypeConstraints,
        T: Into<Self::Output<U>>,
    {
        match self {
            Maybe::Just(x) => x.into(),
            Maybe::Nothing => Maybe::Nothing,
        }
    }

    fn kleisli_compose<U, V, G, H>(g: G, h: H) -> SendSyncFn<T, Self::Output<V>>
    where
        U: ReturnTypeConstraints,
        V: ReturnTypeConstraints,
        G: MonadFn<T, U, Self::Output<U>>,
        H: MonadFn<U, V, Self::Output<V>>,
    {
        SendSyncFn::new(move |x| -> Self::Output<V> {
            g.call(x).bind(h.clone())
        })
    }
}

impl<T> FromIterator<T> for Maybe<T>
where
    T: ReturnTypeConstraints,
{
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        let mut iter = iter.into_iter();
        iter.next().map_or(Maybe::Nothing, Maybe::Just)
    }
}

impl<T> From<Option<T>> for Maybe<T>
where
    T: ReturnTypeConstraints,
{
    fn from(opt: Option<T>) -> Self {
        match opt {
            Some(value) => Maybe::Just(value),
            None => Maybe::Nothing,
        }
    }
}
