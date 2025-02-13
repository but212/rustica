use crate::category::hkt::{HKT, ReturnTypeConstraints};
use crate::category::functor::Functor;
use crate::category::applicative::Applicative;
use crate::category::monad::Monad;
use crate::category::pure::Pure;
use crate::category::category::Category;
use crate::category::arrow::Arrow;
use crate::category::composable::Composable;
use crate::category::identity::Identity;
use crate::fntype::{FnType, FnTrait};

/// A type that represents an optional value.
///
/// The `Maybe` type is used to represent an optional value that can either be `Just`
/// containing a value of type `T`, or `Nothing` indicating the absence of a value.
/// 
/// # Type Parameters
/// * `T` - The value type.
///
/// # Laws
/// A Maybe instance must satisfy these laws in addition to the standard Monad laws:
/// 1. Left Identity: For any value `x` and function `f`,
///    `Maybe::pure(x).bind(f) = f(x)`
/// 2. Right Identity: For any Maybe value `m`,
///    `m.bind(Maybe::pure) = m`
/// 3. Nothing Propagation: For any function `f`,
///    `Maybe::Nothing.bind(f) = Maybe::Nothing`
/// 4. Option Consistency: For any Maybe value `m`,
///    `Maybe::from_option(m.to_option()) = m`
///
/// # Examples
///
/// ```
/// use rustica::prelude::*;
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
#[derive(Clone, Debug)]
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
    /// 
    /// # Returns
    /// * `bool` - True if the maybe is Just, false otherwise.
    pub fn is_just(&self) -> bool {
        matches!(self, Maybe::Just(_))
    }

    /// Returns true if the maybe is Nothing
    /// 
    /// # Returns
    /// * `bool` - True if the maybe is Nothing, false otherwise.
    pub fn is_nothing(&self) -> bool {
        matches!(self, Maybe::Nothing)
    }

    /// Converts from Option<T> to Maybe<T>
    /// 
    /// # Arguments
    /// * `opt` - The option to be converted.
    /// 
    /// # Returns
    /// * `Maybe<T>` - The maybe representation of the option.
    pub fn from_option(opt: Option<T>) -> Self {
        match opt {
            Some(x) => Maybe::Just(x),
            None => Maybe::Nothing,
        }
    }

    /// Converts from Maybe<T> to Option<T>
    /// 
    /// # Arguments
    /// * `self` - The maybe to be converted.
    /// 
    /// # Returns
    /// * `Option<T>` - The option representation of the maybe.
    pub fn to_option(self) -> Option<T> {
        match self {
            Maybe::Just(x) => Some(x),
            Maybe::Nothing => None,
        }
    }

    /// Unwraps the maybe, panicking if the maybe is Nothing
    /// 
    /// # Panics
    /// Panics if the maybe is Nothing
    /// 
    /// # Returns
    /// * `T` - The value of the maybe.
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
    fn fmap<U, F>(self, f: F) -> Self::Output<U>
    where
        U: ReturnTypeConstraints,
        F: FnTrait<T, U>,
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
        F: FnTrait<T, U>,
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
        F: FnTrait<(T, U), V>,
    {
        match (self, b) {
            (Maybe::Just(a), Maybe::Just(b)) => Maybe::Just(f.call((a, b))),
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
        F: FnTrait<(T, U, V), W>,
    {
        match (self, b, c) {
            (Maybe::Just(a), Maybe::Just(b), Maybe::Just(c)) => {
                Maybe::Just(f.call((a, b, c)))
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
        F: FnTrait<T, Self::Output<U>>,
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

    fn kleisli_compose<U, V, G, H>(g: G, h: H) -> FnType<T, Self::Output<V>>
    where
        U: ReturnTypeConstraints,
        V: ReturnTypeConstraints,
        G: FnTrait<T, Self::Output<U>>,
        H: FnTrait<U, Self::Output<V>>,
    {
        FnType::new(move |x| -> Self::Output<V> {
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

impl<T> Identity for Maybe<T>
where
    T: ReturnTypeConstraints,
{
    fn identity<U>(x: U) -> U
    where
        U: ReturnTypeConstraints,
    {
        x
    }
}

impl<T> Composable for Maybe<T>
where
    T: ReturnTypeConstraints,
{
    fn compose<U, V, W, F, G>(f: F, g: G) -> FnType<U, W>
    where
        U: ReturnTypeConstraints,
        V: ReturnTypeConstraints,
        W: ReturnTypeConstraints,
        F: FnTrait<U, V>,
        G: FnTrait<V, W>,
    {
        FnType::new(move |x| g.call(f.call(x)))
    }
}

impl<T> Category for Maybe<T>
where
    T: ReturnTypeConstraints,
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

impl<T> Arrow for Maybe<T>
where
    T: ReturnTypeConstraints,
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
        FnType::new(move |(b, d): (B, D)| (f.call(b), d))
    }
}
