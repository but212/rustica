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
/// # Examples
///
/// ```
/// use rustica::monads::maybe::Maybe;
///
/// let just = Maybe::Just(42);
/// let nothing: Maybe<i32> = Maybe::Nothing;
///
/// assert!(just.is_just());
/// assert!(nothing.is_nothing());
/// ```
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Maybe<T>
where
    T: ReturnTypeConstraints,
{
    Just(T),
    Nothing,
}

impl<T> Default for Maybe<T>
where
    T: ReturnTypeConstraints,
{
    fn default() -> Self {
        Maybe::Nothing
    }
}

impl<T> Maybe<T>
where
    T: ReturnTypeConstraints,
{
    /// Returns `true` if the `Maybe` value is `Just`, otherwise returns `false`.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::monads::maybe::Maybe;
    ///
    /// let just = Maybe::Just(42);
    /// let nothing: Maybe<i32> = Maybe::Nothing;
    ///
    /// assert!(just.is_just());
    /// assert!(!nothing.is_just());
    /// ```
    pub fn is_just(&self) -> bool {
        matches!(self, Maybe::Just(_))
    }

    /// Returns `true` if the `Maybe` value is `Nothing`, otherwise returns `false`.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::monads::maybe::Maybe;
    ///
    /// let just = Maybe::Just(42);
    /// let nothing: Maybe<i32> = Maybe::Nothing;
    ///
    /// assert!(!just.is_nothing());
    /// assert!(nothing.is_nothing());
    /// ```
    pub fn is_nothing(&self) -> bool {
        matches!(self, Maybe::Nothing)
    }

    /// Converts an `Option<T>` into a `Maybe<T>`.
    ///
    /// This function transforms `Some(x)` into `Maybe::Just(x)` and `None` into `Maybe::Nothing`.
    ///
    /// # Arguments
    ///
    /// * `opt` - An `Option<T>` to be converted.
    ///
    /// # Returns
    ///
    /// A `Maybe<T>` equivalent to the input `Option<T>`.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::monads::maybe::Maybe;
    ///
    /// let some_value = Some(42);
    /// let maybe_value = Maybe::from_option(some_value);
    /// assert_eq!(maybe_value, Maybe::Just(42));
    ///
    /// let none_value: Option<i32> = None;
    /// let maybe_none = Maybe::from_option(none_value);
    /// assert_eq!(maybe_none, Maybe::Nothing);
    /// ```
    pub fn from_option(opt: Option<T>) -> Self {
        match opt {
            Some(x) => Maybe::Just(x),
            None => Maybe::Nothing,
        }
    }

    /// Converts a `Maybe<T>` into an `Option<T>`.
    ///
    /// This function transforms `Maybe::Just(x)` into `Some(x)` and `Maybe::Nothing` into `None`.
    ///
    /// # Returns
    ///
    /// An `Option<T>` equivalent to the input `Maybe<T>`.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::monads::maybe::Maybe;
    ///
    /// let just = Maybe::Just(42);
    /// assert_eq!(just.to_option(), Some(42));
    ///
    /// let nothing: Maybe<i32> = Maybe::Nothing;
    /// assert_eq!(nothing.to_option(), None);
    /// ```
    pub fn to_option(self) -> Option<T> {
        match self {
            Maybe::Just(x) => Some(x),
            Maybe::Nothing => None,
        }
    }

    /// Unwraps the `Maybe` value, returning the contained value if it's `Just`.
    ///
    /// # Panics
    ///
    /// Panics if the value is `Nothing`.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::monads::maybe::Maybe;
    ///
    /// let x = Maybe::Just(5);
    /// assert_eq!(x.unwrap(), 5);
    ///
    /// let x: Maybe<i32> = Maybe::Nothing;
    /// // This will panic
    /// // x.unwrap();
    /// ```
    pub fn unwrap(self) -> T {
        match self {
            Maybe::Just(x) => x,
            Maybe::Nothing => panic!("Tried to unwrap a Nothing value!"),
        }
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

impl<T: ReturnTypeConstraints> Identity for Maybe<T> {}

impl<T: ReturnTypeConstraints> Composable for Maybe<T> {}

impl<T: ReturnTypeConstraints> Category for Maybe<T> {
    type Morphism<B, C> = FnType<B, C>
    where
        B: ReturnTypeConstraints,
        C: ReturnTypeConstraints;
}

impl<T: ReturnTypeConstraints> Arrow for Maybe<T> {}