use crate::traits::hkt::{HKT, TypeConstraints};
use crate::traits::functor::Functor;
use crate::traits::applicative::Applicative;
use crate::traits::monad::Monad;
use crate::traits::pure::Pure;
use crate::traits::category::Category;
use crate::traits::arrow::Arrow;
use crate::traits::composable::Composable;
use crate::traits::identity::Identity;
use crate::fntype::{FnType, FnTrait};

/// A type that represents an optional value.
///
/// # Examples
///
/// ```
/// use rustica::datatypes::maybe::Maybe;
/// use rustica::traits::functor::Functor;
/// use rustica::traits::monad::Monad;
/// use rustica::traits::applicative::Applicative;
/// use rustica::fntype::{FnType, FnTrait};
///
/// let just = Maybe::Just(42);
/// let nothing: Maybe<i32> = Maybe::Nothing;
///
/// // Using fmap (Functor)
/// assert_eq!(just.clone().fmap(FnType::new(|x| x * 2)), Maybe::Just(84));
/// assert_eq!(nothing.clone().fmap(FnType::new(|x| x * 2)), Maybe::Nothing);
///
/// // Using bind (Monad)
/// assert_eq!(just.clone().bind(FnType::new(|x: i32| Maybe::Just(x.to_string()))), Maybe::Just("42".to_string()));
/// assert_eq!(nothing.clone().bind(FnType::new(|x: i32| Maybe::Just(x.to_string()))), Maybe::Nothing);
///
/// // Using apply (Applicative)
/// let f = Maybe::Just(FnType::new(|x: i32| x + 1));
/// assert_eq!(just.apply(f.clone()), Maybe::Just(43));
/// assert_eq!(nothing.apply(f), Maybe::Nothing);
/// ```
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Maybe<T: TypeConstraints> {
    Just(T),
    Nothing,
}

impl<T: TypeConstraints> Default for Maybe<T> {
    fn default() -> Self {
        Maybe::Nothing
    }
}

impl<T: TypeConstraints> Maybe<T> {
    /// Returns `true` if the `Maybe` value is `Just`, otherwise returns `false`.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::datatypes::maybe::Maybe;
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
    /// use rustica::datatypes::maybe::Maybe;
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
    /// use rustica::datatypes::maybe::Maybe;
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
    /// use rustica::datatypes::maybe::Maybe;
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
    /// use rustica::datatypes::maybe::Maybe;
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

impl<T: TypeConstraints> HKT for Maybe<T> {
    type Output<U> = Maybe<U> where U: TypeConstraints;
}

impl<T: TypeConstraints> Pure<T> for Maybe<T> {
    fn pure(value: T) -> Self::Output<T> {
        Maybe::Just(value)
    }
}

impl<T: TypeConstraints> Functor<T> for Maybe<T> {
    fn fmap<U, F>(self, f: F) -> Self::Output<U>
    where
        U: TypeConstraints,
        F: FnTrait<T, U>,
    {
        match self {
            Maybe::Just(x) => Maybe::Just(f.call(x)),
            Maybe::Nothing => Maybe::Nothing,
        }
    }
}

impl<T: TypeConstraints> Applicative<T> for Maybe<T> {
    fn apply<U, F>(self, g: Self::Output<F>) -> Self::Output<U>
    where
        U: TypeConstraints,
        F: FnTrait<T, U>,
    {
        match (self, g) {
            (Maybe::Just(x), Maybe::Just(f)) => Maybe::Just(f.call(x)),
            _ => Maybe::Nothing,
        }
    }

    fn lift2<U, V, F>(self, b: Self::Output<U>, f: F) -> Self::Output<V>
    where
        U: TypeConstraints,
        V: TypeConstraints,
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
        U: TypeConstraints,
        V: TypeConstraints,
        W: TypeConstraints,
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

impl<T: TypeConstraints> Identity<T> for Maybe<T> {
    fn map_identity<U, F>(f: F) -> Self::Output<U>
    where
        U: TypeConstraints,
        F: FnTrait<T, U>,
    {
        Maybe::Just(f.call(T::default()))
    }
}

impl<T: TypeConstraints> Monad<T> for Maybe<T> {
    fn bind<B, F>(self, f: F) -> Self::Output<B>
    where
        B: TypeConstraints,
        F: FnTrait<T, Self::Output<B>>,
    {
        match self {
            Maybe::Just(x) => f.call(x),
            Maybe::Nothing => Maybe::Nothing,
        }
    }

    fn join<B>(self) -> Self::Output<B>
    where
        B: TypeConstraints,
        T: Into<Self::Output<B>>,
    {
        match self {
            Maybe::Just(x) => x.into(),
            Maybe::Nothing => Maybe::Nothing,
        }
    }

    fn then<B: TypeConstraints>(self, mb: Self::Output<B>) -> Self::Output<B> {
        let f = FnType::new(move |_| mb.clone());
        self.bind(f)
    }

    fn returns<B, F>(self, f: F) -> Self::Output<B>
    where
        B: TypeConstraints,
        F: FnTrait<T, B>,
    {
        match self {
            Maybe::Just(x) => Maybe::Just(f.call(x)),
            Maybe::Nothing => Maybe::Nothing,
        }
    }
}

impl<T: TypeConstraints> Composable<T> for Maybe<T> {
    fn compose_with<U, F>(self, f: F) -> Self::Output<U>
    where
        U: TypeConstraints,
        F: FnTrait<T, U>,
    {
        match self {
            Maybe::Just(x) => Maybe::Just(f.call(x)),
            Maybe::Nothing => Maybe::Nothing,
        }
    }
}

impl<T: TypeConstraints> Category<T> for Maybe<T> {
    type Morphism<B, C> = FnType<B, C> where B: TypeConstraints, C: TypeConstraints;
}

impl<T: TypeConstraints, U: TypeConstraints> Arrow<T, U> for Maybe<T> {}

impl<T: TypeConstraints> FromIterator<T> for Maybe<T> {
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        let mut iter = iter.into_iter();
        iter.next().map_or(Maybe::Nothing, Maybe::Just)
    }
}

impl<T: TypeConstraints> From<Option<T>> for Maybe<T>
where
    T: TypeConstraints,
{
    fn from(opt: Option<T>) -> Self {
        match opt {
            Some(value) => Maybe::Just(value),
            None => Maybe::Nothing,
        }
    }
}