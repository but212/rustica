//! The Maybe monad represents computations which may fail or return a value.
//! 
//! `Maybe<T>` is an enum that can be either `Just(T)` containing a value, or `Nothing` 
//! representing the absence of a value. This is similar to Rust's built-in `Option<T>` type,
//! but with additional monadic operations.
//! 
//! # Key Features
//! 
//! - **Failure Handling**: Represents computations that might not return a value
//! - **Short-circuiting**: Operations on `Nothing` propagate the `Nothing` value
//! - **Composition**: Chain operations together without explicit null checks
//! 
//! # Common Use Cases
//! 
//! - Representing optional values without using `null`
//! - Chaining operations that might fail
//! - Transforming optional values without unwrapping
//! 
//! # Relationship to Rust's Option
//! 
//! `Maybe<T>` is functionally equivalent to Rust's `Option<T>`, but provides
//! additional monadic operations. Conversion methods are provided to interoperate
//! with `Option<T>`.
//! 
//! # Examples
//! 
//! ```rust
//! use rustica::datatypes::maybe::Maybe;
//! use rustica::traits::functor::Functor;
//! use rustica::traits::monad::Monad;
//! 
//! // Creating Maybe values
//! let just_value = Maybe::Just(42);
//! let nothing_value: Maybe<i32> = Maybe::Nothing;
//! 
//! // Using fmap to transform the value
//! let doubled = just_value.fmap(|x| x * 2);  // Maybe::Just(84)
//! let doubled_nothing = nothing_value.fmap(|x| x * 2);  // Maybe::Nothing
//! 
//! // Chaining operations with bind
//! let result = just_value.bind(|x| {
//!     if *x > 0 {
//!         Maybe::Just(x * 10)
//!     } else {
//!         Maybe::Nothing
//!     }
//! });  // Maybe::Just(420)
//! ```

use crate::traits::hkt::HKT;
use crate::traits::functor::Functor;
use crate::traits::applicative::Applicative;
use crate::traits::monad::Monad;
use crate::traits::pure::Pure;
use crate::traits::composable::Composable;
use crate::traits::identity::Identity;

/// A type that represents an optional value.
///
/// `Maybe<T>` is an enum that can be either `Just(T)` containing a value, or `Nothing` 
/// representing the absence of a value.
///
/// # Type Parameters
///
/// * `T` - The type of the value that might be contained
///
/// # Examples
///
/// ```rust
/// use rustica::datatypes::maybe::Maybe;
///
/// let just_five = Maybe::Just(5);
/// let nothing: Maybe<i32> = Maybe::Nothing;
///
/// // Pattern matching
/// match just_five {
///     Maybe::Just(x) => println!("Got a value: {}", x),
///     Maybe::Nothing => println!("Got nothing"),
/// }
/// ```
#[derive(Clone)]
pub enum Maybe<T> {
    /// Contains a value of type `T`
    Just(T),
    /// Represents the absence of a value
    Nothing,
}

impl<T> Maybe<T> {
    /// Returns `true` if the maybe value is a `Just` value.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::maybe::Maybe;
    ///
    /// let x: Maybe<u32> = Maybe::Just(2);
    /// assert_eq!(x.is_just(), true);
    ///
    /// let y: Maybe<u32> = Maybe::Nothing;
    /// assert_eq!(y.is_just(), false);
    /// ```
    pub fn is_just(&self) -> bool {
        matches!(self, Maybe::Just(_))
    }

    /// Returns `true` if the maybe value is a `Nothing` value.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::maybe::Maybe;
    ///
    /// let x: Maybe<u32> = Maybe::Just(2);
    /// assert_eq!(x.is_nothing(), false);
    ///
    /// let y: Maybe<u32> = Maybe::Nothing;
    /// assert_eq!(y.is_nothing(), true);
    /// ```
    pub fn is_nothing(&self) -> bool {
        matches!(self, Maybe::Nothing)
    }

    /// Converts from `Option<T>` to `Maybe<T>`.
    ///
    /// `Some(x)` is converted to `Just(x)`, and `None` is converted to `Nothing`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::maybe::Maybe;
    ///
    /// let opt_some = Some(42);
    /// let opt_none: Option<i32> = None;
    ///
    /// let maybe_just = Maybe::from_option(opt_some);
    /// let maybe_nothing = Maybe::from_option(opt_none);
    ///
    /// assert!(maybe_just.is_just());
    /// assert!(maybe_nothing.is_nothing());
    /// ```
    pub fn from_option(opt: Option<T>) -> Self {
        match opt {
            Some(x) => Maybe::Just(x),
            None => Maybe::Nothing,
        }
    }

    /// Converts from `Maybe<T>` to `Option<T>`.
    ///
    /// `Just(x)` is converted to `Some(x)`, and `Nothing` is converted to `None`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::maybe::Maybe;
    ///
    /// let maybe_just = Maybe::Just(42);
    /// let maybe_nothing: Maybe<i32> = Maybe::Nothing;
    ///
    /// let opt_some = maybe_just.to_option();
    /// let opt_none = maybe_nothing.to_option();
    ///
    /// assert_eq!(opt_some, Some(42));
    /// assert_eq!(opt_none, None);
    /// ```
    pub fn to_option(self) -> Option<T> {
        match self {
            Maybe::Just(x) => Some(x),
            Maybe::Nothing => None,
        }
    }

    /// Unwraps a maybe, yielding the content of a `Just`.
    ///
    /// # Panics
    ///
    /// Panics if the value is a `Nothing` with a custom panic message.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::maybe::Maybe;
    ///
    /// let x = Maybe::Just("air");
    /// assert_eq!(x.unwrap(), "air");
    /// ```
    ///
    /// ```rust,should_panic
    /// use rustica::datatypes::maybe::Maybe;
    ///
    /// let x: Maybe<&str> = Maybe::Nothing;
    /// x.unwrap(); // This will panic
    /// ```
    pub fn unwrap(self) -> T {
        match self {
            Maybe::Just(x) => x,
            Maybe::Nothing => panic!("Tried to unwrap a Nothing value!"),
        }
    }
}

impl<T> HKT for Maybe<T> {
    type Source = T;
    type Output<U> = Maybe<U>;
}

impl<T> Pure for Maybe<T> {
    fn pure<U: Clone>(value: &U) -> Self::Output<U> {
        Maybe::Just(value.clone())
    }
}

impl<T> Functor for Maybe<T> {
    fn fmap<B, F>(&self, f: F) -> Self::Output<B>
    where
        F: Fn(&Self::Source) -> B,
    {
        match self {
            Maybe::Just(x) => Maybe::Just(f(x)),
            Maybe::Nothing => Maybe::Nothing,
        }
    }

    fn fmap_owned<B, F>(self, f: F) -> Self::Output<B>
    where
        F: Fn(Self::Source) -> B,
    {
        match self {
            Maybe::Just(x) => Maybe::Just(f(x)),
            Maybe::Nothing => Maybe::Nothing,
        }
    }
}

impl<T> Applicative for Maybe<T> {
    fn apply<B, F>(&self, f: &Self::Output<F>) -> Self::Output<B>
        where
            F: Fn(&Self::Source) -> B {
        match (self, f) {
            (Maybe::Just(x), Maybe::Just(f)) => Maybe::Just(f(x)),
            _ => Maybe::Nothing,
        }
    }

    fn lift2<B, C, F>(&self, b: &Self::Output<B>, f: F) -> Self::Output<C>
    where
        F: Fn(&Self::Source, &B) -> C,
    {
        match (self, b) {
            (Maybe::Just(x), Maybe::Just(y)) => Maybe::Just(f(x, y)),
            _ => Maybe::Nothing,
        }
    }

    fn lift3<B, C, D, F>(&self, b: &Self::Output<B>, c: &Self::Output<C>, f: F) -> Self::Output<D>
    where
        F: Fn(&Self::Source, &B, &C) -> D,
    {
        match (self, b, c) {
            (Maybe::Just(x), Maybe::Just(y), Maybe::Just(z)) => Maybe::Just(f(x, y, z)),
            _ => Maybe::Nothing,
        }
    }

    fn apply_owned<B, F>(self, f: Self::Output<F>) -> Self::Output<B>
        where
            F: Fn(Self::Source) -> B,
            Self: Sized {
        match (self, f) {
            (Maybe::Just(x), Maybe::Just(f)) => Maybe::Just(f(x)),
            _ => Maybe::Nothing,
        }
    }

    fn lift2_owned<B, C, F>(
            self,
            b: Self::Output<B>,
            f: F,
        ) -> Self::Output<C>
        where
            F: Fn(Self::Source, B) -> C,
            Self: Sized,
            B: Clone {
        match (self, b) {
            (Maybe::Just(x), Maybe::Just(y)) => Maybe::Just(f(x, y.clone())),
            _ => Maybe::Nothing,
        }
    }

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
            C: Clone {
        match (self, b, c) {
            (Maybe::Just(x), Maybe::Just(y), Maybe::Just(z)) => Maybe::Just(f(x, y.clone(), z.clone())),
            _ => Maybe::Nothing,
        }
    }
}

impl<T> Monad for Maybe<T> {
    fn bind<U, F>(&self, f: F) -> Self::Output<U>
        where
            F: Fn(&Self::Source) -> Self::Output<U>,
            Self::Source: Clone,
            U: Clone {
        match self {
            Maybe::Just(x) => f(&x),
            Maybe::Nothing => Maybe::Nothing,
        }
    }

    fn bind_owned<U, F>(self, f: F) -> Self::Output<U>
        where
            F: Fn(Self::Source) -> Self::Output<U>,
            U: Clone,
            Self: Sized {
        match self {
            Maybe::Just(x) => f(x),
            Maybe::Nothing => Maybe::Nothing,
        }
    }

    fn join<U>(&self) -> Self::Output<U>
        where
            Self::Source: Clone + Into<Self::Output<U>>,
            U: Clone {
        match self {
            Maybe::Just(x) => x.to_owned().into(),
            Maybe::Nothing => Maybe::Nothing,
        }
    }
    
    fn join_owned<U>(self) -> Self::Output<U>
        where
            Self::Source: Into<Self::Output<U>>,
            U: Clone,
            Self: Sized {
        match self {
            Maybe::Just(x) => x.into(),
            Maybe::Nothing => Maybe::Nothing,
        }
    }
}

/// Implementation of FromIterator trait for Maybe
///
/// This allows collecting an iterator into a Maybe value.
impl<T> FromIterator<T> for Maybe<T> {
    /// Creates a Maybe from an iterator.
    ///
    /// Returns `Just` with the first element, or `Nothing` if the iterator is empty.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::maybe::Maybe;
    ///
    /// let v = vec![1, 2, 3];
    /// let maybe: Maybe<i32> = v.into_iter().collect();
    /// assert!(maybe.is_just());
    ///
    /// let empty: Vec<i32> = vec![];
    /// let maybe_empty: Maybe<i32> = empty.into_iter().collect();
    /// assert!(maybe_empty.is_nothing());
    /// ```
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        let mut iter = iter.into_iter();
        iter.next().map_or(Maybe::Nothing, Maybe::Just)
    }
}

/// Implementation of From trait for converting from Option to Maybe
impl<T> From<Option<T>> for Maybe<T> {
    /// Converts an Option into a Maybe.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::maybe::Maybe;
    ///
    /// let opt_some = Some(42);
    /// let maybe_just = Maybe::from(opt_some);
    /// assert!(maybe_just.is_just());
    ///
    /// let opt_none: Option<i32> = None;
    /// let maybe_nothing = Maybe::from(opt_none);
    /// assert!(maybe_nothing.is_nothing());
    /// ```
    fn from(opt: Option<T>) -> Self {
        match opt {
            Some(value) => Maybe::Just(value),
            None => Maybe::Nothing,
        }
    }
}

/// Implementation of Identity trait for Maybe
impl<T> Identity for Maybe<T> {
    /// Gets a reference to the contained value.
    ///
    /// # Panics
    ///
    /// Panics if the value is `Nothing`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::maybe::Maybe;
    /// use rustica::traits::identity::Identity;
    ///
    /// let just_five = Maybe::Just(5);
    /// assert_eq!(*just_five.value(), 5);
    /// ```
    fn value(&self) -> &Self::Source {
        match self {
            Maybe::Just(x) => x,
            Maybe::Nothing => panic!("Tried to get value from Nothing!"),
        }
    }

    fn into_value(self) -> Self::Source {
        match self {
            Maybe::Just(x) => x,
            Maybe::Nothing => panic!("Tried to get value from Nothing!"),
        }
    }

    fn pure_identity<A>(value: A) -> Self::Output<A>
        where
            Self::Output<A>: Identity {
        Maybe::Just(value)
    }
}

/// Implementation of Composable trait for Maybe
impl<T> Composable for Maybe<T> {
    /// Composes two functions.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::maybe::Maybe;
    /// use rustica::prelude::*;
    /// use rustica::traits::composable::Composable;
    ///
    /// let add_one = |x: i32| x + 1;
    /// let double = |x: i32| x * 2;
    /// let composed = <Maybe<i32> as Composable>::compose(&add_one, &double);
    ///
    /// let result = Maybe::Just(5).bind(&|x: &i32| Maybe::Just(composed(*x)));
    /// assert!(result.is_just());
    /// assert_eq!(result.unwrap(), 12);  // (5 + 1) * 2 = 12
    /// ```
    fn compose<U, V, F, G>(f: F, g: G) -> impl Fn(Self::Source) -> V
    where
        F: Fn(Self::Source) -> U,
        G: Fn(U) -> V,
    {
        move |x| g(f(x))
    }
}