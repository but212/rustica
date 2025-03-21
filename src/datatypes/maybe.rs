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
//! # Memory Optimization
//!
//! `Maybe<T>` has the same memory layout as `Option<T>` and takes advantage of the
//! [null pointer optimization](https://doc.rust-lang.org/std/option/index.html#representation).
//! This means that for types like `Box<T>`, `Vec<T>`, `String`, etc., `Maybe<T>` doesn't
//! require any additional memory beyond what's needed to store `T`.
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

use crate::traits::applicative::Applicative;
use crate::traits::composable::Composable;
use crate::traits::functor::Functor;
use crate::traits::hkt::HKT;
use crate::traits::identity::Identity;
use crate::traits::monad::Monad;
use crate::traits::pure::Pure;
use std::marker::PhantomData;

/// A type that represents an optional value, optimized with null pointer optimization.
///
/// `Maybe<T>` is an enum that can be either `Just(T)` containing a value, or `Nothing`
/// representing the absence of a value. It has the same memory layout as `Option<T>`.
///
/// # Memory Optimization
///
/// This type uses Rust's null pointer optimization. For types like `Box<T>`, `Vec<T>`,
/// `String`, etc. that can never be null, the `Nothing` variant doesn't require any
/// additional memory. The compiler optimizes it to use the null pointer representation.
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
#[derive(Copy, Clone, Eq, Debug, Hash, PartialEq, PartialOrd, Ord)]
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
    #[inline]
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
    #[inline]
    pub fn is_nothing(&self) -> bool {
        matches!(self, Maybe::Nothing)
    }

    /// Converts from `Option<T>` to `Maybe<T>`.
    ///
    /// `Some(x)` is converted to `Just(x)`, and `None` is converted to `Nothing`.
    /// This is a zero-cost conversion due to the same memory layout.
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
    #[inline]
    pub fn from_option(opt: Option<T>) -> Self {
        match opt {
            Some(x) => Maybe::Just(x),
            None => Maybe::Nothing,
        }
    }

    /// Converts from `Maybe<T>` to `Option<T>`.
    ///
    /// `Just(x)` is converted to `Some(x)`, and `Nothing` is converted to `None`.
    /// This is a zero-cost conversion due to the same memory layout.
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
    #[inline]
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
    #[inline]
    pub fn unwrap(self) -> T {
        match self {
            Maybe::Just(val) => val,
            Maybe::Nothing => panic!("called `Maybe::unwrap()` on a `Nothing` value"),
        }
    }

    /// Maps a `Maybe<T>` to `Maybe<U>` by applying a function to the contained value.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::maybe::Maybe;
    ///
    /// let maybe_some = Maybe::Just(41);
    /// let maybe_none: Maybe<i32> = Maybe::Nothing;
    ///
    /// let incremented = maybe_some.map(|x| x + 1);
    /// let still_none = maybe_none.map(|x| x + 1);
    ///
    /// assert_eq!(incremented.unwrap(), 42);
    /// assert!(still_none.is_nothing());
    /// ```
    #[inline]
    pub fn map<U, F>(self, f: F) -> Maybe<U>
    where
        F: FnOnce(T) -> U,
    {
        match self {
            Maybe::Just(val) => Maybe::Just(f(val)),
            Maybe::Nothing => Maybe::Nothing,
        }
    }

    /// Returns the provided default value if `Nothing`, or applies a function to the contained value.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::maybe::Maybe;
    ///
    /// let maybe_some = Maybe::Just(41);
    /// let maybe_none: Maybe<i32> = Maybe::Nothing;
    ///
    /// let incremented = maybe_some.map_or(0, |x| x + 1);
    /// let default = maybe_none.map_or(0, |x| x + 1);
    ///
    /// assert_eq!(incremented, 42);
    /// assert_eq!(default, 0);
    /// ```
    #[inline]
    pub fn map_or<U, F>(self, default: U, f: F) -> U
    where
        F: FnOnce(T) -> U,
    {
        match self {
            Maybe::Just(val) => f(val),
            Maybe::Nothing => default,
        }
    }

    /// Returns the result of applying `f` to the contained value if `Just`,
    /// otherwise returns the result of evaluating `default`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::maybe::Maybe;
    ///
    /// let maybe_some = Maybe::Just(41);
    /// let maybe_none: Maybe<i32> = Maybe::Nothing;
    ///
    /// let incremented = maybe_some.map_or_else(|| 0, |x| x + 1);
    /// let default = maybe_none.map_or_else(|| 0, |x| x + 1);
    ///
    /// assert_eq!(incremented, 42);
    /// assert_eq!(default, 0);
    /// ```
    #[inline]
    pub fn map_or_else<U, D, F>(self, default: D, f: F) -> U
    where
        D: FnOnce() -> U,
        F: FnOnce(T) -> U,
    {
        match self {
            Maybe::Just(val) => f(val),
            Maybe::Nothing => default(),
        }
    }
}

// Use a specialized empty struct to enable null pointer optimization
// This is a marker type to verify null pointer optimization is enabled
#[allow(dead_code)]
struct MaybeNullTestStruct<T>(PhantomData<T>);

// Assert that Maybe<Box<T>> has the same size as Box<T>, confirming null pointer optimization works
const _: () = assert!(std::mem::size_of::<Maybe<Box<i32>>>() == std::mem::size_of::<Box<i32>>());

impl<T> HKT for Maybe<T> {
    type Source = T;
    type Output<U> = Maybe<U>;
}

impl<T> Pure for Maybe<T> {
    #[inline]
    fn pure<U: Clone>(value: &U) -> Self::Output<U> {
        Maybe::Just(value.clone())
    }
}

impl<T> Functor for Maybe<T> {
    #[inline]
    fn fmap<B, F>(&self, f: F) -> Self::Output<B>
    where
        F: Fn(&Self::Source) -> B,
    {
        match self {
            Maybe::Just(a) => Maybe::Just(f(a)),
            Maybe::Nothing => Maybe::Nothing,
        }
    }

    #[inline]
    fn fmap_owned<B, F>(self, f: F) -> Self::Output<B>
    where
        F: FnOnce(Self::Source) -> B,
        Self: Sized,
    {
        match self {
            Maybe::Just(a) => Maybe::Just(f(a)),
            Maybe::Nothing => Maybe::Nothing,
        }
    }
}

impl<T> Applicative for Maybe<T> {
    #[inline]
    fn apply<B, F>(&self, f: &Self::Output<F>) -> Self::Output<B>
    where
        F: Fn(&Self::Source) -> B,
    {
        match (self, f) {
            (Maybe::Just(x), Maybe::Just(g)) => Maybe::Just(g(x)),
            _ => Maybe::Nothing,
        }
    }

    #[inline]
    fn lift2<B, C, F>(&self, b: &Self::Output<B>, f: F) -> Self::Output<C>
    where
        F: Fn(&Self::Source, &B) -> C,
    {
        match (self, b) {
            (Maybe::Just(a), Maybe::Just(b)) => Maybe::Just(f(a, b)),
            _ => Maybe::Nothing,
        }
    }

    #[inline]
    fn lift3<B, C, D, F>(&self, b: &Self::Output<B>, c: &Self::Output<C>, f: F) -> Self::Output<D>
    where
        F: Fn(&Self::Source, &B, &C) -> D,
    {
        match (self, b, c) {
            (Maybe::Just(a), Maybe::Just(b), Maybe::Just(c)) => Maybe::Just(f(a, b, c)),
            _ => Maybe::Nothing,
        }
    }

    #[inline]
    fn apply_owned<B, F>(self, f: Self::Output<F>) -> Self::Output<B>
    where
        F: FnOnce(Self::Source) -> B,
        Self: Sized,
    {
        match (self, f) {
            (Maybe::Just(x), Maybe::Just(g)) => Maybe::Just(g(x)),
            _ => Maybe::Nothing,
        }
    }

    #[inline]
    fn lift2_owned<B, C, F>(self, b: Self::Output<B>, f: F) -> Self::Output<C>
    where
        F: FnOnce(Self::Source, B) -> C,
        Self: Sized,
    {
        match (self, b) {
            (Maybe::Just(a), Maybe::Just(b)) => Maybe::Just(f(a, b)),
            _ => Maybe::Nothing,
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
        F: FnOnce(Self::Source, B, C) -> D,
        Self: Sized,
    {
        match (self, b, c) {
            (Maybe::Just(a), Maybe::Just(b), Maybe::Just(c)) => Maybe::Just(f(a, b, c)),
            _ => Maybe::Nothing,
        }
    }
}

impl<T> Monad for Maybe<T> {
    #[inline]
    fn bind<U, F>(&self, f: F) -> Self::Output<U>
    where
        F: Fn(&Self::Source) -> Self::Output<U>,
    {
        match self {
            Maybe::Just(x) => f(x),
            Maybe::Nothing => Maybe::Nothing,
        }
    }

    #[inline]
    fn bind_owned<U, F>(self, f: F) -> Self::Output<U>
    where
        F: FnOnce(Self::Source) -> Self::Output<U>,
        Self: Sized,
    {
        match self {
            Maybe::Just(x) => f(x),
            Maybe::Nothing => Maybe::Nothing,
        }
    }

    #[inline]
    fn join<U>(&self) -> Self::Output<U>
    where
        Self::Source: Clone + Into<Self::Output<U>>,
    {
        match self {
            Maybe::Just(m) => m.clone().into(),
            Maybe::Nothing => Maybe::Nothing,
        }
    }

    #[inline]
    fn join_owned<U>(self) -> Self::Output<U>
    where
        Self::Source: Into<Self::Output<U>>,
        Self: Sized,
    {
        match self {
            Maybe::Just(m) => m.into(),
            Maybe::Nothing => Maybe::Nothing,
        }
    }
}

impl<T> FromIterator<T> for Maybe<T> {
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        let mut iter = iter.into_iter();
        iter.next().map_or(Maybe::Nothing, Maybe::Just)
    }
}

impl<T> From<Option<T>> for Maybe<T> {
    #[inline]
    fn from(opt: Option<T>) -> Self {
        match opt {
            Some(x) => Maybe::Just(x),
            None => Maybe::Nothing,
        }
    }
}

impl<T> From<Maybe<T>> for Option<T> {
    #[inline]
    fn from(maybe: Maybe<T>) -> Self {
        match maybe {
            Maybe::Just(x) => Some(x),
            Maybe::Nothing => None,
        }
    }
}

impl<T> Identity for Maybe<T> {
    #[inline]
    fn value(&self) -> &Self::Source {
        match self {
            Maybe::Just(v) => v,
            Maybe::Nothing => panic!("Called `Identity::value()` on a `Nothing` value"),
        }
    }

    #[inline]
    fn into_value(self) -> Self::Source {
        match self {
            Maybe::Just(v) => v,
            Maybe::Nothing => panic!("Called `Identity::into_value()` on a `Nothing` value"),
        }
    }

    #[inline]
    fn pure_identity<A>(value: A) -> Self::Output<A> {
        Maybe::Just(value)
    }
}

impl<T> Composable for Maybe<T> {}

impl<T> Default for Maybe<T> {
    #[inline]
    fn default() -> Self {
        Maybe::Nothing
    }
}
