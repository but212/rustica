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

use crate::traits::alternative::Alternative;
use crate::traits::applicative::Applicative;
use crate::traits::comonad::Comonad;
use crate::traits::composable::Composable;
use crate::traits::functor::Functor;
use crate::traits::hkt::HKT;
use crate::traits::identity::Identity;
use crate::traits::monad::Monad;
use crate::traits::monad_plus::MonadPlus;
use crate::traits::pure::Pure;
use crate::utils::error_utils::{AppError, WithError};
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

/// Error type for Maybe operations
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum MaybeError {
    /// Error raised when attempting to access a value that doesn't exist
    ValueNotPresent,
    /// Error with a custom message
    Custom(String),
}

impl std::fmt::Display for MaybeError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            MaybeError::ValueNotPresent => write!(f, "Attempted to access a value in a Nothing"),
            MaybeError::Custom(msg) => write!(f, "{}", msg),
        }
    }
}

impl std::error::Error for MaybeError {}

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
    pub const fn is_just(&self) -> bool {
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
    pub const fn is_nothing(&self) -> bool {
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

    /// Converts this Maybe to a Result with the specified error.
    ///
    /// * `Just(x)` is converted to `Ok(x)`.
    /// * `Nothing` is converted to `Err(error)`.
    ///
    /// # Arguments
    ///
    /// * `error` - The error to use if this is `Nothing`
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::maybe::Maybe;
    ///
    /// let maybe_just = Maybe::Just(42);
    /// let maybe_nothing: Maybe<i32> = Maybe::Nothing;
    ///
    /// let ok_result = maybe_just.to_result("No value present");
    /// let err_result = maybe_nothing.to_result("No value present");
    ///
    /// assert_eq!(ok_result, Ok(42));
    /// assert_eq!(err_result, Err("No value present"));
    /// ```
    #[inline]
    pub fn to_result<E>(self, error: E) -> Result<T, E> {
        match self {
            Maybe::Just(x) => Ok(x),
            Maybe::Nothing => Err(error),
        }
    }

    /// Converts this Maybe to a Result with a standard MaybeError.
    ///
    /// * `Just(x)` is converted to `Ok(x)`.
    /// * `Nothing` is converted to `Err(MaybeError::ValueNotPresent)`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::maybe::{Maybe, MaybeError};
    ///
    /// let maybe_just = Maybe::Just(42);
    /// let maybe_nothing: Maybe<i32> = Maybe::Nothing;
    ///
    /// let ok_result = maybe_just.to_standard_result();
    /// let err_result = maybe_nothing.to_standard_result();
    ///
    /// assert_eq!(ok_result.is_ok(), true);
    /// assert_eq!(err_result.unwrap_err(), MaybeError::ValueNotPresent);
    /// ```
    #[inline]
    pub fn to_standard_result(self) -> Result<T, MaybeError> {
        self.to_result(MaybeError::ValueNotPresent)
    }

    /// Unwraps a maybe, yielding the content of a `Just`.
    ///
    /// # Errors
    ///
    /// If the value is a `Nothing`, this function generates and returns an error
    /// with a detailed message.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::maybe::Maybe;
    /// use rustica::utils::error_utils::ResultExt;
    ///
    /// let x = Maybe::Just("air");
    /// let result = x.try_unwrap().unwrap_or_default();
    /// assert_eq!(result, "air");
    ///
    /// let y: Maybe<&str> = Maybe::Nothing;
    /// let result = y.try_unwrap();
    /// assert!(result.is_err());
    /// ```
    #[inline]
    pub fn try_unwrap(self) -> Result<T, AppError<&'static str, &'static str>> {
        match self {
            Maybe::Just(val) => Ok(val),
            Maybe::Nothing => Err(AppError::with_context(
                "Cannot unwrap Nothing value",
                "Called `try_unwrap()` on a `Nothing` value",
            )),
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

    /// Unwraps a maybe, yielding the content of a `Just` or a default value.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::maybe::Maybe;
    ///
    /// let just = Maybe::Just(42);
    /// let nothing: Maybe<i32> = Maybe::Nothing;
    ///
    /// assert_eq!(just.unwrap_or(0), 42);
    /// assert_eq!(nothing.unwrap_or(0), 0);
    /// ```
    #[inline]
    pub fn unwrap_or(self, default: T) -> T {
        match self {
            Maybe::Just(val) => val,
            Maybe::Nothing => default,
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
    /// let incremented = maybe_some.fmap_or(0, |x| x + 1);
    /// let default = maybe_none.fmap_or(0, |x| x + 1);
    ///
    /// assert_eq!(incremented, 42);
    /// assert_eq!(default, 0);
    /// ```
    #[inline]
    pub fn fmap_or<U, F>(self, default: U, f: F) -> U
    where
        F: FnOnce(T) -> U,
    {
        match self {
            Maybe::Just(val) => f(val),
            Maybe::Nothing => default,
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
        F: FnMut(&Self::Source) -> B,
    {
        self.into_iter()
            .map(f)
            .next()
            .map_or(Maybe::Nothing, Maybe::Just)
    }

    #[inline]
    fn fmap_owned<B, F>(self, f: F) -> Self::Output<B>
    where
        F: FnMut(Self::Source) -> B,
        Self: Sized,
    {
        self.into_iter()
            .map(f)
            .next()
            .map_or(Maybe::Nothing, Maybe::Just)
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
        self, b: Self::Output<B>, c: Self::Output<C>, f: F,
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

impl<T: Clone> MonadPlus for Maybe<T> {
    #[inline]
    fn mzero<U: Clone>() -> Self::Output<U> {
        Maybe::Nothing
    }

    fn mplus(&self, other: &Self) -> Self {
        match (self, other) {
            (Maybe::Just(_), _) => self.clone(),
            (Maybe::Nothing, Maybe::Just(_)) => other.clone(),
            _ => Maybe::Nothing,
        }
    }

    fn mplus_owned(self, other: Self) -> Self
    where
        Self: Sized,
    {
        match (self.clone(), other.clone()) {
            (Maybe::Just(_), _) => self,
            (Maybe::Nothing, Maybe::Just(_)) => other,
            _ => Maybe::Nothing,
        }
    }
}

impl<T: Clone> Alternative for Maybe<T> {
    #[inline]
    fn empty_alt<U>() -> Self::Output<U> {
        Maybe::Nothing
    }

    #[inline]
    fn alt(&self, other: &Self) -> Self {
        match self {
            Maybe::Just(_) => self.clone(),
            Maybe::Nothing => other.clone(),
        }
    }

    #[inline]
    fn guard(condition: bool) -> Self::Output<()> {
        if condition {
            Maybe::Just(())
        } else {
            Maybe::Nothing
        }
    }

    #[inline]
    fn many(&self) -> Self::Output<Vec<Self::Source>>
    where
        Self::Source: Clone,
    {
        match self {
            Maybe::Just(x) => Maybe::Just(vec![x.clone()]),
            Maybe::Nothing => Maybe::Nothing,
        }
    }
}

impl<T> FromIterator<T> for Maybe<T> {
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        iter.into_iter().next().map_or(Maybe::Nothing, Maybe::Just)
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

impl<T> WithError<MaybeError> for Maybe<T> {
    type Success = T;
    type ErrorOutput<G> = Maybe<G>;

    /// maybe does not store errors, so this function does nothing
    fn fmap_error<F, G>(self, f: F) -> Self::ErrorOutput<G>
    where
        F: Fn(MaybeError) -> G,
        G: Clone,
    {
        match self {
            Maybe::Just(_) => Maybe::Just(f(MaybeError::ValueNotPresent)),
            Maybe::Nothing => Maybe::Nothing,
        }
    }

    fn to_result(self) -> Result<Self::Success, MaybeError> {
        match self {
            Maybe::Just(x) => Ok(x),
            Maybe::Nothing => Err(MaybeError::ValueNotPresent),
        }
    }
}

impl<T, E> From<Result<T, E>> for Maybe<T> {
    #[inline]
    fn from(result: Result<T, E>) -> Self {
        match result {
            Ok(value) => Maybe::Just(value),
            Err(_) => Maybe::Nothing,
        }
    }
}

/// Extension trait for Maybe that provides additional error handling methods
pub trait MaybeExt<T> {
    /// Converts a Maybe to a Result with the specified error
    fn to_result<E>(self, err: E) -> Result<T, E>;

    /// Provides a safe unwrapping mechanism that returns a Result
    fn try_unwrap(self) -> Result<T, AppError<&'static str, &'static str>>;
}

impl<T> MaybeExt<T> for Maybe<T> {
    #[inline]
    fn to_result<E>(self, err: E) -> Result<T, E> {
        match self {
            Maybe::Just(x) => Ok(x),
            Maybe::Nothing => Err(err),
        }
    }

    #[inline]
    fn try_unwrap(self) -> Result<T, AppError<&'static str, &'static str>> {
        match self {
            Maybe::Just(val) => Ok(val),
            Maybe::Nothing => Err(AppError::with_context(
                "Cannot unwrap Nothing value",
                "Called `try_unwrap()` on a `Nothing` value",
            )),
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

impl<T: Clone> Comonad for Maybe<T> {
    #[inline]
    fn extract(&self) -> T {
        match self {
            Maybe::Just(v) => v.clone(),
            Maybe::Nothing => panic!("Called `Comonad::extract()` on a `Nothing` value"),
        }
    }

    #[inline]
    fn duplicate(&self) -> Self {
        self.clone()
    }

    #[inline]
    fn extend<U, F>(&self, f: F) -> Self::Output<U>
    where
        F: Fn(&Self) -> U,
    {
        match self {
            Maybe::Just(_) => Maybe::Just(f(self)),
            Maybe::Nothing => Maybe::Nothing,
        }
    }
}

// Iterator and IntoIterator implementations for Maybe<T>

impl<T> IntoIterator for Maybe<T> {
    type Item = T;
    type IntoIter = std::option::IntoIter<T>;

    fn into_iter(self) -> Self::IntoIter {
        match self {
            Maybe::Just(val) => Some(val).into_iter(),
            Maybe::Nothing => None.into_iter(),
        }
    }
}

impl<'a, T> IntoIterator for &'a Maybe<T> {
    type Item = &'a T;
    type IntoIter = std::slice::Iter<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        match self {
            Maybe::Just(ref val) => std::slice::from_ref(val).iter(),
            Maybe::Nothing => [].iter(),
        }
    }
}

impl<'a, T> IntoIterator for &'a mut Maybe<T> {
    type Item = &'a mut T;
    type IntoIter = std::slice::IterMut<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        match self {
            Maybe::Just(ref mut val) => std::slice::from_mut(val).iter_mut(),
            Maybe::Nothing => [].iter_mut(),
        }
    }
}
