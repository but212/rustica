//! # Maybe (`Maybe<T>`)
//!
//! The Maybe monad represents computations which may fail or return a value.
//!
//! `Maybe<T>` is an enum that can be either `Just(T)` containing a value, or `Nothing`
//! representing the absence of a value. This is similar to Rust's built-in `Option<T>` type,
//! but with additional monadic operations.
//!
//! ## Quick Start
//!
//! Get started with Maybe in 30 seconds:
//!
//! ```rust
//! use rustica::datatypes::maybe::Maybe;
//! use rustica::traits::functor::Functor;
//! use rustica::traits::monad::Monad;
//!
//! // Create a Maybe value
//! let value = Maybe::Just(10);
//!
//! // Map over it
//! let doubled = value.fmap(|x| x * 2);
//!
//! // Chain operations
//! let result = value
//!     .bind(|x| Maybe::Just(x + 5))
//!     .bind(|x| Maybe::Just(x * 2));
//!
//! assert_eq!(result, Maybe::Just(30));
//!
//! // Handle None cases gracefully
//! let none: Maybe<i32> = Maybe::Nothing;
//! let result = none.fmap(|x| x * 2);
//! assert_eq!(result, Maybe::Nothing);
//! ```
//!
//! ## Functional Programming Context
//!
//! The Maybe type (also known as Option in some languages) is a fundamental abstraction in functional
//! programming that elegantly handles the concept of optional values without resorting to null
//! references. It represents one of the simplest and most commonly used monads in functional programming.
//!
//! Key aspects of Maybe in functional programming:
//!
//! - **Nullability Alternative**: Provides a type-safe way to represent the possible absence of a value,
//!   eliminating null pointer exceptions/panics common in imperative programming
//!
//! - **Error Handling Pattern**: Offers a lightweight approach for handling failures or computations
//!   that might not produce a result
//!
//! - **Compositional Logic**: Enables clean composition of operations that might fail without
//!   explicit conditional statements
//!
//! Similar constructs in other functional languages include:
//!
//! - Haskell's `Maybe` type with `Just` and `Nothing` constructors
//! - Scala's `Option[T]` with `Some[T]` and `None` cases
//! - OCaml's `option` type with `Some` and `None` variants
//! - F#'s `Option<'T>` with `Some` and `None` cases
//! - TypeScript's `Option<T>` in fp-ts
//!
//! # Key Features
//!
//! - **Failure Handling**: Represents computations that might not return a value
//! - **Composition**: Chain operations together without explicit null checks
//!
//! # Common Use Cases
//!
//! - Representing optional values without using `null`
//! - Chaining operations that might fail
//! - Transforming optional values without unwrapping
//!
//! ## Performance Characteristics
//!
//! ### Memory Usage
//!
//! - **Optimized Size**: Takes advantage of the [null pointer optimization](https://doc.rust-lang.org/std/option/index.html#representation)
//!   for types like `Box<T>`, `Vec<T>`, `String`, etc., meaning `Maybe<T>` doesn't require any
//!   additional memory beyond what's needed to store `T`
//! - **Zero-Copy Design**: Memory layout is identical to `Option<T>` with the same optimizations
//! - **Enum Representation**: For simple types, size is typically `size_of::<T>() + size_of::<u8>()`
//!   for tag discrimination (possibly with padding)
//! - **Cloning Impact**: Cloning a `Just` value costs as much as cloning the inner value
//!   while cloning `Nothing` is free
//!
//! ### Time Complexity
//!
//! - **Construction**: O(1) - Both `Just` and `Nothing` constructors are constant time
//! - **Predicates** (`is_just`, `is_nothing`): O(1) - Simple pattern matching operations
//! - **Transformations** (`fmap`, `bind`):
//!   - O(1) for `Nothing` cases (short-circuits without evaluating function)
//!   - O(f) for `Just` cases where `f` is the time complexity of the applied function
//! - **Conversions** (to/from Option, Result): O(1) - Zero-cost due to identical memory layout
//! - **Unwrapping**: O(1) - Direct access to inner value with minimal overhead
//!
//! ### Concurrency
//!
//! - **Thread Safety**: `Maybe<T>` is `Send` and `Sync` when `T` is `Send` and `Sync`
//! - **Immutability**: Operations produce new instances rather than modifying existing ones
//! - **Lock-Free**: No internal synchronization or locks are used
//!
//! # Relationship to Rust's Option
//!
//! `Maybe<T>` is functionally equivalent to Rust's `Option<T>`, but provides
//! additional monadic operations. Conversion methods are provided to interoperate
//! with `Option<T>`.
//!
//! ## Basic Usage
//!
//! ```rust
//! use rustica::datatypes::maybe::Maybe;
//! use rustica::traits::functor::Functor;
//! use rustica::traits::applicative::Applicative;
//! use rustica::traits::monad::Monad;
//!
//! // Creating Maybe values
//! let just_value = Maybe::Just(42);
//! let nothing_value: Maybe<i32> = Maybe::Nothing;
//!
//! // Checking which variant we have
//! assert!(just_value.is_just());
//! assert!(nothing_value.is_nothing());
//!
//! // Converting to and from Option
//! let option_some = just_value.to_option();  // Some(42)
//! let maybe_from_option = Maybe::from_option(Some(100));  // Just(100)
//!
//! // Safely extracting values with defaults
//! assert_eq!(just_value.unwrap_or(0), 42);
//! assert_eq!(nothing_value.unwrap_or(0), 0);
//!
//! // Transforming values with fmap
//! let doubled = just_value.fmap(|x| x * 2);  // Just(84)
//! let doubled_nothing = nothing_value.fmap(|x| x * 2);  // Nothing
//!
//! // Chaining operations with bind
//! let safe_divide = |x: &i32, y: &i32| -> Maybe<i32> {
//!     if *y == 0 {
//!         Maybe::Nothing
//!     } else {
//!         Maybe::Just(x / y)
//!     }
//! };
//!
//! let result1 = Maybe::Just(10).bind(|x| safe_divide(x, &2));  // Just(5)
//! let result2 = Maybe::Just(10).bind(|x| safe_divide(x, &0));  // Nothing
//!
//! // Short-circuiting behavior
//! let combined = Maybe::Just(10)
//!     .bind(|x| safe_divide(x, &2))  // Just(5)
//!     .bind(|x| safe_divide(x, &0))  // Nothing
//!     .bind(|x| Maybe::Just(x + 1)); // Nothing (never executes this function)
//!
//! assert_eq!(combined, Maybe::Nothing);
//! ```
//!
//! ## Type Class Implementations
//!
//! `Maybe<T>` implements several important type classes:
//!
//! - **Functor**: Maps a function over a `Maybe` value
//! - **Applicative**: Applies a function inside a `Maybe` to a value inside another `Maybe`
//! - **Monad**: Allows sequencing of `Maybe` operations with dependencies
//! ### Functor Laws
//!
//! 1. **Identity Law**: `fmap id = id`
//! 2. **Composition Law**: `fmap (f . g) = fmap f . fmap g`
//!
//! ### Monad Laws
//!
//! 1. **Left Identity**: `return a >>= f = f a`
//! 2. **Right Identity**: `m >>= return = m`
//! 3. **Associativity**: `(m >>= f) >>= g = m >>= (\x -> f x >>= g)`
//!
//! ### Alternative/MonadPlus Laws
//!
//! 1. **Left Identity**: `mzero `mplus` m = m`
//! 2. **Right Identity**: `m `mplus` mzero = m`
//! 3. **Associativity**: `(m `mplus` n) >>= f = (m >>= f) `mplus` (n >>= f)`
//!
//! # Examples
//!
//! Refer to the documentation for specific functions to see practical examples demonstrating:
//! - Type class law compliance
//! - Usage patterns
//! - Performance considerations
//! - Error handling approaches
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
use quickcheck::{Arbitrary, Gen};
use std::marker::PhantomData;
// use std::ops::{ControlFlow, FromResidual, Try};

/// A type that represents an optional value, optimized with null pointer optimization.
///
/// `Maybe<T>` is an enum that can be either `Just(T)` containing a value, or `Nothing`
/// representing the absence of a value. It has the same memory layout as `Option<T>`.
///
/// # Performance Characteristics
///
/// ## Time Complexity
///
/// * Construction: O(1) - Both variants are constant time to construct
/// * Access: O(1) - Checking variant and accessing value is constant time
/// * Pattern matching: O(1) - Direct enum discrimination
///
/// ## Memory Optimization
///
/// This type uses Rust's null pointer optimization. For types like `Box<T>`, `Vec<T>`,
/// `String`, etc. that can never be null, the `Nothing` variant doesn't require any
/// additional memory. The compiler optimizes it to use the null pointer representation.
///
/// Memory layout is identical to `Option<T>` in Rust's standard library, making
/// conversions between the two zero-cost.
///
/// # Type Parameters
///
/// * `T` - The type of the value that might be contained
///
/// # When to Use
///
/// Use `Maybe<T>` when you need:
///
/// * To represent an optional value in a functional programming style
/// * To chain operations that might fail without verbose error handling
/// * To leverage monadic interfaces for cleaner composition
///
/// # Examples
///
/// Basic usage with pattern matching:
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
///
/// // Conditional execution with if-let
/// if let Maybe::Just(value) = just_five {
///     println!("Found a value: {}", value);
/// }
/// ```
///
/// Combining multiple optional values:
///
/// ```rust
/// use rustica::datatypes::maybe::Maybe;
/// use rustica::traits::functor::Functor;
/// use rustica::traits::applicative::Applicative;
///
/// fn add(a: i32, b: i32) -> i32 { a + b }
///
/// let a = Maybe::Just(5);
/// let b = Maybe::Just(10);
///
/// // Using lift2 from the Applicative trait to combine values
/// let sum = Maybe::<i32>::lift2(|x, y| *x + *y, &a, &b);
/// assert_eq!(sum, Maybe::Just(15));
///
/// // If any value is Nothing, the result is Nothing
/// let c: Maybe<i32> = Maybe::Nothing;
/// let partial_sum = Maybe::<i32>::lift2(|x, y| *x + *y, &a, &c);
/// assert_eq!(partial_sum, Maybe::Nothing);
/// ```
#[derive(Copy, Clone, Eq, Debug, Hash, PartialEq, PartialOrd, Ord)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
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
            MaybeError::Custom(msg) => write!(f, "{msg}"),
        }
    }
}

impl std::error::Error for MaybeError {}

impl<T> Maybe<T> {
    /// Creates a `Maybe` with a value (alias for `Just`).
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::maybe::Maybe;
    ///
    /// let value = Maybe::some(42);
    /// assert_eq!(value, Maybe::Just(42));
    /// ```
    #[inline]
    pub const fn some(value: T) -> Self {
        Maybe::Just(value)
    }

    /// Creates a `Maybe` without a value (alias for `Nothing`).
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::maybe::Maybe;
    ///
    /// let value: Maybe<i32> = Maybe::none();
    /// assert_eq!(value, Maybe::Nothing);
    /// ```
    #[inline]
    pub const fn none() -> Self {
        Maybe::Nothing
    }

    /// Creates a `Maybe` based on a condition.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::maybe::Maybe;
    ///
    /// let value = Maybe::when(true, 42);
    /// assert_eq!(value, Maybe::Just(42));
    ///
    /// let empty = Maybe::when(false, 42);
    /// assert_eq!(empty, Maybe::Nothing);
    /// ```
    #[inline]
    pub fn when(condition: bool, value: T) -> Self {
        if condition {
            Maybe::Just(value)
        } else {
            Maybe::Nothing
        }
    }

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

    /// Converts a `Maybe<T>` to an `Option<&T>`.
    ///
    /// Converts `Just(x)` to `Some(&x)` and `Nothing` to `None`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::maybe::Maybe;
    ///
    /// let maybe_just = Maybe::Just(42);
    /// let maybe_nothing: Maybe<i32> = Maybe::Nothing;
    ///
    /// assert_eq!(maybe_just.as_ref(), Some(&42));
    /// assert_eq!(maybe_nothing.as_ref(), None);
    /// ```
    #[inline]
    pub const fn as_ref(&self) -> Option<&T> {
        match *self {
            Maybe::Just(ref x) => Some(x),
            Maybe::Nothing => None,
        }
    }

    /// Unwraps a maybe, yielding the content of a `Just` or computing a default.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::maybe::Maybe;
    ///
    /// let just = Maybe::Just(42);
    /// let nothing: Maybe<i32> = Maybe::Nothing;
    ///
    /// assert_eq!(just.unwrap_or_else(|| 10), 42);
    /// assert_eq!(nothing.unwrap_or_else(|| 10), 10);
    /// ```
    #[inline]
    pub fn unwrap_or_else<F>(self, f: F) -> T
    where
        F: FnOnce() -> T,
    {
        match self {
            Maybe::Just(val) => val,
            Maybe::Nothing => f(),
        }
    }

    /// Returns `Nothing` if the value does not satisfy the predicate.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::maybe::Maybe;
    ///
    /// let maybe_some = Maybe::Just(4);
    /// let maybe_none: Maybe<i32> = Maybe::Nothing;
    ///
    /// assert_eq!(maybe_some.filter(|&x| x > 2), Maybe::Just(4));
    /// assert_eq!(maybe_some.filter(|&x| x > 5), Maybe::Nothing);
    /// assert_eq!(maybe_none.filter(|&x| x > 2), Maybe::Nothing);
    /// ```
    #[inline]
    pub fn filter<P>(self, predicate: P) -> Self
    where
        P: FnOnce(&T) -> bool,
    {
        match self {
            Maybe::Just(ref value) if predicate(value) => self,
            _ => Maybe::Nothing,
        }
    }

    /// Calls the provided closure with the contained value if `Just`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::maybe::Maybe;
    ///
    /// let just = Maybe::Just(42);
    /// let nothing: Maybe<i32> = Maybe::Nothing;
    ///
    /// just.tap(|x| println!("Got value: {}", x));
    /// nothing.tap(|x| println!("Got value: {}", x)); // Does nothing
    /// ```
    #[inline]
    pub fn tap<F>(self, f: F) -> Self
    where
        F: FnOnce(&T),
    {
        if let Maybe::Just(ref value) = self {
            f(value);
        }
        self
    }

    /// Returns an iterator over the possibly contained value.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::maybe::Maybe;
    ///
    /// let just = Maybe::Just(42);
    /// let nothing: Maybe<i32> = Maybe::Nothing;
    ///
    /// assert_eq!(just.iter().collect::<Vec<_>>(), vec![&42]);
    /// assert_eq!(nothing.iter().collect::<Vec<&i32>>(), Vec::<&i32>::new());
    /// ```
    #[inline]
    pub fn iter(&self) -> impl Iterator<Item = &T> {
        self.as_ref().into_iter()
    }

    /// Returns a mutable iterator over the possibly contained value.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::maybe::Maybe;
    ///
    /// let mut just = Maybe::Just(42);
    ///
    /// for value in just.iter_mut() {
    ///     *value += 10;
    /// }
    ///
    /// assert_eq!(just, Maybe::Just(52));
    /// ```
    #[inline]
    pub fn iter_mut(&mut self) -> impl Iterator<Item = &mut T> {
        match self {
            Maybe::Just(x) => Some(x).into_iter(),
            Maybe::Nothing => None.into_iter(),
        }
    }

    /// Converts this Maybe to a Vec containing 0 or 1 elements.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::maybe::Maybe;
    ///
    /// let just = Maybe::Just(42);
    /// let nothing: Maybe<i32> = Maybe::Nothing;
    ///
    /// assert_eq!(just.to_vec(), vec![42]);
    /// assert_eq!(nothing.to_vec(), vec![]);
    /// ```
    #[inline]
    pub fn to_vec(self) -> Vec<T> {
        match self {
            Maybe::Just(x) => vec![x],
            Maybe::Nothing => vec![],
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
    /// Applies a function to the contained value (if any).
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::maybe::Maybe;
    /// use rustica::traits::functor::Functor;
    ///
    /// let just = Maybe::Just(5);
    /// let nothing: Maybe<i32> = Maybe::Nothing;
    ///
    /// assert_eq!(just.fmap(|x| x * 2), Maybe::Just(10));
    /// assert_eq!(nothing.fmap(|x| x * 2), Maybe::Nothing);
    /// ```
    #[inline]
    fn fmap<B, F>(&self, f: F) -> Self::Output<B>
    where
        F: FnOnce(&Self::Source) -> B,
    {
        match self {
            Maybe::Just(x) => Maybe::Just(f(x)),
            Maybe::Nothing => Maybe::Nothing,
        }
    }

    /// Applies a function to the contained value (if any), taking ownership.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::maybe::Maybe;
    /// use rustica::traits::functor::Functor;
    ///
    /// let just = Maybe::Just(String::from("hello"));
    /// let nothing: Maybe<String> = Maybe::Nothing;
    ///
    /// assert_eq!(just.fmap_owned(|s| s.len()), Maybe::Just(5));
    /// assert_eq!(nothing.fmap_owned(|s| s.len()), Maybe::Nothing);
    /// ```
    #[inline]
    fn fmap_owned<B, F>(self, f: F) -> Self::Output<B>
    where
        F: FnOnce(Self::Source) -> B,
    {
        match self {
            Maybe::Just(x) => Maybe::Just(f(x)),
            Maybe::Nothing => Maybe::Nothing,
        }
    }
}

impl<T> Applicative for Maybe<T> {
    /// Applies a function wrapped in a `Maybe` to a value wrapped in a `Maybe`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::maybe::Maybe;
    /// use rustica::traits::applicative::Applicative;
    ///
    /// let just_fn = Maybe::Just(|x: &i32| x + 1);
    /// let just_val = Maybe::Just(1);
    /// let nothing_val: Maybe<i32> = Maybe::Nothing;
    ///
    /// assert_eq!(Applicative::apply(&just_fn, &just_val), Maybe::Just(2));
    /// assert_eq!(Applicative::apply(&just_fn, &nothing_val), Maybe::Nothing);
    /// ```
    #[inline]
    fn apply<A, B>(&self, value: &Self::Output<A>) -> Self::Output<B>
    where
        Self::Source: Fn(&A) -> B,
    {
        match (self, value) {
            (Maybe::Just(g), Maybe::Just(x)) => Maybe::Just(g(x)),
            _ => Maybe::Nothing,
        }
    }

    /// Lifts a binary function to work on two `Maybe` values.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::maybe::Maybe;
    /// use rustica::traits::applicative::Applicative;
    ///
    /// let a = Maybe::Just(5);
    /// let b = Maybe::Just(10);
    /// let c: Maybe<i32> = Maybe::Nothing;
    ///
    /// assert_eq!(Maybe::<i32>::lift2(|x, y| x + y, &a, &b), Maybe::Just(15));
    /// assert_eq!(Maybe::<i32>::lift2(|x, y| x + y, &a, &c), Maybe::Nothing);
    /// ```
    #[inline]
    fn lift2<A, B, C, F>(f: F, fa: &Self::Output<A>, fb: &Self::Output<B>) -> Self::Output<C>
    where
        F: Fn(&A, &B) -> C,
        Self: Sized,
    {
        match (fa, fb) {
            (Maybe::Just(a), Maybe::Just(b)) => Maybe::Just(f(a, b)),
            _ => Maybe::Nothing,
        }
    }

    #[inline]
    fn lift3<A, B, C, D, F>(
        f: F, fa: &Self::Output<A>, fb: &Self::Output<B>, fc: &Self::Output<C>,
    ) -> Self::Output<D>
    where
        F: Fn(&A, &B, &C) -> D,
        Self: Sized,
    {
        match (fa, fb, fc) {
            (Maybe::Just(a), Maybe::Just(b), Maybe::Just(c)) => Maybe::Just(f(a, b, c)),
            _ => Maybe::Nothing,
        }
    }

    /// Applies a function wrapped in a `Maybe` to a value wrapped in a `Maybe`, taking ownership.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::maybe::Maybe;
    /// use rustica::traits::applicative::Applicative;
    ///
    /// let just_fn = Maybe::Just(|s: String| s.len());
    /// let just_val = Maybe::Just(String::from("test"));
    ///
    /// assert_eq!(Applicative::apply_owned(just_fn, just_val), Maybe::Just(4));
    /// ```
    #[inline]
    fn apply_owned<U, B>(self, value: Self::Output<U>) -> Self::Output<B>
    where
        Self::Source: Fn(U) -> B,
        U: Clone,
        B: Clone,
    {
        match (self, value) {
            (Maybe::Just(f), Maybe::Just(x)) => Maybe::Just(f(x)),
            _ => Maybe::Nothing,
        }
    }

    /// Lifts a binary function to work on two `Maybe` values, taking ownership.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::maybe::Maybe;
    /// use rustica::traits::applicative::Applicative;
    ///
    /// let a = Maybe::Just(String::from("hello"));
    /// let b = Maybe::Just(String::from(" world"));
    ///
    /// assert_eq!(Maybe::<String>::lift2_owned(|s1, s2| s1 + &s2, a, b), Maybe::Just(String::from("hello world")));
    /// ```
    #[inline]
    fn lift2_owned<A, B, C, F>(f: F, fa: Self::Output<A>, fb: Self::Output<B>) -> Self::Output<C>
    where
        F: Fn(A, B) -> C,
        A: Clone,
        B: Clone,
        C: Clone,
        Self: Sized,
    {
        match (fa, fb) {
            (Maybe::Just(a), Maybe::Just(b)) => Maybe::Just(f(a, b)),
            _ => Maybe::Nothing,
        }
    }

    #[inline]
    fn lift3_owned<A, B, C, D, F>(
        f: F, fa: Self::Output<A>, fb: Self::Output<B>, fc: Self::Output<C>,
    ) -> Self::Output<D>
    where
        F: Fn(A, B, C) -> D,
        A: Clone,
        B: Clone,
        C: Clone,
        D: Clone,
        Self: Sized,
    {
        match (fa, fb, fc) {
            (Maybe::Just(a), Maybe::Just(b), Maybe::Just(c)) => Maybe::Just(f(a, b, c)),
            _ => Maybe::Nothing,
        }
    }
}

impl<T> Monad for Maybe<T> {
    /// Applies a function that returns a `Maybe` to the value inside this `Maybe`, if it exists.
    ///
    /// This is the core monadic operation (often called `flatMap` in other languages) that
    /// allows for sequencing computations that may fail.
    ///
    /// # Performance
    ///
    /// - Time Complexity: O(1) for `Nothing` case, O(f) for `Just` case where `f` is the
    ///   complexity of the provided function
    /// - Memory: No additional allocation beyond what the function `f` requires
    ///
    /// # Arguments
    ///
    /// * `f` - Function to apply to the value inside `Just`. This function must return another `Maybe`.
    ///
    /// # Returns
    ///
    /// - If `self` is `Just(x)`, returns the result of applying `f` to `x`
    /// - If `self` is `Nothing`, returns `Nothing` without calling `f`
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```rust
    /// use rustica::datatypes::maybe::Maybe;
    /// use rustica::traits::monad::Monad;
    ///
    /// // Simple transformation
    /// let m = Maybe::Just(5);
    /// let result = m.bind(|x| Maybe::Just(x * 2));
    /// assert_eq!(result, Maybe::Just(10));
    ///
    /// // Chaining multiple bind operations
    /// let result = Maybe::Just(5)
    ///     .bind(|x| Maybe::Just(x + 3))
    ///     .bind(|x| Maybe::Just(x * 2));
    /// assert_eq!(result, Maybe::Just(16));
    ///
    /// // Short-circuiting with Nothing
    /// let m: Maybe<i32> = Maybe::Nothing;
    /// let result = m.bind(|x| Maybe::Just(x * 2));
    /// assert_eq!(result, Maybe::Nothing);
    /// ```
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

    /// Applies a function that consumes and returns a `Maybe` to the value inside this `Maybe`, if it exists.
    ///
    /// This is similar to `bind` but consumes the `Maybe` and allows the function to consume the inner value.
    /// Useful when ownership of values needs to be transferred.
    ///
    /// # Performance
    ///
    /// - Time Complexity: O(1) for `Nothing` case, O(f) for `Just` case where `f` is the
    ///   complexity of the provided function
    /// - Memory: No additional allocation beyond what the function `f` requires
    ///   Potentially more efficient than `bind` when dealing with non-copyable types
    ///
    /// # Arguments
    ///
    /// * `f` - Function that consumes the value inside `Just`. This function must return another `Maybe`.
    ///
    /// # Returns
    ///
    /// - If `self` is `Just(x)`, returns the result of applying `f` to `x`
    /// - If `self` is `Nothing`, returns `Nothing` without calling `f`
    ///
    /// # Examples
    ///
    /// Basic usage with non-copyable types:
    ///
    /// ```rust
    /// use rustica::datatypes::maybe::Maybe;
    /// use rustica::traits::monad::Monad;
    ///
    /// // Using bind_owned with a String (non-Copy type)
    /// let m = Maybe::Just(String::from("hello"));
    ///
    /// // This consumes both the Maybe and the String
    /// let result = m.bind_owned(|s| {
    ///     if s.len() > 3 {
    ///         Maybe::Just(s + " world")
    ///     } else {
    ///         Maybe::Nothing
    ///     }
    /// });
    ///
    /// assert_eq!(result, Maybe::Just(String::from("hello world")));
    ///
    /// // The original m is moved and can't be used again
    /// // let invalid = m;  // This would cause a compile error
    /// ```
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

    /// Flattens a nested `Maybe` structure by one level.
    ///
    /// Takes a `Maybe<Maybe<T>>` and returns a `Maybe<T>`. This is useful when you have
    /// nested optional values and want to simplify the structure.
    ///
    /// # Performance
    ///
    /// - Time Complexity: O(1) - Only requires pattern matching and a clone operation
    /// - Memory: Requires cloning of the inner `Maybe` if `self` is `Just`
    ///
    /// # Type Parameters
    ///
    /// * `U` - The type contained in the inner `Maybe`
    ///
    /// # Returns
    ///
    /// - If `self` is `Just(Maybe::Just(x))`, returns `Maybe::Just(x)`
    /// - If `self` is `Just(Maybe::Nothing)`, returns `Maybe::Nothing`
    /// - If `self` is `Nothing`, returns `Maybe::Nothing`
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```rust
    /// use rustica::datatypes::maybe::Maybe;
    /// use rustica::traits::monad::Monad;
    ///
    /// // Create a nested Maybe
    /// let nested: Maybe<Maybe<i32>> = Maybe::Just(Maybe::Just(42));
    ///
    /// // Flatten it using join
    /// let flattened = nested.join();
    /// assert_eq!(flattened, Maybe::Just(42));
    ///
    /// // If the inner Maybe is Nothing, join returns Nothing
    /// let inner_nothing: Maybe<Maybe<i32>> = Maybe::Just(Maybe::Nothing);
    /// let result = inner_nothing.join();
    /// assert_eq!(result, Maybe::Nothing);
    ///
    /// // If the outer Maybe is Nothing, join returns Nothing
    /// let outer_nothing: Maybe<Maybe<i32>> = Maybe::Nothing;
    /// let result = outer_nothing.join();
    /// assert_eq!(result, Maybe::Nothing);
    /// ```
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

    /// Flattens a nested `Maybe` structure by one level, consuming both layers.
    ///
    /// Takes a `Maybe<Maybe<T>>` and returns a `Maybe<T>`. This is the ownership-taking
    /// version of `join` that avoids cloning.
    ///
    /// # Performance
    ///
    /// - Time Complexity: O(1) - Only requires pattern matching and conversion
    /// - Memory: More efficient than `join` as it avoids cloning the inner `Maybe`
    ///
    /// # Type Parameters
    ///
    /// * `U` - The type contained in the inner `Maybe`
    ///
    /// # Returns
    ///
    /// - If `self` is `Just(Maybe::Just(x))`, returns `Maybe::Just(x)`
    /// - If `self` is `Just(Maybe::Nothing)`, returns `Maybe::Nothing`
    /// - If `self` is `Nothing`, returns `Maybe::Nothing`
    ///
    /// # Examples
    ///
    /// Basic usage with owned values:
    ///
    /// ```rust
    /// use rustica::datatypes::maybe::Maybe;
    /// use rustica::traits::monad::Monad;
    ///
    /// // Create a nested Maybe with non-Copy type
    /// let nested: Maybe<Maybe<String>> = Maybe::Just(Maybe::Just(String::from("hello")));
    ///
    /// // Flatten it using join_owned to avoid cloning
    /// let flattened = nested.join_owned();
    /// assert_eq!(flattened, Maybe::Just(String::from("hello")));
    ///
    /// // The original nested value is consumed
    /// // let invalid = nested;  // This would cause a compile error
    /// ```
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
    /// Returns the identity of `mplus` (`Nothing`).
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::maybe::Maybe;
    /// use rustica::traits::monad_plus::MonadPlus;
    ///
    /// assert_eq!(Maybe::<i32>::mzero::<i32>(), Maybe::Nothing);
    /// ```
    #[inline]
    fn mzero<U: Clone>() -> Self::Output<U> {
        Maybe::Nothing
    }

    /// Chooses the first `Just` value, or `Nothing` if both are `Nothing`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::maybe::Maybe;
    /// use rustica::traits::monad_plus::MonadPlus;
    ///
    /// let just1 = Maybe::Just(1);
    /// let just2 = Maybe::Just(2);
    /// let nothing: Maybe<i32> = Maybe::Nothing;
    ///
    /// assert_eq!(just1.mplus(&just2), Maybe::Just(1));
    /// assert_eq!(just1.mplus(&nothing), Maybe::Just(1));
    /// assert_eq!(nothing.mplus(&just2), Maybe::Just(2));
    /// assert_eq!(nothing.mplus(&nothing), Maybe::Nothing);
    /// ```
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
        match &self {
            Maybe::Just(_) => self,
            Maybe::Nothing => other,
        }
    }
}

impl<T: Clone> Alternative for Maybe<T> {
    /// Returns the identity of `alt` (`Nothing`).
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::maybe::Maybe;
    /// use rustica::traits::alternative::Alternative;
    ///
    /// assert_eq!(Maybe::<i32>::empty_alt::<i32>(), Maybe::Nothing);
    /// ```
    #[inline]
    fn empty_alt<U>() -> Self::Output<U> {
        Maybe::Nothing
    }

    /// Chooses the first `Just` value, or `Nothing` if both are `Nothing`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::maybe::Maybe;
    /// use rustica::traits::alternative::Alternative;
    ///
    /// let just1 = Maybe::Just(1);
    /// let just2 = Maybe::Just(2);
    /// let nothing: Maybe<i32> = Maybe::Nothing;
    ///
    /// assert_eq!(just1.alt(&just2), Maybe::Just(1));
    /// assert_eq!(just1.alt(&nothing), Maybe::Just(1));
    /// assert_eq!(nothing.alt(&just2), Maybe::Just(2));
    /// assert_eq!(nothing.alt(&nothing), Maybe::Nothing);
    /// ```
    #[inline]
    fn alt(&self, other: &Self) -> Self {
        match self {
            Maybe::Just(_) => self.clone(),
            Maybe::Nothing => other.clone(),
        }
    }

    /// Returns `Just(())` if the condition is true, otherwise `Nothing`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::maybe::Maybe;
    /// use rustica::traits::alternative::Alternative;
    ///
    /// assert_eq!(Maybe::<i32>::guard(true), Maybe::Just(()));
    /// assert_eq!(Maybe::<i32>::guard(false), Maybe::Nothing);
    /// ```
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

/// Creates a `Maybe` from an iterator.
///
/// It will be `Just` with the first element if the iterator is not empty, otherwise `Nothing`.
///
/// # Examples
///
/// ```rust
/// use rustica::datatypes::maybe::Maybe;
///
/// let v1 = vec![1, 2, 3];
/// let m1: Maybe<i32> = v1.into_iter().collect();
/// assert_eq!(m1, Maybe::Just(1));
///
/// let v2: Vec<i32> = vec![];
/// let m2: Maybe<i32> = v2.into_iter().collect();
/// assert_eq!(m2, Maybe::Nothing);
/// ```
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
    /// Gets a reference to the value, panicking if `Nothing`.
    ///
    /// # Panics
    ///
    /// Panics if called on a `Nothing` value.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::maybe::Maybe;
    /// use rustica::traits::identity::Identity;
    ///
    /// let just = Maybe::Just(10);
    /// assert_eq!(*just.value(), 10);
    /// ```
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
    /// Extracts the value out of a `Just`, panicking if it's `Nothing`.
    ///
    /// # Panics
    ///
    /// Panics if called on a `Nothing` value.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::maybe::Maybe;
    /// use rustica::traits::comonad::Comonad;
    ///
    /// let just = Maybe::Just(10);
    /// assert_eq!(just.extract(), 10);
    /// ```
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

    /// Extends a computation from a `Maybe` to a new `Maybe`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::maybe::{Maybe, Maybe::*};
    /// use rustica::traits::comonad::Comonad;
    ///
    /// let just = Just(5);
    /// let extended = just.extend(|m| m.extract() * 2);
    /// assert_eq!(extended, Just(10));
    ///
    /// let nothing: Maybe<i32> = Nothing;
    /// let extended_nothing = nothing.extend(|m| m.extract() * 2);
    /// assert_eq!(extended_nothing, Nothing);
    /// ```
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

/// Creates an iterator from a `Maybe`.
///
/// The iterator will yield one value if the `Maybe` is `Just`, and zero values if it is `Nothing`.
///
/// # Examples
///
/// ```rust
/// use rustica::datatypes::maybe::Maybe;
///
/// let just = Maybe::Just(1);
/// let mut iter = just.into_iter();
/// assert_eq!(iter.next(), Some(1));
/// assert_eq!(iter.next(), None);
///
/// let nothing: Maybe<i32> = Maybe::Nothing;
/// assert_eq!(nothing.into_iter().next(), None);
/// ```
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
            Maybe::Just(val) => std::slice::from_ref(val).iter(),
            Maybe::Nothing => [].iter(),
        }
    }
}

impl<'a, T> IntoIterator for &'a mut Maybe<T> {
    type Item = &'a mut T;
    type IntoIter = std::slice::IterMut<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        match self {
            Maybe::Just(val) => std::slice::from_mut(val).iter_mut(),
            Maybe::Nothing => [].iter_mut(),
        }
    }
}

impl<T> Arbitrary for Maybe<T>
where
    T: Arbitrary + Clone,
{
    fn arbitrary(g: &mut Gen) -> Self {
        if bool::arbitrary(g) {
            Maybe::Nothing
        } else {
            Maybe::Just(T::arbitrary(g))
        }
    }

    fn shrink(&self) -> Box<dyn Iterator<Item = Self>> {
        match self {
            Maybe::Just(a) => Box::new(
                a.shrink()
                    .map(Maybe::Just)
                    .chain(std::iter::once(Maybe::Nothing)),
            ),
            Maybe::Nothing => Box::new(std::iter::empty()),
        }
    }
}

// // Try trait implementation for ? operator support
// impl<T> Try for Maybe<T> {
//     type Output = T;
//     type Residual = Maybe<std::convert::Infallible>;

//     #[inline]
//     fn from_output(output: Self::Output) -> Self {
//         Maybe::Just(output)
//     }

//     #[inline]
//     fn branch(self) -> ControlFlow<Self::Residual, Self::Output> {
//         match self {
//             Maybe::Just(value) => ControlFlow::Continue(value),
//             Maybe::Nothing => ControlFlow::Break(Maybe::Nothing),
//         }
//     }
// }

// impl<T> FromResidual<Maybe<std::convert::Infallible>> for Maybe<T> {
//     #[inline]
//     fn from_residual(_: Maybe<std::convert::Infallible>) -> Self {
//         Maybe::Nothing
//     }
// }
