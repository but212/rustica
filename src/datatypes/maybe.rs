//! # Maybe (`Maybe<T>`)
//!
//! The Maybe monad represents computations which may fail or return a value.
//!
//! `Maybe<T>` is an enum that can be either `Just(T)` containing a value, or `Nothing`
//! representing the absence of a value. This is similar to Rust's built-in `Option<T>` type,
//! but with additional monadic operations.
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
//! - **Short-Circuit Evaluation**: Automatically propagates failure states (`Nothing`) through
//!   computation chains, similar to how Rust's `?` operator works
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
//! - **Short-circuiting**: Operations on `Nothing` propagate the `Nothing` value
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
//! - **MonadPlus**: Extends `Monad` with ability to combine or choose alternatives
//! - **Alternative**: Provides choice between values and an empty value
//! - **Foldable**: Allows folding over the contained value
//!
//! ## Type Class Laws
//!
//! ### Functor Laws
//!
//! The `Maybe` implementation satisfies the functor laws:
//!
//! 1. **Identity Law**: Mapping the identity function over a `Maybe` is the same as the original `Maybe`
//!    - `fmap id = id`
//!
//! 2. **Composition Law**: Mapping a composition of functions is the same as composing the mapped functions
//!    - `fmap (f . g) = fmap f . fmap g`
//!
//! ```rust
//! use rustica::datatypes::maybe::Maybe;
//! use rustica::traits::functor::Functor;
//!
//! // Identity Law: fmap id = id
//! let m1 = Maybe::Just(42);
//! let id = |x: &i32| *x;
//! assert_eq!(m1.fmap(id), m1);
//!
//! // Composition Law: fmap (f . g) = fmap f . fmap g
//! let f = |x: &i32| x + 1;
//! let g = |x: &i32| x * 2;
//! let compose = |x: &i32| f(&g(x));
//!
//! let m2 = Maybe::Just(10);
//! assert_eq!(m2.fmap(compose), m2.fmap(g).fmap(f));
//!
//! // Nothing case should also satisfy both laws
//! let m3: Maybe<i32> = Maybe::Nothing;
//! assert_eq!(m3.fmap(id), m3);  // Identity law for Nothing
//! assert_eq!(m3.fmap(compose), m3.fmap(g).fmap(f));  // Composition law for Nothing
//! ```
//!
//! ### Applicative Laws
//!
//! The `Maybe` implementation satisfies the applicative functor laws:
//!
//! 1. **Identity Law**: Applying `pure id` to any applicative value gives back the same value
//!    - `pure id <*> v = v`
//!
//! 2. **Homomorphism**: Applying a pure function to a pure value is the same as applying the function to the value and then using pure
//!    - `pure f <*> pure x = pure (f x)`
//!
//! 3. **Interchange**: Applying an applicative function to a pure value is the same as applying the pure function application to the function
//!    - `u <*> pure y = pure ($ y) <*> u`
//!
//! 4. **Composition**: Composing applicative functions is associative
//!    - `pure (.) <*> u <*> v <*> w = u <*> (v <*> w)`
//!
//! ```rust
//! use rustica::datatypes::maybe::Maybe;
//! use rustica::traits::applicative::Applicative;
//! use rustica::traits::pure::Pure;
//!
//! // Identity Law for Just
//! let v = Maybe::Just(42);
//! let id = |x: &i32| *x;
//! let pure_id = Maybe::Just(id);
//! assert_eq!(v.apply(&pure_id), v);
//!
//! // Identity Law for Nothing
//! let v_nothing: Maybe<i32> = Maybe::Nothing;
//! assert_eq!(v_nothing.apply(&pure_id), v_nothing);
//!
//! // Homomorphism Law
//! let f = |x: &i32| x + 5;
//! let x = 10;
//! let pure_f = Maybe::Just(f);
//! let pure_x = Maybe::Just(x);
//! assert_eq!(pure_x.apply(&pure_f), Maybe::Just(f(&x)));
//! ```
//!
//! ### Monad Laws
//!
//! The `Maybe` implementation satisfies the monad laws:
//!
//! 1. **Left Identity**: Binding a function to a pure value is the same as applying the function
//!    - `return a >>= f = f a`
//!
//! 2. **Right Identity**: Binding `return` to a monad gives the original monad
//!    - `m >>= return = m`
//!
//! 3. **Associativity**: Sequential binds can be nested or flattened equivalently
//!    - `(m >>= f) >>= g = m >>= (\x -> f x >>= g)`
//!
//! ```rust
//! use rustica::datatypes::maybe::Maybe;
//! use rustica::traits::monad::Monad;
//! use rustica::traits::pure::Pure;
//!
//! // Left Identity: return a >>= f = f a
//! let a = 42;
//! let f = |x: &i32| Maybe::Just(x + 10);
//! assert_eq!(Maybe::<i32>::pure(&a).bind(f), f(&a));
//!
//! // Right Identity: m >>= return = m
//! let m = Maybe::Just(42);
//! let return_fn = |x: &i32| Maybe::<i32>::pure(x);
//! assert_eq!(m.bind(return_fn), m);
//!
//! // Associativity: (m >>= f) >>= g = m >>= (\x -> f x >>= g)
//! let m = Maybe::Just(5);
//! let f = |x: &i32| Maybe::Just(x * 2);
//! let g = |x: &i32| Maybe::Just(x + 10);
//!
//! let left = m.bind(f).bind(g);
//! let right = m.bind(|x| f(x).bind(g));
//! assert_eq!(left, right);
//!
//! // All laws should hold for Nothing as well
//! let nothing: Maybe<i32> = Maybe::Nothing;
//! assert_eq!(nothing.bind(f), Maybe::Nothing);  // Nothing propagates
//! assert_eq!(nothing.bind(return_fn), nothing);  // Right identity for Nothing
//! ```
//!
//! ### MonadPlus/Alternative Laws
//!
//! The `Maybe` implementation satisfies these additional laws:
//!
//! 1. **Left Identity**: `mzero` is a left identity for `mplus`
//!    - `mzero `mplus` m = m`
//!
//! 2. **Right Identity**: `mzero` is a right identity for `mplus`
//!    - `m `mplus` mzero = m`
//!
//! 3. **Left Zero**: `mzero` is a left zero for `bind`
//!    - `mzero >>= f = mzero`
//!
//! 4. **Distributivity**: `mplus` distributes over `bind`
//!    - `(m `mplus` n) >>= f = (m >>= f) `mplus` (n >>= f)`
//!
//! ```rust
//! use rustica::datatypes::maybe::Maybe;
//! use rustica::traits::monad_plus::MonadPlus;
//! use rustica::traits::monad::Monad;
//!
//! // Left and Right Identity
//! let m = Maybe::Just(42);
//! let mzero = Maybe::<i32>::mzero();
//!
//! assert_eq!(mzero.mplus(&m), m);  // Left identity
//! assert_eq!(m.mplus(&mzero), m);  // Right identity
//!
//! // Left Zero
//! let f = |x: &i32| Maybe::Just(x + 10);
//! assert_eq!(mzero.bind(f), mzero);
//!
//! // Distributivity
//! let n = Maybe::Just(7);
//! let left = m.mplus(&n).bind(f);
//! let right = m.bind(f).mplus(&n.bind(f));
//! assert_eq!(left, right);
//! ```
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
#[cfg(feature = "full")]
use quickcheck::{Arbitrary, Gen};
use std::marker::PhantomData;

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
/// let sum = a.lift2(&b, |x, y| *x + *y);
/// assert_eq!(sum, Maybe::Just(15));
///
/// // If any value is Nothing, the result is Nothing
/// let c: Maybe<i32> = Maybe::Nothing;
/// let partial_sum = a.lift2(&c, |x, y| *x + *y);
/// assert_eq!(partial_sum, Maybe::Nothing);
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
            MaybeError::Custom(msg) => write!(f, "{msg}"),
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
        F: FnOnce(&Self::Source) -> B,
    {
        match self {
            Maybe::Just(x) => Maybe::Just(f(x)),
            Maybe::Nothing => Maybe::Nothing,
        }
    }

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
    ///
    /// Conditional logic:
    ///
    /// ```rust
    /// use rustica::datatypes::maybe::Maybe;
    /// use rustica::traits::monad::Monad;
    ///
    /// // A function that returns Maybe based on a condition
    /// fn safe_divide(x: i32, y: i32) -> Maybe<i32> {
    ///     if y == 0 {
    ///         Maybe::Nothing
    ///     } else {
    ///         Maybe::Just(x / y)
    ///     }
    /// }
    ///
    /// // Using bind with conditional logic
    /// let m = Maybe::Just(10);
    ///
    /// // This succeeds because 2 is not zero
    /// let result = m.bind(|x| safe_divide(*x, 2));
    /// assert_eq!(result, Maybe::Just(5));
    ///
    /// // This fails because we're dividing by zero
    /// let result = m.bind(|x| safe_divide(*x, 0));
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
    ///
    /// Handling complex transformations that require ownership:
    ///
    /// ```rust
    /// use rustica::datatypes::maybe::Maybe;
    /// use rustica::traits::monad::Monad;
    ///
    /// // A function that requires ownership of its input
    /// fn process_vec(vec: Vec<i32>) -> Maybe<i32> {
    ///     if vec.is_empty() {
    ///         Maybe::Nothing
    ///     } else {
    ///         let sum: i32 = vec.into_iter().sum();
    ///         Maybe::Just(sum)
    ///     }
    /// }
    ///
    /// let m = Maybe::Just(vec![1, 2, 3, 4]);
    /// let result = m.bind_owned(process_vec);
    /// assert_eq!(result, Maybe::Just(10));
    ///
    /// let empty: Maybe<Vec<i32>> = Maybe::Just(Vec::new());
    /// let result = empty.bind_owned(process_vec);
    /// assert_eq!(result, Maybe::Nothing);
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
    ///
    /// Using join to simplify nested computations:
    ///
    /// ```rust
    /// use rustica::datatypes::maybe::Maybe;
    /// use rustica::traits::monad::Monad;
    /// use rustica::traits::functor::Functor;
    ///
    /// // A function that returns Maybe<Maybe<T>>
    /// fn lookup_with_fallback(id: i32) -> Maybe<Maybe<String>> {
    ///     if id < 0 {
    ///         Maybe::Nothing // Invalid ID
    ///     } else if id < 10 {
    ///         // Primary lookup succeeded
    ///         Maybe::Just(Maybe::Just(format!("User-{}", id)))
    ///     } else {
    ///         // Primary lookup failed, no fallback available
    ///         Maybe::Just(Maybe::Nothing)
    ///     }
    /// }
    ///
    /// // Using join to flatten the results
    /// let result_found = lookup_with_fallback(5).join();
    /// let result_not_found = lookup_with_fallback(15).join();
    /// let invalid = lookup_with_fallback(-1).join();
    ///
    /// assert_eq!(result_found, Maybe::Just(String::from("User-5")));
    /// assert_eq!(result_not_found, Maybe::Nothing);
    /// assert_eq!(invalid, Maybe::Nothing);
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
    ///
    /// Performance comparison with `join` (conceptual example):
    ///
    /// ```rust
    /// use rustica::datatypes::maybe::Maybe;
    /// use rustica::traits::monad::Monad;
    ///
    /// // A large vector that would be expensive to clone
    /// let large_data = vec![1; 1000000];
    ///
    /// // Wrap it in nested Maybes
    /// let nested_clone = Maybe::Just(Maybe::Just(large_data.clone()));
    /// let nested_owned = Maybe::Just(Maybe::Just(large_data));
    ///
    /// // join requires a clone of the inner Maybe
    /// let result1 = nested_clone.join();
    ///
    /// // join_owned moves the inner Maybe, avoiding the clone
    /// let result2 = nested_owned.join_owned();
    ///
    /// // Both produce the same result, but join_owned is more efficient
    /// // for large or non-Copy types
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

#[cfg(feature = "full")]
impl<T> Arbitrary for Maybe<T>
where
    T: Arbitrary + Clone,
{
    fn arbitrary(g: &mut Gen) -> Self {
        let value = T::arbitrary(g);
        if bool::arbitrary(g) {
            Maybe::Just(value)
        } else {
            Maybe::Nothing
        }
    }
}
