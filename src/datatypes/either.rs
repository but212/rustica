//! # Either Datatype
//!
//! The `Either` datatype represents values with two possibilities: a value of type `L` (Left) or a value of type `R` (Right).
//! It is a fundamental functional programming construct that is similar to Rust's built-in `Result<T, E>` but without the
//! semantic meaning of success/failure.
//!
//! ## Functional Programming Context
//!
//! In functional programming, the `Either` type is commonly used for:
//!
//! - Representing computations that can produce one of two different types of values
//! - Handling branching logic in a composable way
//! - Implementing error handling without the success/failure semantics of `Result`
//! - Building more complex data structures and control flow mechanisms
//!
//! ## Performance Characteristics
//!
//! - **Memory Usage**: An `Either<L, R>` uses the same memory as the larger of `L` or `R`, plus a tag (usually 1 byte) to
//!   distinguish between Left and Right variants.
//! - **Construction**: O(1) time and space complexity.
//! - **Pattern Matching**: O(1) time complexity for checking whether a value is Left or Right.
//! - **Transformations**: Operations like `fmap`, `fmap_left`, and `bind` have O(1) complexity for the operation itself,
//!   with the overall complexity determined by the provided function.
//! - **Cloning**: O(n) where n is the size of the contained value (Left or Right).
//! - **Iterator Operations**: O(1) for iterator creation, yields at most one item
//! - **Left/Right Iterator Symmetry**: Both directions have identical performance characteristics
//!
//! ## Type Class Implementations
//!
//! The `Either` type implements several important functional programming abstractions:
//!
//! - `Functor`: Maps over the right value with `fmap`
//! - `Applicative`: Applies functions wrapped in `Either` to values wrapped in `Either`
//! - `Monad`: Chains computations that may produce either left or right values
//! - `Alternative`/`MonadPlus`: Provides choice between alternatives (requires `L: Default + Clone`)
//! - `Identity`: **WARNING**: Logically unsound implementation that only works with `Right` values and panics on `Left`
//!
//! **Note**: The `Identity` implementation should be avoided. Use explicit methods like `right_value()`, `is_right()` instead.
//!
//! ## Type Class Laws
//!
//! ### Functor Laws
//!
//! ```rust
//! use rustica::datatypes::either::Either;
//! use rustica::traits::functor::Functor;
//!
//! // 1. Identity: fmap id = id
//! let e: Either<i32, String> = Either::right("test".to_string());
//! assert_eq!(e.fmap(|x| x.clone()), e);
//!
//! // 2. Composition: fmap (f . g) = fmap f . fmap g
//! let e: Either<i32, i32> = Either::right(5);
//!
//! let f = |x: &i32| x * 2;
//! let g = |x: &i32| x + 3;
//!
//! let composed = |x: &i32| f(&g(x));
//!
//! assert_eq!(e.fmap(composed), e.fmap(g).fmap(f));
//!
//! // Laws hold for Left values too (trivially, since fmap doesn't affect Left)
//! let e: Either<i32, String> = Either::left(10);
//! let e_with_len = e.clone().fmap(|x: &String| x.len());
//! assert_eq!(e_with_len, Either::left(10));
//! ```
//!
//! ### Monad Laws
//!
//! ```rust
//! use rustica::datatypes::either::Either;
//! use rustica::traits::pure::Pure;
//! use rustica::traits::monad::Monad;
//!
//! // 1. Left Identity: return a >>= f = f a
//! let a = 5;
//! let f = |x: &i32| Either::<String, i32>::right(*x * 2);
//! assert_eq!(Either::<String, i32>::pure(&a).bind(f), f(&a));
//!
//! // 2. Right Identity: m >>= return = m
//! let m: Either<String, i32> = Either::right(5);
//! assert_eq!(m.bind(|x| Either::<String, i32>::pure(x)), m);
//!
//! // 3. Associativity: (m >>= f) >>= g = m >>= (\x -> f x >>= g)
//! let m: Either<String, i32> = Either::right(5);
//! let f = |x: &i32| Either::<String, i32>::right(*x * 2);
//! let g = |x: &i32| Either::<String, i32>::right(*x + 3);
//!
//! assert_eq!(m.bind(f).bind(g), m.bind(|x| f(x).bind(g)));
//! ```
//!
//! ## Basic Usage
//!
//! ```rust
//! use rustica::datatypes::either::Either;
//! use rustica::prelude::*;
//!
//! // Create Either values
//! let left_value: Either<i32, &str> = Either::left(42);
//! let right_value: Either<i32, &str> = Either::right("hello");
//!
//! // Pattern matching
//! match left_value {
//!     Either::Left(n) => println!("Got left value: {}", n),
//!     Either::Right(s) => println!("Got right value: {}", s),
//! }
//!
//! // Transform values using specific transformers
//! let doubled = left_value.fmap_left(|x| x * 2);  // Either::Left(84)
//!
//! // Functor operations (maps over Right values only)
//! let right_val: Either<&str, i32> = Either::right(42);
//! let mapped = right_val.fmap(|x| x * 2);  // Either::Right(84)
//! ```
//!
//! ## Advanced Usage: Chaining Computations
//!
//! ```rust
//! use rustica::datatypes::either::Either;
//! use rustica::traits::monad::Monad;
//!
//! // Create a function that might fail (return Left) or succeed (return Right)
//! fn safe_divide(a: i32, b: i32) -> Either<String, i32> {
//!     if b == 0 {
//!         Either::left("Division by zero".to_string())
//!     } else {
//!         Either::right(a / b)
//!     }
//! }
//!
//! // Chain computations safely
//! let result = safe_divide(10, 2)
//!     .bind(|x| safe_divide(*x, 1)); // Will succeed with Right(5)
//!     
//! let error_result = safe_divide(10, 2)
//!     .bind(|x| safe_divide(*x, 0)); // Will fail with Left("Division by zero")
//!
//! assert_eq!(result, Either::right(5));
//! assert_eq!(error_result, Either::left("Division by zero".to_string()));
//! ```
//!
//! ## Conversion with Result
//!
//! `Either` can be easily converted to and from `Result`:
//!
//! ```rust
//! use rustica::datatypes::either::Either;
//!
//! // From Result to Either
//! let ok_result: Result<i32, &str> = Ok(42);
//! let either = Either::from_result(ok_result);
//! assert_eq!(either, Either::right(42));
//!
//! // From Either to Result
//! let either: Either<&str, i32> = Either::right(42);
//! let result = either.to_result();
//! assert_eq!(result, Ok(42));
//! ```
//!
//! ## Iterator Support
//!
//! The `Either` type provides **symmetric iterator support** for both `Left` and `Right` values.
//! Both `Left` and `Right` values can be iterated over, yielding at most one item.
//!
//! This design allows `Either<L, R>` to function similarly to `Option<L>` or `Option<R>`
//! in iterator contexts, where the contained value (if present) is treated as the "value of interest".
//!
//! Six iterator types are provided:
//!
//! - `EitherIter<R>` - Consumes the `Either` and iterates over the contained `Right` value
//! - `EitherIterRef<'a, R>` - Provides references to the `Right` value
//! - `EitherIterMut<'a, R>` - Provides mutable references to the `Right` value
//! - `EitherLeftIter<L>` - Consumes the `Either` and iterates over the contained `Left` value
//! - `EitherLeftIterRef<'a, L>` - Provides references to the `Left` value
//! - `EitherLeftIterMut<'a, L>` - Provides mutable references to the `Left` value
//!
//! All iterator implementations yield at most one item, making them similar to `Option::into_iter()`.
//!
//! ```rust
//! use rustica::datatypes::either::Either;
//!
//! // Iterate over Right values
//! let right_val: Either<&str, i32> = Either::right(42);
//! let values: Vec<i32> = right_val.into_iter().collect();
//! assert_eq!(values, vec![42]);
//!
//! // Left values yield empty iterators when using the Right-biased iterator
//! let left_val: Either<&str, i32> = Either::left("error");
//! let values: Vec<i32> = left_val.into_iter().collect();
//! assert!(values.is_empty());
//!
//! // Reference iteration works similarly for Right
//! let right_val: Either<&str, i32> = Either::right(42);
//! let values: Vec<&i32> = (&right_val).into_iter().collect();
//! assert_eq!(values, vec![&42]);
//!
//! // Iterate over Left values
//! let left_val: Either<i32, &str> = Either::left(100);
//! let values: Vec<i32> = left_val.left_iter().collect();
//! assert_eq!(values, vec![100]);
//!
//! // Right values yield empty iterators when using the Left-biased iterator
//! let right_val: Either<i32, &str> = Either::right("success");
//! let values: Vec<i32> = right_val.left_iter().collect();
//! assert!(values.is_empty());
//!
//! // Reference iteration works similarly for Left
//! let left_val: Either<i32, &str> = Either::left(100);
//! let values: Vec<&i32> = left_val.left_iter_ref().collect();
//! assert_eq!(values, vec![&100]);
//! ```
//!
//! ## Safety Considerations
//!
//! Several methods in `Either` can panic and should be used with caution:
//!
//! - `unwrap_left()`, `unwrap_right()`: Panic if called on wrong variant
//! - `left_value()`, `right_value()`: Panic if called on wrong variant  
//! - `left_ref()`, `right_ref()`: Panic if called on wrong variant
//! - `Identity` trait methods: Panic if called on `Left` variant
//!
//! **Recommended alternatives**: Use pattern matching, `left_option()`, `right_option()`, or the safe `*_or()` methods.

use crate::traits::alternative::Alternative;
use crate::traits::applicative::Applicative;
use crate::traits::composable::Composable;
use crate::traits::functor::Functor;
use crate::traits::hkt::HKT;
use crate::traits::identity::Identity;
use crate::traits::monad::Monad;
use crate::traits::monad_plus::MonadPlus;
use crate::traits::pure::Pure;
use crate::utils::error_utils;
#[cfg(feature = "full")]
use quickcheck::{Arbitrary, Gen};

/// The `Either` type represents values with two possibilities: a value of type `L` or a value of type `R`.
/// This is similar to `Result<T, E>` but without the semantic meaning of success/failure.
///
/// # Type Parameters
///
/// * `L`: The type of the left value
/// * `R`: The type of the right value
///
/// See the module-level documentation for examples and more information.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum Either<L, R> {
    /// Contains a value of type `L`
    Left(L),
    /// Contains a value of type `R`
    Right(R),
}

impl<L, R> Either<L, R> {
    /// Creates a new `Either::Left` containing the given value.
    ///
    /// Left represents the first possibility of the Either type.
    ///
    /// # Performance
    ///
    /// - Time complexity: O(1).
    /// - Space complexity: O(1).
    ///
    /// # Usage
    ///
    /// Use this constructor to create an `Either` instance holding a `Left` value.
    ///
    /// ```
    /// # use rustica::datatypes::either::Either;
    /// let e: Either<i32, String> = Either::left(42);
    /// assert!(e.is_left());
    /// ```
    #[inline]
    pub const fn left(l: L) -> Self {
        Either::Left(l)
    }

    /// Creates a new `Either::Right` containing the given value.
    ///
    /// Right represents the second possibility of the Either type.
    ///
    /// # Performance
    ///
    /// - Time complexity: O(1).
    /// - Space complexity: O(1).
    ///
    /// # Usage
    ///
    /// Use this constructor to create an `Either` instance holding a `Right` value.
    ///
    /// ```
    /// # use rustica::datatypes::either::Either;
    /// let e: Either<i32, String> = Either::right("hello".to_string());
    /// assert!(e.is_right());
    /// ```
    #[inline]
    pub const fn right(r: R) -> Self {
        Either::Right(r)
    }

    /// Returns `true` if this is a `Left` value.
    ///
    /// # Performance
    ///
    /// - Time complexity: O(1).
    /// - Space complexity: O(1).
    ///
    /// # Usage
    ///
    /// Check if an `Either` is `Left` without consuming it or panicking.
    /// Useful for conditional logic based on the variant.
    ///
    /// ```
    /// # use rustica::datatypes::either::Either;
    /// let left: Either<i32, &str> = Either::Left(1);
    /// assert!(left.is_left());
    /// let right: Either<i32, &str> = Either::Right("test");
    /// assert!(!right.is_left());
    /// ```
    #[inline]
    pub const fn is_left(&self) -> bool {
        matches!(self, Either::Left(_))
    }

    /// Returns `true` if this is a `Right` value.
    ///
    /// # Performance
    ///
    /// - Time complexity: O(1).
    /// - Space complexity: O(1).
    ///
    /// # Usage
    ///
    /// Check if an `Either` is `Right` without consuming it or panicking.
    /// Useful for conditional logic based on the variant.
    ///
    /// ```
    /// # use rustica::datatypes::either::Either;
    /// let right: Either<i32, &str> = Either::Right("test");
    /// assert!(right.is_right());
    /// let left: Either<i32, &str> = Either::Left(1);
    /// assert!(!left.is_right());
    /// ```
    #[inline]
    pub const fn is_right(&self) -> bool {
        matches!(self, Either::Right(_))
    }

    /// Maps a function over the left value, leaving a right value unchanged.
    ///
    /// This is similar to `Result::map_err` but for `Either`.
    ///
    /// # Performance
    ///
    /// - Time complexity: O(1), assuming the provided function `f` is O(1).
    /// - Space complexity: O(1).
    ///
    /// # Usage
    ///
    /// Use `fmap_left` to apply a transformation to the `Left` value if present,
    /// while leaving a `Right` value untouched. This is useful for changing the
    /// type or value of the `Left` case, often an error or alternative type.
    ///
    /// ```
    /// # use rustica::datatypes::either::Either;
    /// let left_val: Either<i32, String> = Either::Left(10);
    /// let mapped = left_val.fmap_left(|x| x * 2);
    /// assert_eq!(mapped, Either::Left(20));
    ///
    /// let right_val: Either<i32, String> = Either::Right("hello".to_string());
    /// let mapped_right = right_val.fmap_left(|x| x * 2); // f is not called
    /// assert_eq!(mapped_right, Either::Right("hello".to_string()));
    /// ```
    #[inline]
    pub fn fmap_left<T, F>(self, f: F) -> Either<T, R>
    where
        F: Fn(L) -> T,
    {
        match self {
            Either::Left(l) => Either::Left(f(l)),
            Either::Right(r) => Either::Right(r),
        }
    }

    /// Maps a function over the right value, leaving a left value unchanged.
    ///
    /// This is similar to `Result::map` but for `Either`. It is the primary
    /// way to transform the `Right` variant and is fundamental to `Either`'s
    /// role as a `Functor` (see `Functor::fmap_owned` for the general version).
    ///
    /// # Performance
    ///
    /// - Time complexity: O(1), assuming the provided function `f` is O(1).
    /// - Space complexity: O(1).
    ///
    /// # Usage
    ///
    /// Use `fmap_right` to apply a transformation to the `Right` value without
    /// affecting a `Left` value. For example, if you have an `Either<Error, Data>`,
    /// you can use `fmap_right` to process `Data` while propagating `Error`.
    ///
    /// ```
    /// # use rustica::datatypes::either::Either;
    /// let right_val: Either<String, i32> = Either::Right(10);
    /// let mapped = right_val.fmap_right(|x| x * 2);
    /// assert_eq!(mapped, Either::Right(20));
    ///
    /// let left_val: Either<String, i32> = Either::Left("error".to_string());
    /// let mapped_left = left_val.fmap_right(|x| x * 2); // f is not called
    /// assert_eq!(mapped_left, Either::Left("error".to_string()));
    /// ```
    #[inline]
    pub fn fmap_right<T, F>(self, mut f: F) -> Either<L, T>
    where
        F: FnMut(R) -> T,
    {
        match self {
            Either::Left(l) => Either::Left(l),
            Either::Right(r) => Either::Right(f(r)),
        }
    }

    /// Extracts the left value, panicking if this is a `Right`.
    ///
    /// # Performance
    ///
    /// - Time complexity: O(1).
    /// - Space complexity: O(1).
    ///
    /// # Usage
    ///
    /// Use this method when you are certain that the `Either` contains a `Left`
    /// value and a panic is an acceptable outcome if this assumption is wrong.
    /// This is often used in tests or when a `Left` value is a precondition
    /// for subsequent logic. For a non-panicking alternative, consider `left_option`
    /// or pattern matching.
    ///
    /// # Panics
    ///
    /// Panics if called on a `Right` value.
    #[inline]
    pub fn unwrap_left(self) -> L {
        match self {
            Either::Left(l) => l,
            Either::Right(_) => panic!("called unwrap_left on Right value"),
        }
    }

    /// Extracts the right value, panicking if this is a `Left`.
    ///
    /// This method delegates to `right_value`.
    ///
    /// # Performance
    ///
    /// - Time complexity: O(1).
    /// - Space complexity: O(1).
    ///
    /// # Usage
    ///
    /// Use this method when you are certain that the `Either` contains a `Right`
    /// value and a panic is an acceptable outcome if this assumption is wrong.
    /// This is often used in tests or when a `Right` value is a precondition
    /// for subsequent logic. For a non-panicking alternative, consider `right_option`
    /// or pattern matching.
    ///
    /// # Panics
    ///
    /// Panics if called on a `Left` value.
    #[inline]
    pub fn unwrap_right(self) -> R {
        match self {
            Either::Right(r) => r,
            Either::Left(_) => panic!("called unwrap_right on Left value"),
        }
    }

    /// Returns the contained `Left` value, consuming the `self` value.
    ///
    /// Because this function consumes the original `Either`, there is no need to clone
    /// the content if `L` is not `Copy`. This can be more efficient than `unwrap_left`
    /// in such cases, though `unwrap_left` also consumes `self`.
    /// The main distinction is often stylistic or historical.
    ///
    /// # Performance
    ///
    /// - Time complexity: O(1).
    /// - Space complexity: O(1).
    ///
    /// # Usage
    ///
    /// Similar to `unwrap_left`, use this when you expect a `Left` value and
    /// want to consume the `Either` to get it. A panic occurs if it's `Right`.
    ///
    /// # Panics
    ///
    /// Panics if the value is a `Right`.
    #[inline]
    pub fn left_value(self) -> L
    where
        Self: Sized,
    {
        match self {
            Either::Left(l) => l,
            Either::Right(_) => panic!("Called left_value on an Either::Right"),
        }
    }

    /// Returns the contained `Right` value, consuming the `self` value.
    ///
    /// Because this function consumes the original `Either`, there is no need to clone
    /// the content if `R` is not `Copy`. This can be more efficient than methods
    /// that might require cloning if `self` were borrowed.
    ///
    /// # Performance
    ///
    /// - Time complexity: O(1).
    /// - Space complexity: O(1).
    ///
    /// # Usage
    ///
    /// Similar to `unwrap_right`, use this when you expect a `Right` value and
    /// want to consume the `Either` to get it. A panic occurs if it's `Left`.
    ///
    /// # Panics
    ///
    /// Panics if the value is a `Left`.
    #[inline]
    pub fn right_value(self) -> R {
        match self {
            Either::Right(r) => r,
            Either::Left(_) => panic!("called right_value on Left value"),
        }
    }

    /// Returns a reference to the `Left` value.
    ///
    /// # Performance
    ///
    /// - Time complexity: O(1).
    /// - Space complexity: O(1).
    ///
    /// # Usage
    ///
    /// Use this to get an immutable reference to the `Left` value without consuming
    /// the `Either`. This is useful when you need to inspect the `Left` value but
    /// keep the `Either` instance for later use. Panics if the `Either` is `Right`.
    ///
    /// # Panics
    ///
    /// Panics if the value is a `Right`.
    #[inline]
    pub fn left_ref(&self) -> &L {
        match self {
            Either::Left(l) => l,
            Either::Right(_) => panic!("Called left_ref on an Either::Right"),
        }
    }

    /// Returns a reference to the `Right` value.
    ///
    /// # Performance
    ///
    /// - Time complexity: O(1).
    /// - Space complexity: O(1).
    ///
    /// # Usage
    ///
    /// Use this to get an immutable reference to the `Right` value without consuming
    /// the `Either`. This is useful when you need to inspect the `Right` value but
    /// keep the `Either` instance for later use. Panics if the `Either` is `Left`.
    ///
    /// # Panics
    ///
    /// Panics if the value is a `Left`.
    #[inline]
    pub fn right_ref(&self) -> &R {
        self.into_iter()
            .next()
            .expect("Called right_ref() on a Left value")
    }

    /// Returns the contained `Right` value or a default.
    ///
    /// Similar to `Result::unwrap_or` but for `Either`.
    /// Consumes `self` and returns the `Right` value if present, otherwise returns
    /// the provided `default`.
    ///
    /// # Performance
    ///
    /// - Time complexity: O(1).
    /// - Space complexity: O(1).
    ///
    /// # Usage
    ///
    /// Use this method to extract the `Right` value if it exists, or fall back to a
    /// default value if it's a `Left`. This avoids panics.
    ///
    /// ```
    /// # use rustica::datatypes::either::Either;
    /// let right: Either<String, i32> = Either::Right(100);
    /// assert_eq!(right.right_or(0), 100);
    ///
    /// let left: Either<String, i32> = Either::Left("error".to_string());
    /// assert_eq!(left.right_or(0), 0);
    /// ```
    #[inline]
    pub fn right_or(self, default: R) -> R {
        self.into_iter().next().unwrap_or(default)
    }

    /// Returns the contained `Left` value or a default.
    ///
    /// Similar to `Result::err().unwrap_or()` but for `Either`.
    /// Consumes `self` and returns the `Left` value if present, otherwise returns
    /// the provided `default`.
    ///
    /// # Performance
    ///
    /// - Time complexity: O(1).
    /// - Space complexity: O(1).
    ///
    /// # Usage
    ///
    /// Use this method to extract the `Left` value if it exists, or fall back to a
    /// default value if it's a `Right`. This avoids panics.
    ///
    /// ```
    /// # use rustica::datatypes::either::Either;
    /// let left: Either<i32, String> = Either::Left(42);
    /// assert_eq!(left.left_or(0), 42);
    ///
    /// let right: Either<i32, String> = Either::Right("ok".to_string());
    /// assert_eq!(right.left_or(0), 0);
    /// ```
    #[inline]
    pub fn left_or(self, default: L) -> L {
        match self {
            Either::Left(l) => l,
            Either::Right(_) => default,
        }
    }

    /// Returns the contained `Right` value as an Option.
    ///
    /// Returns `Some(R)` for `Right(R)` values and `None` for `Left(L)` values.
    /// Consumes `self`.
    ///
    /// # Performance
    ///
    /// - Time complexity: O(1).
    /// - Space complexity: O(1).
    ///
    /// # Usage
    ///
    /// Convert an `Either` into an `Option<R>`, discarding the `Left` value.
    /// This is useful for integrating with Option-based APIs or when you only
    /// care about the `Right` case and want to treat `Left` as absence of value.
    ///
    /// ```
    /// # use rustica::datatypes::either::Either;
    /// let right: Either<String, i32> = Either::Right(10);
    /// assert_eq!(right.right_option(), Some(10));
    ///
    /// let left: Either<String, i32> = Either::Left("error".to_string());
    /// assert_eq!(left.right_option(), None);
    /// ```
    #[inline]
    pub fn right_option(self) -> Option<R> {
        self.into_iter().next()
    }

    /// Converts this `Either` to a `Result`.
    ///
    /// `Either::Left(L)` becomes `Result::Err(L)` and `Either::Right(R)` becomes `Result::Ok(R)`.
    /// Consumes `self`.
    ///
    /// # Performance
    ///
    /// - Time complexity: O(1).
    /// - Space complexity: O(1).
    ///
    /// # Usage
    ///
    /// Use this to bridge `Either` with Rust's standard `Result` type, especially
    /// when `Either` is used to represent a computation that can fail (where `Left`
    /// typically holds an error type) and you want to leverage `Result`'s error
    /// handling mechanisms (e.g., the `?` operator).
    ///
    /// ```
    /// # use rustica::datatypes::either::Either;
    /// let right_either: Either<String, i32> = Either::Right(100);
    /// assert_eq!(right_either.to_result(), Ok(100));
    ///
    /// let left_either: Either<String, i32> = Either::Left("failed".to_string());
    /// assert_eq!(left_either.to_result(), Err("failed".to_string()));
    /// ```
    #[inline]
    pub fn to_result(self) -> Result<R, L> {
        error_utils::either_to_result(self)
    }

    /// Creates an `Either` from a `Result`.
    ///
    /// `Result::Err(L)` becomes `Either::Left(L)` and `Result::Ok(R)` becomes `Either::Right(R)`.
    ///
    /// # Performance
    ///
    /// - Time complexity: O(1).
    /// - Space complexity: O(1).
    ///
    /// # Usage
    ///
    /// Use this to convert a standard `Result` into an `Either`. This is useful
    /// when interfacing with functions that return `Result` but you want to work
    /// with `Either`'s more general two-possibility semantics without the inherent
    /// success/failure implication of `Result`.
    ///
    /// ```
    /// # use rustica::datatypes::either::Either;
    /// let ok_result: Result<i32, String> = Ok(100);
    /// assert_eq!(Either::from_result(ok_result), Either::Right(100));
    ///
    /// let err_result: Result<i32, String> = Err("oops".to_string());
    /// assert_eq!(Either::from_result(err_result), Either::Left("oops".to_string()));
    /// ```
    #[inline]
    pub fn from_result(result: Result<R, L>) -> Self {
        error_utils::result_to_either(result)
    }

    /// Returns an iterator over the left value, consuming self.
    pub fn left_iter(self) -> EitherLeftIter<L> {
        match self {
            Either::Left(l) => EitherLeftIter { left: Some(l) },
            Either::Right(_) => EitherLeftIter { left: None },
        }
    }

    /// Returns an iterator over a reference to the left value.
    pub fn left_iter_ref(&self) -> EitherLeftIterRef<'_, L> {
        match self {
            Either::Left(l) => EitherLeftIterRef { left: Some(l) },
            Either::Right(_) => EitherLeftIterRef { left: None },
        }
    }

    /// Returns an iterator over a mutable reference to the left value.
    pub fn left_iter_mut(&mut self) -> EitherLeftIterMut<'_, L> {
        match self {
            Either::Left(l) => EitherLeftIterMut { left: Some(l) },
            Either::Right(_) => EitherLeftIterMut { left: None },
        }
    }

    /// Returns the contained `Left` value as an Option.
    ///
    /// Returns `Some(L)` for `Left(L)` values and `None` for `Right(R)` values.
    /// Consumes `self`.
    ///
    /// # Performance
    ///
    /// - Time complexity: O(1).
    /// - Space complexity: O(1).
    ///
    /// # Usage
    ///
    /// Convert an `Either` into an `Option<L>`, discarding the `Right` value.
    /// This is useful when you only care about the `Left` case and want to treat
    /// `Right` as absence of the `Left` type.
    ///
    /// ```
    /// # use rustica::datatypes::either::Either;
    /// let left: Either<i32, String> = Either::Left(42);
    /// assert_eq!(left.left_option(), Some(42));
    ///
    /// let right: Either<i32, String> = Either::Right("ok".to_string());
    /// assert_eq!(right.left_option(), None);
    /// ```
    pub fn left_option(self) -> Option<L> {
        self.left_iter().next()
    }

    /// Returns a mutable reference to the `Left` value, panicking if not present.
    pub fn left_mut(&mut self) -> &mut L {
        self.left_iter_mut()
            .next()
            .expect("Called left_mut() on a Right value")
    }
}

/// An iterator over the left value of an `Either<L, R>`.
pub struct EitherLeftIter<L> {
    left: Option<L>,
}

impl<L> Iterator for EitherLeftIter<L> {
    type Item = L;
    fn next(&mut self) -> Option<L> {
        self.left.take()
    }
}

/// An iterator over a reference to the left value of an `Either<L, R>`.
pub struct EitherLeftIterRef<'a, L> {
    left: Option<&'a L>,
}

impl<'a, L> Iterator for EitherLeftIterRef<'a, L> {
    type Item = &'a L;
    fn next(&mut self) -> Option<&'a L> {
        self.left.take()
    }
}

/// An iterator over a mutable reference to the left value of an `Either<L, R>`.
pub struct EitherLeftIterMut<'a, L> {
    left: Option<&'a mut L>,
}

impl<'a, L> Iterator for EitherLeftIterMut<'a, L> {
    type Item = &'a mut L;
    fn next(&mut self) -> Option<&'a mut L> {
        self.left.take()
    }
}

impl<L, R> HKT for Either<L, R> {
    type Source = R;
    type Output<T> = Either<L, T>;
}

impl<L: Clone, R: Clone> Functor for Either<L, R> {
    #[inline]
    fn fmap<B, F>(&self, f: F) -> Self::Output<B>
    where
        F: Fn(&Self::Source) -> B,
    {
        match self {
            Either::Left(l) => Either::Left(l.clone()),
            Either::Right(r) => Either::Right(f(r)),
        }
    }

    #[inline]
    fn fmap_owned<B, F>(self, f: F) -> Self::Output<B>
    where
        F: Fn(Self::Source) -> B,
    {
        match self {
            Either::Left(l) => Either::Left(l),
            Either::Right(r) => Either::Right(f(r)),
        }
    }
}

impl<L, R> Pure for Either<L, R> {
    #[inline]
    fn pure<T: Clone>(value: &T) -> Self::Output<T> {
        Either::Right(value.clone())
    }
}

impl<L: Clone, R: Clone> Applicative for Either<L, R> {
    fn apply<B, F>(&self, f: &Self::Output<F>) -> Self::Output<B>
    where
        F: Fn(&Self::Source) -> B,
    {
        match (self, f) {
            (Either::Right(r), Either::Right(func)) => Either::Right(func(r)),
            (Either::Left(l), _) => Either::Left(l.clone()),
            (_, Either::Left(l)) => Either::Left(l.clone()),
        }
    }

    fn lift2<B, C, F>(&self, b: &Self::Output<B>, f: F) -> Self::Output<C>
    where
        F: Fn(&Self::Source, &B) -> C,
    {
        match (self, b) {
            (Either::Right(r), Either::Right(b_val)) => Either::Right(f(r, b_val)),
            (Either::Left(l), _) => Either::Left(l.clone()),
            (_, Either::Left(l)) => Either::Left(l.clone()),
        }
    }

    fn lift3<B, C, D, F>(&self, b: &Self::Output<B>, c: &Self::Output<C>, f: F) -> Self::Output<D>
    where
        F: Fn(&Self::Source, &B, &C) -> D,
    {
        match (self, b, c) {
            (Either::Right(r), Either::Right(b_val), Either::Right(c_val)) => {
                Either::Right(f(r, b_val, c_val))
            },
            (Either::Left(l), _, _) => Either::Left(l.clone()),
            (_, Either::Left(l), _) => Either::Left(l.clone()),
            (_, _, Either::Left(l)) => Either::Left(l.clone()),
        }
    }

    fn apply_owned<B, F>(self, f: Self::Output<F>) -> Self::Output<B>
    where
        F: FnOnce(Self::Source) -> B,
        Self: Sized,
    {
        match (self, f) {
            (Either::Right(x), Either::Right(f)) => Either::Right(f(x)),
            (Either::Left(l), _) => Either::Left(l),
            (_, Either::Left(l)) => Either::Left(l),
        }
    }

    fn lift2_owned<B, C, F>(self, b: Self::Output<B>, f: F) -> Self::Output<C>
    where
        F: FnOnce(Self::Source, B) -> C,
        Self: Sized,
    {
        match (self, b) {
            (Either::Right(x), Either::Right(y)) => Either::Right(f(x, y)),
            (Either::Left(l), _) => Either::Left(l),
            (_, Either::Left(l)) => Either::Left(l),
        }
    }

    fn lift3_owned<B, C, D, F>(
        self, b: Self::Output<B>, c: Self::Output<C>, f: F,
    ) -> Self::Output<D>
    where
        F: FnOnce(Self::Source, B, C) -> D,
        Self: Sized,
    {
        match (self, b, c) {
            (Either::Right(x), Either::Right(y), Either::Right(z)) => Either::Right(f(x, y, z)),
            (Either::Left(l), _, _) => Either::Left(l),
            (_, Either::Left(l), _) => Either::Left(l),
            (_, _, Either::Left(l)) => Either::Left(l),
        }
    }
}

impl<L: Clone, R: Clone> Monad for Either<L, R> {
    #[inline]
    fn bind<B, F>(&self, f: F) -> Self::Output<B>
    where
        F: Fn(&Self::Source) -> Self::Output<B>,
    {
        match self {
            Either::Left(l) => Either::Left(l.clone()),
            Either::Right(r) => f(r),
        }
    }

    #[inline]
    fn join<B>(&self) -> Self::Output<B>
    where
        Self::Source: Into<Self::Output<B>>,
    {
        match self {
            Either::Left(l) => Either::Left(l.clone()),
            Either::Right(r) => r.clone().into(),
        }
    }

    #[inline]
    fn bind_owned<U, F>(self, f: F) -> Self::Output<U>
    where
        F: FnOnce(Self::Source) -> Self::Output<U>,
        Self: Sized,
    {
        match self {
            Either::Left(l) => Either::Left(l),
            Either::Right(r) => f(r),
        }
    }

    #[inline]
    fn join_owned<U>(self) -> Self::Output<U>
    where
        Self::Source: Into<Self::Output<U>>,
        Self: Sized,
    {
        match self {
            Either::Left(l) => Either::Left(l),
            Either::Right(r) => r.into(),
        }
    }
}

/// WARNING: The `Identity` trait implementation for `Either` is logically unsound and should be used with caution.
/// `Either<L, R>` can contain either a value of type `L` or `R`, but the `Identity` trait treats `R` as the
/// primary type, which is arbitrary and potentially confusing. This implementation can easily lead to runtime panics
/// when used with `Either::Left` values.
///
/// # Recommended Alternative
///
/// Instead of using the `Identity` trait methods, prefer the explicit methods `is_right()`, `right_value()`,
/// `right_ref()`, and `right_option()` which make the behavior more obvious and provide safer alternatives
/// that don't panic unexpectedly.
impl<L: Clone, R: Clone> Identity for Either<L, R> {
    #[inline]
    /// Returns a reference to the contained `Right` value.
    ///
    /// # Panics
    ///
    /// This method will panic if called on an `Either::Left` variant. This makes the `Identity` implementation
    /// for `Either` inherently unsound, as it can only safely operate on half of the possible values.
    /// Consider using `right_ref()` in combination with `is_right()` for a safer alternative.
    fn value(&self) -> &Self::Source {
        match self {
            Either::Left(_) => panic!("Cannot get value from Left variant"),
            Either::Right(r) => r,
        }
    }

    #[inline]
    fn pure_identity<A>(value: A) -> Self::Output<A>
    where
        Self::Output<A>: Identity,
    {
        Either::Right(value)
    }

    #[inline]
    /// Consumes the `Either` and returns the contained `Right` value.
    ///
    /// # Panics
    ///
    /// This method will panic if called on an `Either::Left` variant. This makes the `Identity` implementation
    /// for `Either` inherently unsound, as it can only safely operate on half of the possible values.
    /// Consider using `right_value()` in combination with `is_right()` for a safer alternative, or use
    /// pattern matching which handles both variants safely.
    fn into_value(self) -> Self::Source {
        match self {
            Either::Left(_) => panic!("Called into_value on an Either::Left"),
            Either::Right(r) => r,
        }
    }
}

impl<L, R> Composable for Either<L, R> {}

/// Implementation of `MonadPlus` for `Either`, which provides zero and plus operations.
///
/// # Type Parameters
///
/// * `L`: The left type, which must implement `Default + Clone`. The `Default` requirement is needed
///   to create the zero element (`mzero`) by producing a `Left(L::default())` value.
/// * `R`: The right type, which must implement `Clone` for all operations.
///
/// # Implementation Notes
///
/// - `mzero<U>()` returns `Either::Left(L::default())`, representing a failure or empty value.
/// - `mplus` combines two `Either` values, preferring `Right` values over `Left` values.
///   If both are `Left`, the first value is kept.
///
/// # Examples
///
/// ```rust
/// use rustica::datatypes::either::Either;
/// use rustica::traits::monad_plus::MonadPlus;
///
/// // Zero produces a Left with the default value
/// let zero = Either::<String, i32>::mzero::<i32>(); // Either::Left(String::default())
///
/// // Plus prefers Right values
/// let a: Either<String, i32> = Either::right(42);
/// let b: Either<String, i32> = Either::left("error".to_string());
/// assert_eq!(a.mplus(&b), Either::right(42)); // Right preferred over Left
/// assert_eq!(b.mplus(&a), Either::right(42)); // Right preferred over Left
/// ```
impl<L: Default + Clone, R: Clone> MonadPlus for Either<L, R> {
    /// Returns a zero element of the `MonadPlus` instance as `Either::Left(L::default())`.
    ///
    /// # Type Parameters
    ///
    /// * `U`: The right type of the resulting `Either` (can differ from `R`)
    ///
    /// # Requirements
    ///
    /// Requires `L: Default` to create the default value for the `Left` variant.
    fn mzero<U: Clone>() -> Self::Output<U> {
        Either::Left(L::default().clone())
    }

    /// Combines two `Either` values, preferring `Right` values over `Left` values.
    /// If both are `Left`, the first value is kept.
    ///
    /// # Performance
    ///
    /// - Time complexity: O(1) for the operation, O(n) for cloning where n is the size
    ///   of the contained value.
    /// - Space complexity: O(1).
    fn mplus(&self, other: &Self) -> Self {
        match (self, other) {
            (Either::Right(_), _) => self.clone(),
            (Either::Left(_), Either::Right(_)) => other.clone(),
            (Either::Left(_), Either::Left(_)) => self.clone(),
        }
    }

    /// Owned version of `mplus` that consumes both inputs.
    /// Combines two `Either` values, preferring `Right` values over `Left` values.
    /// If both are `Left`, the first value is kept.
    ///
    /// # Performance
    ///
    /// - Time complexity: O(1).
    /// - Space complexity: O(1).
    fn mplus_owned(self, other: Self) -> Self
    where
        Self: Sized,
    {
        match (&self, &other) {
            (Either::Right(_), _) => self,
            (Either::Left(_), Either::Right(_)) => other,
            (Either::Left(_), Either::Left(_)) => self,
        }
    }
}

/// Implementation of `Alternative` for `Either`, which provides choice between alternatives.
///
/// # Type Parameters
///
/// * `L`: The left type, which must implement `Default + Clone`. The `Default` requirement is needed
///   to create empty/failure values using `L::default()`.
/// * `R`: The right type, which must implement `Clone` for all operations.
///
/// # Implementation Notes
///
/// - `empty_alt<B>()` returns `Either::Left(L::default())`, representing a failure or empty value.
/// - `alt` chooses between two `Either` values, preferring `Right` values over `Left` values.
///
/// # Examples
///
/// ```rust
/// use rustica::datatypes::either::Either;
/// use rustica::traits::alternative::Alternative;
///
/// // Empty produces a Left with the default value
/// let empty = Either::<String, i32>::empty_alt::<i32>(); // Either::Left(String::default())
///
/// // Alt prefers Right values (success) over Left values (failure)
/// let a: Either<String, i32> = Either::right(42);
/// let b: Either<String, i32> = Either::left("error".to_string());
/// assert_eq!(a.alt(&b), Either::right(42)); // First Right wins
/// assert_eq!(b.alt(&a), Either::right(42)); // Prefers Right over Left
/// ```
impl<L: Default + Clone, R: Clone> Alternative for Either<L, R> {
    /// Returns an empty element of the `Alternative` instance as `Either::Left(L::default())`.
    ///
    /// # Type Parameters
    ///
    /// * `B`: The right type of the resulting `Either` (can differ from `R`)
    ///
    /// # Requirements
    ///
    /// Requires `L: Default` to create the default value for the `Left` variant.
    #[inline]
    fn empty_alt<B>() -> Self::Output<B> {
        Either::Left(L::default())
    }

    /// Chooses between two `Either` values, preferring `Right` values over `Left` values.
    /// If `self` is `Right`, it is returned; otherwise, `other` is returned.
    ///
    /// # Performance
    ///
    /// - Time complexity: O(1) for the operation, O(n) for cloning where n is the size
    ///   of the contained value.
    /// - Space complexity: O(1).
    #[inline]
    fn alt(&self, other: &Self) -> Self {
        match self {
            Either::Right(_) => self.clone(),
            Either::Left(_) => other.clone(),
        }
    }

    /// Creates an `Either` based on a boolean condition.
    /// Returns `Either::Right(())` if the condition is true, otherwise returns `Either::Left(L::default())`.
    ///
    /// # Requirements
    ///
    /// Requires `L: Default` to create the default value for the `Left` variant when the condition is false.
    ///
    /// # Performance
    ///
    /// - Time complexity: O(1).
    /// - Space complexity: O(1).
    fn guard(condition: bool) -> Self::Output<()> {
        if condition {
            Either::Right(())
        } else {
            Either::Left(L::default())
        }
    }

    /// Converts a single value to a collection containing that value.
    /// Returns `Either::Right(vec![x])` if `self` is `Right(x)`,
    /// otherwise returns `Either::Left(L::default())` if `self` is `Left`.
    ///
    /// # Requirements
    ///
    /// Requires `L: Default` to create the default value for the `Left` variant.
    /// Requires `R: Clone` to clone the value for the vector.
    ///
    /// # Performance
    ///
    /// - Time complexity: O(1).
    /// - Space complexity: O(1) plus the size of the cloned value.
    #[inline]
    fn many(&self) -> Self::Output<Vec<Self::Source>>
    where
        Self::Source: Clone,
    {
        match self {
            Either::Right(x) => Either::Right(vec![x.clone()]),
            Either::Left(_) => Either::Left(L::default()),
        }
    }
}

// Iterator support for Either
/// An iterator over the right value of an `Either<L, R>`.
pub struct EitherIter<R> {
    inner: Option<R>,
}

impl<L, R> IntoIterator for Either<L, R> {
    type Item = R;
    type IntoIter = EitherIter<R>;
    /// Converts the `Either` into an iterator over the right value.
    ///
    /// If the value is `Right`, yields the contained value. If `Left`, yields nothing.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::either::Either;
    /// let e: Either<&str, i32> = Either::right(42);
    /// let v: Vec<_> = e.into_iter().collect();
    /// assert_eq!(v, vec![42]);
    /// let e: Either<&str, i32> = Either::left("err");
    /// let v: Vec<_> = e.into_iter().collect();
    /// assert!(v.is_empty());
    /// ```
    fn into_iter(self) -> Self::IntoIter {
        match self {
            Either::Right(r) => EitherIter { inner: Some(r) },
            Either::Left(_) => EitherIter { inner: None },
        }
    }
}

impl<R> Iterator for EitherIter<R> {
    type Item = R;
    fn next(&mut self) -> Option<R> {
        self.inner.take()
    }
}

/// An iterator over a reference to the right value of an `Either<L, R>`.
pub struct EitherIterRef<'a, R> {
    inner: Option<&'a R>,
}

impl<'a, L, R> IntoIterator for &'a Either<L, R> {
    type Item = &'a R;
    type IntoIter = EitherIterRef<'a, R>;
    /// Converts a reference to `Either` into an iterator over a reference to the right value.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::either::Either;
    /// let e: Either<&str, i32> = Either::right(42);
    /// let v: Vec<_> = (&e).into_iter().collect();
    /// assert_eq!(v, vec![&42]);
    /// let e: Either<&str, i32> = Either::left("err");
    /// let v: Vec<_> = (&e).into_iter().collect::<Vec<_>>();
    /// assert!(v.is_empty());
    /// ```
    fn into_iter(self) -> Self::IntoIter {
        match self {
            Either::Right(r) => EitherIterRef { inner: Some(r) },
            Either::Left(_) => EitherIterRef { inner: None },
        }
    }
}

impl<'a, R> Iterator for EitherIterRef<'a, R> {
    type Item = &'a R;
    fn next(&mut self) -> Option<&'a R> {
        self.inner.take()
    }
}

/// An iterator over a mutable reference to the right value of an `Either<L, R>`.
pub struct EitherIterMut<'a, R> {
    inner: Option<&'a mut R>,
}

impl<'a, L, R> IntoIterator for &'a mut Either<L, R> {
    type Item = &'a mut R;
    type IntoIter = EitherIterMut<'a, R>;
    /// Converts a mutable reference to `Either` into an iterator over a mutable reference to the right value.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::either::Either;
    /// let mut e: Either<&str, i32> = Either::right(42);
    /// for v in &mut e {
    ///     *v += 1;
    /// }
    /// assert_eq!(e, Either::right(43));
    /// ```
    fn into_iter(self) -> Self::IntoIter {
        match self {
            Either::Right(r) => EitherIterMut { inner: Some(r) },
            Either::Left(_) => EitherIterMut { inner: None },
        }
    }
}

impl<'a, R> Iterator for EitherIterMut<'a, R> {
    type Item = &'a mut R;
    fn next(&mut self) -> Option<&'a mut R> {
        self.inner.take()
    }
}

#[cfg(feature = "full")]
impl<L, R> Arbitrary for Either<L, R>
where
    L: Arbitrary,
    R: Arbitrary,
{
    fn arbitrary(g: &mut Gen) -> Self {
        let left = L::arbitrary(g);
        let right = R::arbitrary(g);
        if bool::arbitrary(g) {
            Either::Left(left)
        } else {
            Either::Right(right)
        }
    }
}
