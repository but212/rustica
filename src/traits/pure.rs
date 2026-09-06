//! # Pure
//!
//! The `Pure` module provides the `Pure` trait, which represents the ability to lift values
//! into a higher-kinded context. This is one of the fundamental operations in
//! functional programming, often called `return` or `unit` in other languages.
//!
//! # Mathematical Definition
//!
//! In category theory, `pure` corresponds to the η (eta) natural transformation that
//! maps values into a context.
//!
//! Note: laws involving `bind` (Monad) or `apply` (Applicative) only apply once `Pure` is used
//! together with those additional structures.
//!
//! # Core Concepts
//!
//! In functional programming, the ability to lift a value into a context is essential
//! for building composable abstractions. The `Pure` trait serves as the foundation for:
//!
//! - **Applicative Functors**: `pure` is one of the core operations of Applicative
//! - **Monads**: `pure` is equivalent to the `return` operation in monads
//! - **Effect Systems**: Wrapping values in computational contexts
//!
//! # Examples
//!
//! ```rust
//! use rustica::traits::hkt::HKT;
//! use rustica::traits::pure::Pure;
//!
//! // Using pure with Option
//! let value: i32 = 42;
//! let option: Option<i32> = <Option<i32> as Pure>::pure(value);
//! assert_eq!(option, Some(42));
//!
//! // Using pure with Result
//! let result: Result<i32, &str> = <Result<i32, &str> as Pure>::pure(value);
//! assert_eq!(result, Ok(42));
//!
//! // Using pure with Vec
//! let vec: Vec<i32> = <Vec<i32> as Pure>::pure(value);
//! assert_eq!(vec, vec![42]);
//! ```
//!
//! # Extension Traits
//!
//! `PureExt` provides value-oriented helpers such as `to_pure`, `pair_with`, and
//! `lift_other`. Each method documents one concise invocation below its definition.

use crate::traits::hkt::HKT;

/// A trait for types that can lift values into a higher-kinded context.
///
/// The `Pure` trait provides the fundamental operation of "lifting" a regular value
/// into a context. This is a core concept in functional programming, often referred to
/// as `return` or `unit` in other languages and frameworks.
///
/// # Type Parameters
/// The trait inherits type parameters from `HKT`:
/// * `Source`: The type of values being transformed
/// * `Output<T>`: The result type after transformation
///
/// # Laws
/// For a valid Pure implementation, the following laws must hold:
///
/// Note: the laws below are stated in terms of `fmap` and `apply`, so they apply when the
/// implementing type also forms a lawful `Functor`/`Applicative`.
///
/// 1. Identity Preservation:
///    ```text
///    pure(x).fmap(id) == pure(x)
///    ```
///    Lifting a value and then mapping the identity function over it should yield the same result.
///
/// 2. Homomorphism:
///    ```text
///    pure(f(x)) == pure(f).apply(pure(x))
///    ```
///    Applying a function to a value and then lifting the result should be the same as
///    lifting both the function and the value and then applying them.
///
/// # Examples
///
/// Basic implementation for a custom type:
/// ```rust
/// use rustica::traits::hkt::HKT;
/// use rustica::traits::pure::Pure;
///
/// // A simple wrapper type
/// struct MyWrapper<T>(T);
///
/// impl<T> HKT for MyWrapper<T> {
///     type Source = T;
///     type Output<U> = MyWrapper<U>;
/// }
///
/// impl<T> Pure for MyWrapper<T> {
///     fn pure<U>(value: U) -> Self::Output<U> {
///         MyWrapper(value)
///     }
/// }
///
/// // Using our Pure implementation
/// let wrapped: MyWrapper<i32> = MyWrapper::<()>::pure(42);
/// ```
pub trait Pure: HKT {
    /// Lift a value into a context, consuming the value.
    ///
    /// This method creates a new instance of the higher-kinded type containing the provided value.
    ///
    /// # Type Parameters
    /// * `T`: The type of the value to lift
    ///
    /// # Parameters
    /// * `value`: The value to lift, which will be consumed
    ///
    /// # Returns
    /// A new instance of the higher-kinded type containing the value
    ///
    /// # Examples
    /// ```rust
    /// use rustica::traits::hkt::HKT;
    /// use rustica::traits::pure::Pure;
    ///
    /// let option: Option<i32> = <Option<i32> as Pure>::pure(42);
    /// assert_eq!(option, Some(42));
    /// ```
    fn pure<T>(value: T) -> Self::Output<T>;
}

// Standard Library Implementations

impl<T> Pure for Option<T> {
    #[inline]
    fn pure<U>(value: U) -> Self::Output<U> {
        Some(value)
    }
}

impl<T, E: Clone> Pure for Result<T, E> {
    #[inline]
    fn pure<U>(value: U) -> Self::Output<U> {
        Ok(value)
    }
}

impl<T> Pure for Vec<T> {
    #[inline]
    fn pure<U>(value: U) -> Self::Output<U> {
        vec![value]
    }
}

impl<T> Pure for Box<T> {
    #[inline]
    fn pure<U>(value: U) -> Self::Output<U> {
        Box::new(value)
    }
}

/// Extension trait providing a more ergonomic way to use Pure.
///
/// This trait allows calling methods like `to_pure` directly on values, making it more
/// convenient to lift values into higher-kinded contexts and work with them.
///
/// # Examples
///
/// Using `to_pure` to lift a value into Option:
/// ```rust
/// use rustica::traits::hkt::HKT;
/// use rustica::traits::pure::{Pure, PureExt};
///
/// let value: i32 = 42;
/// let option: Option<i32> = value.to_pure::<Option<i32>>();
/// assert_eq!(option, Some(42));
/// ```
pub trait PureExt: Sized {
    /// Lift a value into a context, consuming the value.
    ///
    /// # Type Parameters
    /// * `P`: The higher-kinded type to lift into, implementing `Pure`
    ///
    /// # Returns
    /// The value wrapped in the higher-kinded context
    #[inline]
    fn to_pure<P>(self) -> P::Output<Self>
    where
        P: Pure,
    {
        P::pure(self)
    }

    /// Lift a pair of values into a context.
    #[inline]
    fn pair_with<P, U>(self, other: U) -> P::Output<(Self, U)>
    where
        P: Pure,
    {
        P::pure((self, other))
    }

    /// Lift another value into a context.
    #[inline]
    fn lift_other<P, U>(&self, other: U) -> P::Output<U>
    where
        P: Pure,
    {
        P::pure(other)
    }

    /// Combine two values into a new value and lift it into a context.
    #[inline]
    fn combine_with<P, U, V>(self, other: U, f: impl FnOnce(Self, U) -> V) -> P::Output<V>
    where
        P: Pure,
    {
        P::pure(f(self, other))
    }
}

impl<T> PureExt for T {}
