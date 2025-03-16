//! # Pure
//!
//! The `Pure` module provides the `Pure` trait, which represents the ability to lift values
//! into a higher-kinded context. This is one of the fundamental operations in
//! functional programming, often called `return` or `unit` in other languages.
//!
//! # Mathematical Definition
//!
//! In category theory, `pure` corresponds to the η (eta) natural transformation that
//! maps values from a category to a Monad. The following laws should hold:
//!
//! - Left identity: `pure(x).bind(f) == f(x)`
//! - Right identity: `m.bind(pure) == m`
//!
//! where `bind` is the bind operation from the Monad trait.
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
//! let option: Option<i32> = <Option<i32> as Pure>::pure(&value);
//! assert_eq!(option, Some(42));
//!
//! // Using pure with Result
//! let result: Result<i32, &str> = <Result<i32, &str> as Pure>::pure(&value);
//! assert_eq!(result, Ok(42));
//!
//! // Using pure with Vec
//! let vec: Vec<i32> = <Vec<i32> as Pure>::pure(&value);
//! assert_eq!(vec, vec![42]);
//! ```
//!
//! # Extension Traits
//!
//! The `PureExt` trait provides extension methods for working with values that can be
//! lifted into a context:
//!
//! ```rust
//! use rustica::traits::hkt::HKT;
//! use rustica::traits::pure::{Pure, PureExt};
//!
//! // Using the to_pure extension method
//! let value: i32 = 42;
//! let option: Option<i32> = value.to_pure::<Option<i32>>();
//! assert_eq!(option, Some(42));
//!
//! // Using pair_with to combine two values
//! let a: i32 = 42;
//! let b: &str = "hello";
//! let pair: Option<(i32, &str)> = a.pair_with::<Option<(i32, &str)>, &str>(&b);
//! assert_eq!(pair, Some((42, "hello")));
//!
//! // Using lift_other to lift a value into the same context
//! let a: i32 = 42;
//! let b: &str = "hello";
//! let lifted: Option<&str> = a.lift_other::<Option<&str>, &str>(&b);
//! assert_eq!(lifted, Some("hello"));
//! ```

use crate::traits::hkt::HKT;
use std::marker::PhantomData;

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
///     fn pure<U: Clone>(value: &U) -> Self::Output<U> {
///         MyWrapper(value.clone())
///     }
///
///     // We can provide a more efficient implementation for pure_owned
///     fn pure_owned<U>(value: U) -> Self::Output<U> {
///         MyWrapper(value)
///     }
/// }
///
/// // Using our Pure implementation
/// let wrapped: MyWrapper<i32> = MyWrapper::<()>::pure(&42);
/// ```
pub trait Pure: HKT {
    /// Lift a value into a context.
    ///
    /// This method creates a new instance of the higher-kinded type containing the provided value.
    /// It operates on a reference to the value, which is cloned into the context.
    ///
    /// # Type Parameters
    /// * `T`: The type of the value to lift
    ///
    /// # Parameters
    /// * `value`: A reference to the value to lift
    ///
    /// # Returns
    /// A new instance of the higher-kinded type containing the value
    ///
    /// # Examples
    /// ```rust
    /// use rustica::traits::hkt::HKT;
    /// use rustica::traits::pure::Pure;
    ///
    /// let x = 42;
    /// let option: Option<i32> = <Option<i32> as Pure>::pure(&x);
    /// assert_eq!(option, Some(42));
    /// ```
    fn pure<T: Clone>(value: &T) -> Self::Output<T>;

    /// Lift a value into a context, consuming the value.
    ///
    /// This method is an ownership-based variant of `pure` that consumes the provided value
    /// instead of cloning it. This can be more efficient when the original value is no longer needed.
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
    /// let option: Option<i32> = <Option<i32> as Pure>::pure_owned(42);
    /// assert_eq!(option, Some(42));
    /// ```
    #[inline]
    fn pure_owned<T: Clone>(value: T) -> Self::Output<T> {
        Self::pure(&value)
    }
}

// Standard Library Implementations

impl<T> Pure for Option<T> {
    #[inline]
    fn pure<U: Clone>(value: &U) -> Self::Output<U> {
        Some(value.clone())
    }

    #[inline]
    fn pure_owned<U>(value: U) -> Self::Output<U> {
        Some(value)
    }
}

impl<T, E: Clone> Pure for Result<T, E> {
    #[inline]
    fn pure<U: Clone>(value: &U) -> Self::Output<U> {
        Ok(value.clone())
    }

    #[inline]
    fn pure_owned<U>(value: U) -> Self::Output<U> {
        Ok(value)
    }
}

impl<T> Pure for Vec<T> {
    #[inline]
    fn pure_owned<U>(value: U) -> Self::Output<U> {
        vec![value]
    }

    #[inline]
    fn pure<U: Clone>(value: &U) -> Self::Output<U> {
        vec![value.clone()]
    }
}

impl<T> Pure for Box<T> {
    #[inline]
    fn pure_owned<U>(value: U) -> Self::Output<U> {
        Box::new(value)
    }

    #[inline]
    fn pure<U: Clone>(value: &U) -> Self::Output<U> {
        Box::new(value.clone())
    }
}

/// Extension trait providing a more ergonomic way to use Pure.
///
/// This trait allows calling methods like `to_pure` directly on values, making it more
/// convenient to lift values into higher-kinded contexts and work with them.
///
/// # Implemented For
///
/// This trait is implemented for all types that implement `Clone`, which means
/// it can be used with any cloneable value.
///
/// # Examples
///
/// Using `to_pure` to lift a value into Option:
/// ```rust
/// use rustica::traits::hkt::HKT;
/// use rustica::traits::pure::{Pure, PureExt};
///
/// // Instead of: <Option<i32> as Pure>::pure(&42)
/// // We can write:
/// let value: i32 = 42;
/// let option: Option<i32> = value.to_pure::<Option<i32>>();
/// assert_eq!(option, Some(42));
/// ```
///
/// Chaining operations with the Validated type:
/// ```rust
/// use rustica::traits::hkt::HKT;
/// use rustica::traits::pure::{Pure, PureExt};
/// use rustica::traits::functor::Functor;
/// use rustica::datatypes::validated::Validated;
///
/// let value: i32 = 42;
///
/// // Lift into Validated context and transform
/// let validated: Validated<&str, i32> = value.to_pure::<Validated<&str, i32>>();
/// let doubled: Validated<&str, i32> = validated.fmap(|x: &i32| x * 2);
///
/// assert!(matches!(doubled, Validated::Valid(84)));
/// ```
pub trait PureExt: Sized {
    /// Lift a value into a context.
    ///
    /// This method provides a more ergonomic way to use `Pure::pure`, allowing
    /// you to call it directly on values.
    ///
    /// # Type Parameters
    ///
    /// * `P`: The higher-kinded type to lift into, implementing `Pure`
    ///
    /// # Returns
    ///
    /// The value wrapped in the higher-kinded context
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::traits::hkt::HKT;
    /// use rustica::traits::pure::{Pure, PureExt};
    /// use rustica::datatypes::validated::Validated;
    ///
    /// let x: i32 = 42;
    ///
    /// // Lift into Option
    /// let option: Option<i32> = x.to_pure::<Option<i32>>();
    /// assert_eq!(option, Some(42));
    ///
    /// // Lift into Validated
    /// let validated: Validated<&str, i32> = x.to_pure::<Validated<&str, i32>>();
    /// assert!(matches!(validated, Validated::Valid(42)));
    /// ```
    #[inline]
    fn to_pure<P>(&self) -> P::Output<Self>
    where
        P: Pure,
        Self: Clone,
    {
        P::pure(self)
    }

    /// Lift a value into a context, consuming the value.
    ///
    /// This method provides a more efficient version of `to_pure` that consumes
    /// the value instead of cloning it.
    ///
    /// # Type Parameters
    ///
    /// * `P`: The higher-kinded type to lift into, implementing `Pure`
    ///
    /// # Returns
    ///
    /// The value wrapped in the higher-kinded context
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::traits::hkt::HKT;
    /// use rustica::traits::pure::{Pure, PureExt};
    ///
    /// // Using to_pure_owned (consumes the value)
    /// let option: Option<i32> = 42.to_pure_owned::<Option<i32>>();
    /// assert_eq!(option, Some(42));
    /// ```
    #[inline]
    fn to_pure_owned<P>(self) -> P::Output<Self>
    where
        P: Pure,
        Self: Clone,
    {
        P::pure_owned(self)
    }

    /// Lift a pair of values into a context.
    ///
    /// This method combines two values into a tuple and lifts the result
    /// into a higher-kinded context.
    ///
    /// # Type Parameters
    ///
    /// * `P`: The higher-kinded type to lift into, implementing `Pure`
    /// * `U`: The type of the second value
    ///
    /// # Parameters
    ///
    /// * `other`: A reference to the second value to pair with this one
    ///
    /// # Returns
    ///
    /// A pair of values in the higher-kinded context
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::traits::hkt::HKT;
    /// use rustica::traits::pure::{Pure, PureExt};
    /// use rustica::datatypes::validated::Validated;
    ///
    /// let a: i32 = 42;
    /// let b: &str = "hello";
    ///
    /// // Create a pair in Option context
    /// let option_pair: Option<(i32, &str)> = a.pair_with::<Option<(i32, &str)>, &str>(&b);
    /// assert_eq!(option_pair, Some((42, "hello")));
    ///
    /// // Create a pair in Validated context
    /// let validated_pair: Validated<&str, (i32, &str)> = a.pair_with::<Validated<&str, (i32, &str)>, &str>(&b);
    /// assert!(matches!(validated_pair, Validated::Valid((42, "hello"))));
    /// ```
    #[inline]
    fn pair_with<P, U>(&self, other: &U) -> P::Output<(Self, U)>
    where
        P: Pure,
        Self: Clone,
        U: Clone,
    {
        let pair = (self.clone(), other.clone());
        P::pure(&pair)
    }

    /// Lift another value into a context.
    ///
    /// This method lifts a different value into the same context type.
    /// It's useful for working with applicative functors.
    ///
    /// # Type Parameters
    ///
    /// * `P`: The higher-kinded type to lift into, implementing `Pure`
    /// * `U`: The type of the other value
    ///
    /// # Parameters
    ///
    /// * `other`: A reference to the value to lift
    ///
    /// # Returns
    ///
    /// The other value lifted into the context
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::traits::hkt::HKT;
    /// use rustica::traits::pure::{Pure, PureExt};
    ///
    /// let a: i32 = 42;
    /// let b: &str = "hello";
    ///
    /// // Lift b into the same context as would be used for a
    /// let option_b: Option<&str> = a.lift_other::<Option<&str>, &str>(&b);
    /// assert_eq!(option_b, Some("hello"));
    /// ```
    #[inline]
    fn lift_other<P, U>(&self, other: &U) -> P::Output<U>
    where
        P: Pure,
        U: Clone,
    {
        P::pure(other)
    }

    /// Combine two values into a new value and lift it into a context.
    ///
    /// This method applies a function to two values and lifts the result
    /// into a higher-kinded context. It's particularly useful for applicative-style
    /// programming.
    ///
    /// # Type Parameters
    ///
    /// * `P`: The higher-kinded type to lift into, implementing `Pure`
    /// * `U`: The type of the second value
    /// * `V`: The result type after applying the function
    ///
    /// # Parameters
    ///
    /// * `other`: A reference to the second value to combine with
    /// * `f`: The function to apply to both values
    ///
    /// # Returns
    ///
    /// The result of applying the function to both values, lifted into the context
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::traits::hkt::HKT;
    /// use rustica::traits::pure::{Pure, PureExt};
    ///
    /// let a: i32 = 42;
    /// let b: i32 = 10;
    ///
    /// // Combine values with a function
    /// let result: Option<i32> = a.combine_with::<Option<i32>, i32, i32>(&b, |x, y| x * y);
    /// assert_eq!(result, Some(420));
    /// ```
    #[inline]
    fn combine_with<P, U, V>(&self, other: &U, f: impl Fn(&Self, &U) -> V) -> P::Output<V>
    where
        P: Pure,
        Self: Clone,
        U: Clone,
        V: Clone,
    {
        let result = f(self, other);
        P::pure(&result)
    }
}

impl<T: Clone> PureExt for T {}

/// A zero-cost wrapper for types that implement `Pure`.
///
/// This wrapper uses `PhantomData` to avoid any runtime overhead while
/// still providing a way to specify which `Pure` implementation to use.
///
/// # Type Parameters
///
/// * `P`: The type that implements `Pure`
/// * `T`: The source type of the higher-kinded type
///
/// # Examples
///
/// ```rust
/// use rustica::traits::hkt::HKT;
/// use rustica::traits::pure::{Pure, PureType};
///
/// // Create a PureType with Option as the Pure implementation
/// let pure_option = PureType::<Option<i32>, i32>::new();
///
/// // Use it to lift values
/// let option: Option<i32> = PureType::<Option<i32>, i32>::lift(&42);
/// assert_eq!(option, Some(42));
///
/// // PureType is zero-cost - it doesn't add any runtime overhead
/// assert_eq!(std::mem::size_of::<PureType<Option<i32>, i32>>(), 0);
/// ```
///
/// Using with the Validated type:
///
/// ```rust
/// use rustica::traits::hkt::HKT;
/// use rustica::traits::pure::{Pure, PureType};
/// use rustica::datatypes::validated::Validated;
/// use rustica::traits::functor::Functor;
///
/// // Create Pure wrappers for different contexts
/// let pure_validated = PureType::<Validated<&str, i32>, i32>::new();
///
/// // Lift a value into the Validated context
/// let valid: Validated<&str, i32> = PureType::<Validated<&str, i32>, i32>::lift(&42);
///
/// // We can then use Functor operations on the result
/// let doubled: Validated<&str, i32> = valid.fmap(|x: &i32| x * 2);
/// assert!(matches!(doubled, Validated::Valid(84)));
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct PureType<P, T>(PhantomData<P>, PhantomData<T>);

impl<P, T> PureType<P, T>
where
    P: Pure,
{
    /// Create a new PureType.
    ///
    /// Since this type is zero-sized, this method is essentially a no-op.
    ///
    /// # Returns
    ///
    /// A new PureType instance
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::traits::pure::PureType;
    ///
    /// let pure_option = PureType::<Option<i32>, i32>::new();
    /// ```
    #[inline]
    pub fn new() -> Self {
        PureType(PhantomData, PhantomData)
    }

    /// Lift a value into a context.
    ///
    /// This method lifts a value into the context specified by the `P` type parameter.
    ///
    /// # Type Parameters
    ///
    /// * `U`: The type of the value to lift
    ///
    /// # Parameters
    ///
    /// * `value`: A reference to the value to lift
    ///
    /// # Returns
    ///
    /// The value lifted into the context
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::traits::pure::{Pure, PureType};
    /// use rustica::datatypes::validated::Validated;
    ///
    /// let pure_validated = PureType::<Validated<&str, i32>, i32>::new();
    ///
    /// let valid: Validated<&str, i32> = PureType::<Validated<&str, i32>, i32>::lift(&42);
    /// assert!(matches!(valid, Validated::Valid(42)));
    /// ```
    #[inline]
    pub fn lift<U: Clone>(value: &U) -> P::Output<U> {
        P::pure(value)
    }

    /// Lift a value into a context, consuming the value.
    ///
    /// This method lifts a value into the context specified by the `P` type parameter,
    /// consuming the value instead of cloning it.
    ///
    /// # Type Parameters
    ///
    /// * `U`: The type of the value to lift
    ///
    /// # Parameters
    ///
    /// * `value`: The value to lift, which will be consumed
    ///
    /// # Returns
    ///
    /// The value lifted into the context
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::traits::pure::{Pure, PureType};
    /// use rustica::datatypes::validated::Validated;
    ///
    /// let pure_validated = PureType::<Validated<&str, i32>, i32>::new();
    ///
    /// let valid: Validated<&str, i32> = PureType::<Validated<&str, i32>, i32>::lift_owned(42);
    /// assert!(matches!(valid, Validated::Valid(42)));
    /// ```
    #[inline]
    pub fn lift_owned<U: Clone>(value: U) -> P::Output<U> {
        P::pure_owned(value)
    }
}

// Default implementation
impl<P: Pure, T> Default for PureType<P, T> {
    /// Create a default PureType.
    ///
    /// This method returns a new PureType instance.
    ///
    /// # Returns
    ///
    /// A new PureType instance
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::traits::pure::PureType;
    /// use std::default::Default;
    ///
    /// let pure_option: PureType<Option<i32>, i32> = Default::default();
    /// ```
    #[inline]
    fn default() -> Self {
        Self::new()
    }
}
