//! # Identity Trait
//!
//! This module provides the `Identity` trait, which represents identity functions in category theory
//! and provides functionality for working with container types that can provide access to their
//! contained values.
//!
//! ## Category Theory Background
//!
//! In category theory, an identity morphism (or identity function) is a morphism that
//! leaves an object unchanged. The Identity trait provides functionality for working
//! with identity functions and accessing values in a type-safe way.
//!
//! ## Identity Laws
//!
//! Types implementing `Identity` should adhere to the following laws:
//!
//! 1. **Left identity**: `identity.pure_identity(a).map(f) == f(a)`
//! 2. **Right identity**: `identity.map(Identity::id) == identity`
//!
//! ## Examples
//!
//! ```rust
//! use rustica::traits::hkt::HKT;
//! use rustica::traits::identity::Identity;
//!
//! // A simple wrapper type
//! struct Wrapper<T>(T);
//!
//! impl<T> HKT for Wrapper<T> {
//!     type Source = T;
//!     type Output<U> = Wrapper<U>;
//! }
//!
//! impl<T> Identity for Wrapper<T> {
//!     #[inline]
//!     fn value(&self) -> &Self::Source {
//!         &self.0
//!     }
//!     
//!     #[inline]
//!     fn into_value(self) -> Self::Source {
//!         self.0
//!     }
//!
//!     #[inline]
//!     fn pure_identity<A>(value: A) -> Self::Output<A> {
//!         Wrapper(value)
//!     }
//! }
//!
//! // Using the Identity trait
//! let wrapped: Wrapper<i32> = Wrapper(42);
//! assert_eq!(*wrapped.value(), 42);
//!
//! // Using the identity function
//! let x: i32 = 5;
//! assert_eq!(<Wrapper<i32> as Identity>::id(x), 5);
//! ```
//!
//! ## TODO: Future Improvements
//!
//! - **Extended Examples**: Add more examples showing integration with other functional traits
//! - **Performance Benchmarks**: Add documentation about performance characteristics
//! - **Implementation Guidelines**: Add guidelines for correctly implementing the trait
//! - **Type Safety**: Enhance documentation around type safety considerations
//! - **Additional Extensions**: Consider adding more utility methods to the `IdentityExt` trait

use crate::traits::hkt::HKT;

/// A trait for types that represent identity functions in category theory.
///
/// In category theory, an identity morphism (or identity function) is a morphism that
/// leaves an object unchanged. The Identity trait provides functionality for working
/// with identity functions and accessing values in a type-safe way.
///
/// # Laws
///
/// Types implementing `Identity` should adhere to the following laws:
///
/// 1. **Left identity**: `identity.pure_identity(a).map(f) == f(a)`
/// 2. **Right identity**: `identity.map(Identity::id) == identity`
///
/// # Examples
///
/// ```rust
/// use rustica::traits::hkt::HKT;
/// use rustica::traits::identity::Identity;
///
/// // A simple wrapper type
/// struct Wrapper<T>(T);
///
/// impl<T> HKT for Wrapper<T> {
///     type Source = T;
///     type Output<U> = Wrapper<U>;
/// }
///
/// impl<T> Identity for Wrapper<T> {
///     fn value(&self) -> &Self::Source {
///         &self.0
///     }
///     
///     fn into_value(self) -> Self::Source {
///         self.0
///     }
///
///     fn pure_identity<A>(value: A) -> Self::Output<A> {
///         Wrapper(value)
///     }
/// }
///
/// // Using the Identity trait
/// let wrapped: Wrapper<i32> = Wrapper(42);
/// assert_eq!(*wrapped.value(), 42);
///
/// // Using the identity function
/// let x: i32 = 5;
/// assert_eq!(<Wrapper<i32> as Identity>::id(x), 5);
/// ```
pub trait Identity: HKT {
    /// Returns a reference to the contained value.
    ///
    /// # Panics
    ///
    /// This method may panic if the container doesn't contain a valid value.
    /// For a non-panicking alternative, use `try_value()`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::traits::identity::Identity;
    ///
    /// // For an Option:
    /// let some_value: Option<i32> = Some(42);
    /// assert_eq!(*some_value.value(), 42);
    ///
    /// // This would panic:
    /// // let none_value: Option<i32> = None;
    /// // none_value.value(); // panics
    /// ```
    fn value(&self) -> &Self::Source;

    /// Returns a reference to the contained value, if available.
    ///
    /// This method is safer than `value()` as it returns an `Option`
    /// instead of potentially panicking.
    ///
    /// # Default Implementation
    ///
    /// By default, this calls `value()` and wraps the result in `Some`.
    /// Types that might not contain a value should override this method.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::traits::identity::Identity;
    ///
    /// // For an Option:
    /// let some_value: Option<i32> = Some(42);
    /// assert_eq!(some_value.try_value(), Some(&42));
    ///
    /// let none_value: Option<i32> = None;
    /// assert_eq!(none_value.try_value(), None);
    /// ```
    #[inline]
    fn try_value(&self) -> Option<&Self::Source> {
        Some(self.value())
    }

    /// Consumes self and returns the contained value.
    ///
    /// # Panics
    ///
    /// This method may panic if the container doesn't contain a valid value.
    /// For a non-panicking alternative, use `try_into_value()`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::traits::identity::Identity;
    ///
    /// // For an Option:
    /// let some_value: Option<i32> = Some(42);
    /// assert_eq!(some_value.into_value(), 42);
    ///
    /// // This would panic:
    /// // let none_value: Option<i32> = None;
    /// // none_value.into_value(); // panics
    /// ```
    fn into_value(self) -> Self::Source;

    /// Consumes self and returns the contained value, if available.
    ///
    /// This method is safer than `into_value()` as it returns an `Option`
    /// instead of potentially panicking.
    ///
    /// # Default Implementation
    ///
    /// By default, this method attempts to obtain the value using `into_value()`.
    /// Types that might not contain a value should override this method.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::traits::identity::Identity;
    ///
    /// // For an Option:
    /// let some_value: Option<i32> = Some(42);
    /// assert_eq!(some_value.try_into_value(), Some(42));
    ///
    /// let none_value: Option<i32> = None;
    /// assert_eq!(none_value.try_into_value(), None);
    /// ```
    #[inline]
    fn try_into_value(self) -> Option<Self::Source>
    where
        Self: Sized,
    {
        Some(self.into_value())
    }

    /// The identity function, which returns its input unchanged.
    ///
    /// This function serves as the identity morphism in category theory.
    ///
    /// # Type Parameters
    ///
    /// * `A`: The type of the input value
    ///
    /// # Arguments
    ///
    /// * `a`: The value to return unchanged
    #[inline]
    fn id<A>(a: A) -> A {
        a
    }

    /// Creates an identity instance containing the given value.
    ///
    /// This is a convenience method for creating a new instance of a type
    /// that implements `Identity`.
    ///
    /// # Type Parameters
    ///
    /// * `A`: The type of the value to wrap
    ///
    /// # Arguments
    ///
    /// * `value`: The value to wrap
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::traits::identity::Identity;
    ///
    /// // For an Option:
    /// let value: i32 = 42;
    /// let option = <Option<i32> as Identity>::pure_identity(value);
    /// assert_eq!(option, Some(42));
    /// ```
    fn pure_identity<A>(value: A) -> Self::Output<A>
    where
        Self::Output<A>: Identity;
}

// Standard Library Implementations

impl<T> Identity for Option<T> {
    #[inline]
    fn value(&self) -> &Self::Source {
        self.as_ref().expect("Option is None")
    }

    #[inline]
    fn try_value(&self) -> Option<&Self::Source> {
        self.as_ref()
    }

    #[inline]
    fn into_value(self) -> Self::Source {
        self.expect("Option is None")
    }

    #[inline]
    fn try_into_value(self) -> Option<Self::Source> {
        self
    }

    #[inline]
    fn pure_identity<A>(value: A) -> Self::Output<A> {
        Some(value)
    }
}

impl<T, E: Clone + std::fmt::Debug> Identity for Result<T, E> {
    #[inline]
    fn value(&self) -> &Self::Source {
        self.as_ref().expect("Result is Err")
    }

    #[inline]
    fn try_value(&self) -> Option<&Self::Source> {
        self.as_ref().ok()
    }

    #[inline]
    fn into_value(self) -> Self::Source {
        self.expect("Result is Err")
    }

    #[inline]
    fn try_into_value(self) -> Option<Self::Source> {
        self.ok()
    }

    #[inline]
    fn pure_identity<A>(value: A) -> Self::Output<A> {
        Ok(value)
    }
}

impl<T> Identity for Vec<T> {
    #[inline]
    fn value(&self) -> &Self::Source {
        self.first().expect("Vec is empty")
    }

    #[inline]
    fn try_value(&self) -> Option<&Self::Source> {
        self.first()
    }

    #[inline]
    fn into_value(self) -> Self::Source {
        self.into_iter().next().expect("Vec is empty")
    }

    #[inline]
    fn try_into_value(self) -> Option<Self::Source> {
        self.into_iter().next()
    }

    #[inline]
    fn pure_identity<A>(value: A) -> Self::Output<A> {
        vec![value]
    }
}

/// Extension trait providing additional identity-related functionality.
///
/// This trait extends the base `Identity` trait with more specialized
/// methods for working with identities in a functional programming context.
///
/// # Examples
///
/// ```rust
/// use rustica::traits::identity::{Identity, IdentityExt};
///
/// let opt: Option<i32> = Some(42);
///
/// // Access value or fallback to default
/// assert_eq!(opt.value_or(&0), &42);
///
/// let none: Option<i32> = None;
/// assert_eq!(none.value_or(&0), &0);
/// ```
pub trait IdentityExt: Identity {
    /// Returns a reference to the contained value or a provided reference.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::traits::identity::{Identity, IdentityExt};
    ///
    /// let some_value: Option<i32> = Some(42);
    /// let fallback = 10;
    /// assert_eq!(some_value.value_or(&fallback), &42);
    ///
    /// let none_value: Option<i32> = None;
    /// assert_eq!(none_value.value_or(&fallback), &10);
    /// ```
    #[inline]
    fn value_or<'a>(&'a self, default: &'a Self::Source) -> &'a Self::Source {
        self.try_value().unwrap_or(default)
    }

    /// Maps a function over the value if it exists, or returns a default.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::traits::identity::{Identity, IdentityExt};
    /// use rustica::traits::hkt::HKT;
    ///
    /// let some_value: Option<i32> = Some(42);
    /// let result = some_value.map_or_else(|| 0, |x| x * 2);
    /// assert_eq!(result, 84);
    ///
    /// let none_value: Option<i32> = None;
    /// let result = none_value.map_or_else(|| 0, |x| x * 2);
    /// assert_eq!(result, 0);
    /// ```
    #[inline]
    fn map_or_else<F, D, R>(&self, default: D, f: F) -> R
    where
        F: Fn(&Self::Source) -> R,
        D: Fn() -> R,
    {
        match self.try_value() {
            Some(value) => f(value),
            None => default(),
        }
    }
}

// Blanket implementation for all types implementing Identity
impl<T: Identity> IdentityExt for T {}
