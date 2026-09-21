//! # Functor
//!
//! The `Functor` module provides trait definitions for implementing functors
//! in Rust, a fundamental abstraction in functional programming.
//!
//! A functor is a type constructor that supports a mapping operation which preserves
//! the structure of the functor while transforming its contents.
//!
//! ## Quick Start
//!
//! Transform values while preserving structure:
//!
//! ```rust
//! use rustica::traits::functor::Functor;
//!
//! // Transform values in context
//! let numbers = vec![1, 2, 3, 4, 5];
//! let doubled: Vec<i32> = numbers.fmap(|x| x * 2);
//! assert_eq!(doubled, vec![2, 4, 6, 8, 10]);
//!
//! // Works with optional values
//! let opt_num = Some(42);
//! let opt_string = opt_num.fmap(|x| x.to_string());
//! assert_eq!(opt_string, Some("42".to_string()));
//!
//! // Preserves structure - None stays None
//! let nothing: Option<i32> = None;
//! let still_nothing = nothing.fmap(|x| x.to_string());
//! assert_eq!(still_nothing, None);
//! ```
//!
//! ## Relationship to other traits
//!
//! Functors are the foundation of many higher-level abstractions in functional programming:
//!
//! ``` Text
//! Functor -> Applicative -> Monad
//! ```
//!
//! Each level adds more capabilities:
//! - Functors: Transforming values in a context (`fmap`)
//! - Applicatives: Applying functions in a context to values in a context (`apply`)
//! - Monads: Sequencing operations that return values in a context (`bind`)
//!
//! ## Components
//!
//! The module contains:
//!
//! - The core `Functor` trait that defines mapping operations
//! - Extension methods in `FunctorExt` for additional utility
//! - Implementations for standard Rust types like `Option`, `Result`, and `Vec`
//!
//! ## Functor Laws
//!
//! Implementations preserve identity and composition. Exhaustive law checks live in
//! `tests/traits/algebraic_laws.rs`; the quick-start example above shows normal usage.

use crate::prelude::*;

/// A trait for functors, which are type constructors that support mapping over values.
///
/// In category theory, a functor is a mapping between categories that preserves
/// structure. In Rust terms, it's a type constructor that provides a way to apply
/// a function to values while preserving their structure.
///
/// # Functor Laws
///
/// Any implementation of `Functor` should satisfy these laws:
///
/// 1. Identity: `functor.fmap(|x| x) == functor`
///    Mapping the identity function over a functor should return an equivalent functor.
///
/// 2. Composition: `functor.fmap(|x| g(f(x))) == functor.fmap(f).fmap(g)`
///    Mapping a composition of functions should be the same as mapping each function in sequence.
///
/// # Examples
///
/// ```rust
/// use rustica::traits::functor::Functor;
///
/// // Using the Functor implementation for Option
/// let opt_int = Some(42);
///
/// // Transform i32 to String
/// let opt_string = opt_int.fmap(|x: i32| x.to_string());
/// assert_eq!(opt_string, Some("42".to_string()));
///
/// // Using replace to substitute values
/// let replaced = Some(42).replace(String::from("hello"));
/// assert_eq!(replaced.unwrap(), "hello");
///
/// // Using void to discard values
/// let voided = Some(42).void();
/// assert!(matches!(voided, Some(())));
///
/// // With empty values
/// let opt_none: Option<i32> = None;
/// let mapped_none = opt_none.fmap(|x: i32| x.to_string());
/// assert_eq!(mapped_none, None);
/// ```
pub trait Functor: HKT {
    /// Maps a function over the values in a functor, consuming it.
    ///
    /// # Arguments
    ///
    /// * `f` - A function that transforms values of type `Self::Source` into type `B`
    ///
    /// # Returns
    ///
    /// A new functor containing the transformed value.
    fn fmap<B, F>(self, f: F) -> Self::Output<B>
    where
        F: FnMut(Self::Source) -> B;

    /// Replaces all values in the functor with a constant value, consuming the functor.
    ///
    /// # Arguments
    ///
    /// * `value` - The value to replace all elements with
    ///
    /// # Returns
    ///
    /// A new functor with all elements replaced by the given value
    #[inline]
    fn replace<B>(self, value: B) -> Self::Output<B>
    where
        B: Clone,
        Self: Sized,
    {
        self.fmap(move |_| value.clone())
    }

    /// Void functor - discards the values and replaces them with unit, consuming the functor.
    ///
    /// # Returns
    ///
    /// A new functor with all elements replaced by ()
    #[inline]
    fn void(self) -> Self::Output<()>
    where
        Self: Sized,
    {
        self.fmap(|_| ())
    }
}

/// Extension trait for functors providing additional utility methods.
pub trait FunctorExt: Functor {}

impl<T: Functor> FunctorExt for T {}

impl<T> Functor for Vec<T> {
    #[inline]
    fn fmap<B, F>(self, f: F) -> Self::Output<B>
    where
        F: FnMut(Self::Source) -> B,
    {
        self.into_iter().map(f).collect()
    }
}

impl<T> Functor for Option<T> {
    #[inline]
    fn fmap<B, F>(self, f: F) -> Self::Output<B>
    where
        F: FnMut(Self::Source) -> B,
    {
        self.map(f)
    }
}

impl<A, E: Clone> Functor for Result<A, E> {
    #[inline]
    fn fmap<B, F>(self, f: F) -> Self::Output<B>
    where
        F: FnMut(Self::Source) -> B,
    {
        self.map(f)
    }
}

#[cfg(test)]
mod standard_law_tests {
    use super::Functor;
    use quickcheck_macros::quickcheck;

    #[quickcheck]
    fn option_functor_laws(m: Option<i32>) -> bool {
        let f = |x: i32| x.saturating_mul(2);
        let g = |x: i32| x.saturating_add(1);
        m.fmap(|x| x) == m
            && m.fmap(|x| g(f(x))) == m.fmap(f).fmap(g)
            && m.fmap(f).is_some() == m.is_some()
    }

    #[quickcheck]
    fn result_functor_laws(m: Result<i32, i8>) -> bool {
        let f = |x: i32| x.saturating_add(10);
        let g = |x: i32| x.saturating_mul(3);
        m.fmap(|x| x) == m
            && m.fmap(|x| g(f(x))) == m.fmap(f).fmap(g)
            && m.fmap(f).is_ok() == m.is_ok()
    }

    #[quickcheck]
    fn vec_functor_laws(v: Vec<i32>) -> bool {
        let mapped = v.clone().fmap(|x| x.saturating_abs());
        v.clone().fmap(|x| x) == v && mapped.len() == v.len()
    }
}
