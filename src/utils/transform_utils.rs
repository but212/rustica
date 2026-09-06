//! # Transformation Utilities
//!
//! Utilities for data transformation and operation chaining.

use crate::traits::functor::Functor;

/// Applies a transformation to a single optional value.
#[deprecated(
    since = "0.15.0",
    note = "use `Option::map` together with `Functor::fmap` instead"
)]
#[inline]
pub fn transform_chain<T, F, U>(value: Option<T>, f: F) -> Option<T::Output<U>>
where
    T: Functor,
    F: Fn(&T::Source) -> U,
{
    value.map(|v| v.fmap(|x| f(&x)))
}
