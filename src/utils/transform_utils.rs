//! # Transformation Utilities
//!
//! Utilities for data transformation and operation chaining.

use crate::traits::functor::Functor;

/// Applies a transformation to a single optional value.
#[inline]
pub fn transform_chain<T, F, U>(value: Option<T>, f: F) -> Option<T::Output<U>>
where
    T: Functor,
    F: Fn(&T::Source) -> U,
    U: Clone,
{
    value.map(|v| v.fmap(f))
}
