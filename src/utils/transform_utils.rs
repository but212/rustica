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

// ===== Pipeline Builder =====

/// A wrapper providing fluent chaining for functorial values.
#[deprecated(
    since = "0.13.0",
    note = "Pipeline is an unnecessary wrapper. Use native method chaining directly. Will be removed in 0.14.0."
)]
#[repr(transparent)]
#[derive(Clone)]
pub struct Pipeline<T>(T);

#[allow(deprecated)]
impl<T> Pipeline<T> {
    pub fn new(value: T) -> Self {
        Pipeline(value)
    }

    pub fn extract(self) -> T {
        self.0
    }
}

#[allow(deprecated)]
impl<T: Functor> Pipeline<T> {
    pub fn map_owned<F, U>(self, f: F) -> Pipeline<T::Output<U>>
    where
        F: Fn(T::Source) -> U,
        T::Source: Clone,
        U: Clone,
    {
        Pipeline(self.0.fmap_owned(f))
    }

    pub fn map<F, U>(self, f: F) -> Pipeline<T::Output<U>>
    where
        F: Fn(&T::Source) -> U,
        U: Clone,
    {
        Pipeline(self.0.fmap(f))
    }
}

#[allow(deprecated)]
impl<T> IntoIterator for Pipeline<T>
where
    T: IntoIterator,
{
    type Item = T::Item;
    type IntoIter = T::IntoIter;

    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}
