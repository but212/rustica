use crate::traits::hkt::{HKT, TypeConstraints};
use crate::fntype::FnTrait;
use std::collections::HashMap;
use std::hash::Hash;

/// A trait for types that have an identity element.
///
/// The identity element is a value that, when combined with any other value,
/// returns that other value unchanged.
///
/// # Type Parameters
/// * `T` - The type of the value contained in the identity element
///
/// # Laws
/// 1. Right Identity: `x.combine(identity()) = x`
/// 2. Left Identity: `identity().combine(x) = x`
pub trait Identity<T: TypeConstraints>: HKT {
    /// Returns the identity element for this type
    fn identity() -> Self::Output<T>;

    /// Maps a function over the identity element
    fn map_identity<U, F>(f: F) -> Self::Output<U>
    where
        U: TypeConstraints,
        F: FnTrait<T, U>;
}

impl<T: TypeConstraints> Identity<T> for Vec<T> {
    fn identity() -> Self::Output<T> {
        Vec::new()
    }

    fn map_identity<U, F>(_f: F) -> Self::Output<U>
    where
        U: TypeConstraints,
        F: FnTrait<T, U>,
    {
        Vec::new()
    }
}

impl<T: TypeConstraints> Identity<T> for Box<T> {
    fn identity() -> Self::Output<T> {
        Box::new(T::default())
    }

    fn map_identity<U, F>(f: F) -> Self::Output<U>
    where
        U: TypeConstraints,
        F: FnTrait<T, U>,
    {
        Box::new(f.call(T::default()))
    }
}

impl<K: Hash + Eq + TypeConstraints, V: TypeConstraints> Identity<V> for HashMap<K, V> {
    fn identity() -> Self::Output<V> {
        HashMap::new()
    }

    fn map_identity<U, F>(_f: F) -> Self::Output<U>
    where
        U: TypeConstraints,
        F: FnTrait<V, U>,
    {
        HashMap::new()
    }
}