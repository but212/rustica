use crate::traits::hkt::{HKT, TypeConstraints};
use crate::traits::composable::Composable;
use crate::fntype::FnTrait;
use std::collections::HashMap;
use std::hash::Hash;
use std::fmt::Debug;

/// A trait representing the identity operation in category theory.
///
/// This trait defines methods for creating an identity element and mapping over it.
/// It is parameterized over a type `T` that satisfies the `TypeConstraints`.
///
/// # Type Parameters
/// * `T`: The type contained within the identity, must satisfy `TypeConstraints`.
///
/// # Associated Types
/// * `Output`: Defined by the `HKT` supertrait.
///
/// # Laws
/// 
/// An Identity instance must satisfy these laws:
/// 
/// 1. Left identity: For any function `f`,
///    `map_identity(f).compose(identity()) = f`
/// 2. Right identity: For any value `x`,
///    `map_identity(identity()).apply(x) = x`
/// 3. Composition: For any functions `f` and `g`,
///    `map_identity(f.compose(g)) = map_identity(f).compose(map_identity(g))`
/// 4. Naturality: For any natural transformation `η`,
///    `η(map_identity(f)) = map_identity(η.compose(f))`
/// 5. Functor Consistency: For any value `x` and function `f`,
///    `pure(x).fmap(f) = pure(f(x))`
pub trait Identity<T: TypeConstraints>: HKT + Composable<T> {
    /// Returns the identity element for this type.
    ///
    /// By default, this method returns the default value of `Self::Output<T>`.
    ///
    /// # Returns
    /// An instance of `Self::Output<T>` representing the identity element.
    fn identity() -> Self::Output<T> {
        Self::Output::default()
    }

    /// Maps a function over the identity element.
    ///
    /// # Type Parameters
    /// * `U`: The target type of the mapping, must satisfy `TypeConstraints`.
    /// * `F`: The function type, must implement `FnTrait<T, U>`.
    ///
    /// # Parameters
    /// * `f`: The function to map over the identity element.
    ///
    /// # Returns
    /// An instance of `Self::Output<U>` representing the mapped identity.
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

impl<K: Hash + Eq + Debug + TypeConstraints, V: TypeConstraints> Identity<V> for HashMap<K, V> {
    fn map_identity<U, F>(_f: F) -> Self::Output<U>
    where
        U: TypeConstraints,
        F: FnTrait<V, U>,
    {
        HashMap::new()
    }
}