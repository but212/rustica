use crate::traits::hkt::{HKT, TypeConstraints};
use crate::fntype::{FnTrait, FnType};
use std::hash::Hash;
use std::collections::HashMap;

/// A trait for types that support function composition.
///
/// This trait represents the composition operation in category theory,
/// allowing functions to be combined in a type-safe way.
///
/// Laws:
/// 1. Associativity: `f.compose(g).compose(h) = f.compose(g.compose(h))`
/// 2. Type Safety: If `f: A -> B` and `g: B -> C`, then `f.compose(g): A -> C`
pub trait Composable<T: TypeConstraints>: HKT {
    /// Composes two functions, applying the second function to the result of the first.
    fn compose<U, V, F, G>(f: F, g: G) -> impl FnTrait<T, V>
    where
        U: TypeConstraints,
        V: TypeConstraints,
        F: FnTrait<T, U>,
        G: FnTrait<U, V>,
    {
        FnType::new(move |x| g.call(f.call(x)))
    }

    /// Composes a function with this type's operation
    fn compose_with<U, F>(self, f: F) -> Self::Output<U>
    where
        U: TypeConstraints,
        F: FnTrait<T, U>;
}

impl<T: TypeConstraints> Composable<T> for Vec<T> {
    fn compose_with<U, F>(self, f: F) -> Vec<U>
    where
        U: TypeConstraints,
        F: FnTrait<T, U>,
    {
        self.into_iter().map(|x| f.call(x)).collect()
    }
}

impl<T: TypeConstraints> Composable<T> for Box<T> {
    fn compose_with<U, F>(self, f: F) -> Box<U>
    where
        U: TypeConstraints,
        F: FnTrait<T, U>,
    {
        Box::new(f.call(*self))
    }
}

impl<K: Hash + Eq + TypeConstraints, V: TypeConstraints> Composable<V> for HashMap<K, V> {
    fn compose_with<U, F>(self, f: F) -> HashMap<K, U>
    where
        U: TypeConstraints,
        F: FnTrait<V, U>,
    {
        self.into_iter().map(|(k, v)| (k, f.call(v))).collect()
    }
}
