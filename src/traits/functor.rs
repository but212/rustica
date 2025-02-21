use crate::traits::identity::Identity;
use crate::traits::hkt::TypeConstraints;
use crate::fntype::{FnTrait, FnType};
use crate::traits::composable::Composable;

use std::collections::HashMap;
use std::hash::Hash;
use std::fmt::Debug;

/// A trait for functors, which are type constructors that can map functions over their contents.
///
/// # Type Parameters
/// * `T` - The type of value contained in the functor
///
/// # Laws
/// 1. Identity: `fmap(id) = id`
/// 2. Composition: `fmap(f ∘ g) = fmap(f) ∘ fmap(g)`
/// 3. Structure Preservation: `fmap` must preserve the structure of the functor
/// 4. Type Safety: `fmap` must maintain the same type constructor
pub trait Functor<T>: Identity<T> + Composable<T>
where
    T: TypeConstraints,
{
    fn fmap<U, F>(self, f: F) -> Self::Output<U>
    where
        U: TypeConstraints,
        F: FnTrait<T, U>,
    {
        self.compose_with(f)
    }

    fn lift<U, F>(f: F) -> FnType<Self, Self::Output<U>>
    where
        U: TypeConstraints,
        F: FnTrait<T, U>,
    {
        FnType::new(move |x: Self| x.fmap(f.clone()))
    }
}

impl<T> Functor<T> for Vec<T>
where
    T: TypeConstraints,
{
    fn fmap<U, F>(self, f: F) -> Self::Output<U>
    where
        U: TypeConstraints,
        F: FnTrait<T, U>,
    {
        self.into_iter().map(|x| f.call(x)).collect()
    }
}

impl<T: TypeConstraints> Functor<T> for Box<T> {
    fn fmap<U, F>(self, f: F) -> Self::Output<U>
    where
        U: TypeConstraints,
        F: FnTrait<T, U>,
    {
        Box::new(f.call(*self))
    }
}

impl<K, V> Functor<V> for HashMap<K, V>
where
    K: Hash + Eq + Debug + TypeConstraints + 'static,
    V: TypeConstraints,
{
    fn fmap<U, F>(self, f: F) -> Self::Output<U>
    where
        U: TypeConstraints,
        F: FnTrait<V, U>,
    {
        self.into_iter()
            .map(|(k, v)| (k, f.call(v)))
            .collect()
    }
}