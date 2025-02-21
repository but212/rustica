use crate::traits::hkt::{HKT, TypeConstraints};
use crate::fntype::{FnTrait, FnType};
use std::hash::Hash;
use std::collections::HashMap;
use std::fmt::Debug;

/// A trait for types that can be composed with functions.
///
/// This trait defines operations for composing types with functions, allowing for
/// functional composition and transformation of values within a context.
///
/// # Type Parameters
/// * `T`: The type to be composed, must satisfy `TypeConstraints`.
///
/// # Laws
/// 
/// A Composable instance must satisfy these laws:
/// 
/// 1. Associativity: For any composable `x` and functions `f`, `g`, `h`,
///    `x.compose_with(f).compose_with(g).compose_with(h) = x.compose_with(|a| f.call(a).compose_with(g).compose_with(h))`
/// 2. Identity: For any composable `x`,
///    `x.compose_with(|a| a) = x`
/// 3. Distributivity: For any composable `x` and functions `f`, `g`,
///    `x.compose_with(|a| f.call(a)).compose_with(g) = x.compose_with(|a| g.call(f.call(a)))`
/// 4. Naturality: For any natural transformation `η: F ~> G`,
///    `η(x.compose_with(f)) = η(x).compose_with(|a| η(f.call(a)))`
/// 5. Functor Consistency: For any value `x` and function `f`,
///    `pure(x).compose_with(f) = pure(f.call(x))`
pub trait Composable<T: TypeConstraints>: HKT {
    /// Composes two functions, applying the second function to the result of the first.
    ///
    /// This method creates a new function that is the composition of `f` and `g`,
    /// where the output of `f` is passed as input to `g`.
    ///
    /// # Type Parameters
    /// * `U`: Intermediate type, must satisfy `TypeConstraints`.
    /// * `V`: Result type, must satisfy `TypeConstraints`.
    /// * `F`: First function type, must implement `FnTrait<T, U>`.
    /// * `G`: Second function type, must implement `FnTrait<U, V>`.
    ///
    /// # Returns
    /// A new function of type `impl FnTrait<T, V>` that represents the composition of `f` and `g`.
    fn compose<U, V, F, G>(f: F, g: G) -> impl FnTrait<T, V>
    where
        U: TypeConstraints,
        V: TypeConstraints,
        F: FnTrait<T, U>,
        G: FnTrait<U, V>,
    {
        FnType::new(move |x| g.call(f.call(x)))
    }

    /// Composes a function with this type's operation.
    ///
    /// This method allows for the composition of the current type with a given function,
    /// transforming the value within the context of the composable type.
    ///
    /// # Type Parameters
    /// * `U`: Result type, must satisfy `TypeConstraints`.
    /// * `F`: Function type, must implement `FnTrait<T, U>`.
    ///
    /// # Returns
    /// The result of composing `self` with the given function `f`, wrapped in the `Output` type.
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

impl<K: Hash + Eq + Debug + TypeConstraints, V: TypeConstraints> Composable<V> for HashMap<K, V> {
    fn compose_with<U, F>(self, f: F) -> HashMap<K, U>
    where
        U: TypeConstraints,
        F: FnTrait<V, U>,
    {
        self.into_iter().map(|(k, v)| (k, f.call(v))).collect()
    }
}
