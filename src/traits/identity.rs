use crate::traits::hkt::{TypeOps, AnyBox, HKT};

use std::collections::HashMap;
use std::hash::Hash;
use std::fmt::Debug;
use std::sync::Arc;

/// Identity trait for types that can be mapped over
///
/// This trait defines the concept of an identity element and a mapping operation
/// for types that implement it. It extends the Higher Kinded Type (HKT) trait.
///
/// # Laws
///
/// An Identity instance must satisfy these laws:
///
/// 1. Left Identity: For any value `x` and function `f`,
///    `identity().map_identity(f) = f(x)`
/// 2. Right Identity: For any value `x`,
///    `x.map_identity(identity) = x`
/// 3. Associativity: For any value `x` and functions `f`, `g`,
///    `x.map_identity(f).map_identity(g) = x.map_identity(|y| g(f(y)))`
/// 4. Naturality: For any natural transformation `η` and function `f`,
///    `η(map_identity(f)) = map_identity(η.compose(f))`
/// 5. Functor Consistency: For any value `x` and function `f`,
///    `pure(x).fmap(f) = pure(f(x))`
pub trait Identity: HKT {
    /// Returns the identity element for this type.
    ///
    /// The identity element is a value that, when combined with any other value
    /// of the same type using the `map_identity` operation, leaves the other value unchanged.
    ///
    /// # Returns
    ///
    /// An `AnyBox` representing the identity element.
    fn identity() -> AnyBox;

    /// Maps a function over the identity element.
    ///
    /// This method applies the given function to the identity element of the type.
    /// It's a key operation that allows for the transformation of the identity element
    /// while preserving the identity laws.
    ///
    /// # Arguments
    ///
    /// * `f` - A function wrapped in an `Arc` that takes an `AnyBox` and returns an `AnyBox`.
    ///         This function should be both `Send` and `Sync` to ensure thread safety.
    ///
    /// # Returns
    ///
    /// An `AnyBox` representing the result of applying the function to the identity element.
    fn map_identity(f: Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>) -> AnyBox;
}

impl<T> Identity for Vec<T> 
where
    T: TypeOps + 'static
{
    fn identity() -> AnyBox {
        Arc::new(Vec::<AnyBox>::new())
    }

    fn map_identity(f: Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>) -> AnyBox {
        f(Arc::new(Vec::<AnyBox>::new()) as AnyBox)
    }
}

impl<K, V> Identity for Result<K, V>
where
    K: TypeOps + 'static,
    V: TypeOps + 'static
{
    fn identity() -> AnyBox {
        Arc::new(Ok::<AnyBox, AnyBox>(Arc::new(()) as AnyBox)) as AnyBox
    }

    fn map_identity(f: Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>) -> AnyBox {
        f(Arc::new(Ok::<AnyBox, AnyBox>(Arc::new(()) as AnyBox)) as AnyBox)
    }
}

impl<T> Identity for Option<T>
where
    T: TypeOps + 'static
{
    fn identity() -> AnyBox {
        Arc::new(None::<AnyBox>) as AnyBox
    }

    fn map_identity(f: Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>) -> AnyBox {
        f(Arc::new(None::<AnyBox>) as AnyBox)
    }
}

impl<K, V> Identity for HashMap<K, V>
where
    K: Clone + Hash + Eq + Debug + Send + Sync + 'static,
    V: TypeOps + Clone + 'static
{
    fn identity() -> AnyBox {
        Arc::new(HashMap::<K, AnyBox>::new()) as AnyBox
    }

    fn map_identity(f: Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>) -> AnyBox {
        f(Arc::new(HashMap::<K, AnyBox>::new()) as AnyBox)
    }
}