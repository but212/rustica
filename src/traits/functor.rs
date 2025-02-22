use crate::traits::identity::Identity;
use crate::traits::hkt::{AnyBox, TypeOps};

use std::collections::HashMap;
use std::hash::Hash;
use std::fmt::Debug;
use std::sync::Arc;

/// A trait representing functors in category theory.
///
/// Functors are structures that can be mapped over, preserving the structure
/// of the functor while transforming its contents.
///
/// # Laws
///
/// A Functor instance must satisfy these laws:
///
/// 1. Identity: For any functor `f`,
///    `f.fmap(|x| x) == f`
/// 2. Composition: For any functor `f` and functions `g`, `h`,
///    `f.fmap(|x| g(h(x))) == f.fmap(h).fmap(g)`
pub trait Functor: Identity {
    /// Maps a function over the contents of the functor.
    ///
    /// # Arguments
    ///
    /// * `f` - The function to apply to the functor's contents.
    ///
    /// # Returns
    ///
    /// A new functor instance containing the results of applying `f`.
    fn fmap(&self, f: Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>) -> AnyBox;
}

impl<T> Functor for Vec<T>
where
    T: TypeOps + 'static
{
    fn fmap(&self, f: Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>) -> AnyBox {
        let result = self.iter()
            .map(|x| f(x.clone_box()))
            .collect::<Vec<_>>();
        Arc::new(result)
    }
}

impl<T> Functor for Option<T>
where
    T: TypeOps + 'static
{
    fn fmap(&self, f: Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>) -> AnyBox {
        match self {
            Some(x) => Arc::new(Some(f(x.clone_box()))),
            None => Arc::new(None::<AnyBox>),
        }
    }
}

impl<K, V> Functor for HashMap<K, V>
where
    K: Clone + Hash + Eq + Debug + Send + Sync + 'static,
    V: TypeOps + Clone + 'static
{
    fn fmap(&self, f: Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>) -> AnyBox {
        let mut result = HashMap::new();
        for (k, v) in self.iter() {
            result.insert(k.clone(), f(v.clone_box()));
        }
        Arc::new(result)
    }
}

impl<K, V> Functor for Result<K, V>
where
    K: TypeOps + 'static,
    V: TypeOps + 'static
{
    fn fmap(&self, f: Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>) -> AnyBox {
        match self {
            Ok(x) => Arc::new(Ok::<AnyBox, AnyBox>(f(x.clone_box()))),
            Err(e) => Arc::new(Err::<AnyBox, AnyBox>(e.clone_box())),
        }
    }
}