use std::sync::Arc;
use std::hash::Hash;
use crate::traits::hkt::{TypeOps, AnyBox};

/// A trait for bifunctors, which are functors that can map over two type parameters.
/// 
/// # Laws
/// 
/// A bifunctor must satisfy these laws:
/// 
/// 1. Identity:
///    `bimap(id, id) = id`
/// 
/// 2. Composition:
///    `bimap(f . g, h . i) = bimap(f, h) . bimap(g, i)`
/// 
/// 3. First-Second Equivalence:
///    `bimap(f, g)(b) = first(f)(second(g)(b))`
pub trait Bifunctor: Send + Sync {
    /// Maps a function over the first type parameter of the bifunctor.
    fn map_first(&self, f: Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>) -> AnyBox;

    /// Maps a function over the second type parameter of the bifunctor.
    fn map_second(&self, f: Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>) -> AnyBox;

    /// Maps functions over both type parameters of the bifunctor simultaneously.
    fn bimap(
        &self,
        f: Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>,
        g: Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>
    ) -> AnyBox;
}

impl<A, B> Bifunctor for Result<A, B>
where
    A: TypeOps + 'static,
    B: TypeOps + 'static
{
    fn map_first(&self, f: Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>) -> AnyBox {
        match self {
            Ok(a) => Arc::new(Ok::<AnyBox, AnyBox>(f(a.clone_box()))),
            Err(b) => Arc::new(Err::<AnyBox, AnyBox>(b.clone_box()))
        }
    }

    fn map_second(&self, f: Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>) -> AnyBox {
        match self {
            Ok(a) => Arc::new(Ok::<AnyBox, AnyBox>(a.clone_box())),
            Err(b) => Arc::new(Err::<AnyBox, AnyBox>(f(b.clone_box())))
        }
    }

    fn bimap(
        &self,
        f: Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>,
        g: Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>
    ) -> AnyBox {
        match self {
            Ok(a) => Arc::new(Ok::<AnyBox, AnyBox>(f(a.clone_box()))),
            Err(b) => Arc::new(Err::<AnyBox, AnyBox>(g(b.clone_box())))
        }
    }
}

impl<T> Bifunctor for Vec<T>
where
    T: TypeOps + Clone + 'static
{
    fn map_first(&self, f: Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>) -> AnyBox {
        let mut result = Vec::new();
        for item in self {
            result.push(f(item.clone_box()));
        }
        Arc::new(result)
    }

    fn map_second(&self, f: Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>) -> AnyBox {
        let mut result = Vec::new();
        for item in self {
            result.push(f(item.clone_box()));
        }
        Arc::new(result)
    }

    fn bimap(
        &self,
        f: Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>,
        _g: Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>
    ) -> AnyBox {
        let mut result = Vec::new();
        for item in self {
            result.push(f(item.clone_box()));
        }
        Arc::new(result)
    }
}

impl<T> Bifunctor for Option<T>
where
    T: TypeOps + Clone + 'static
{
    fn map_first(&self, f: Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>) -> AnyBox {
        match self {
            Some(x) => Arc::new(Some(f(x.clone_box()))),
            None => Arc::new(None::<AnyBox>)
        }
    }

    fn map_second(&self, f: Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>) -> AnyBox {
        match self {
            Some(x) => Arc::new(Some(f(x.clone_box()))),
            None => Arc::new(None::<AnyBox>)
        }
    }

    fn bimap(
        &self,
        f: Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>,
        _g: Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>
    ) -> AnyBox {
        match self {
            Some(x) => Arc::new(Some(f(x.clone_box()))),
            None => Arc::new(None::<AnyBox>)
        }
    }
}

impl<K, V> Bifunctor for std::collections::HashMap<K, V>
where
    K: Clone + Hash + Eq + Send + Sync + 'static,
    V: TypeOps + Clone + 'static
{
    fn map_first(&self, f: Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>) -> AnyBox {
        let mut result = std::collections::HashMap::new();
        for (k, v) in self.iter() {
            if let Some(new_k) = f(Arc::new(k.clone())).downcast_ref::<K>() {
                result.insert(new_k.clone(), v.clone());
            }
        }
        Arc::new(result)
    }

    fn map_second(&self, f: Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>) -> AnyBox {
        let mut result = std::collections::HashMap::new();
        for (k, v) in self.iter() {
            result.insert(k.clone(), f(v.clone_box()));
        }
        Arc::new(result)
    }

    fn bimap(
        &self,
        f: Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>,
        g: Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>
    ) -> AnyBox {
        let mut result = std::collections::HashMap::new();
        for (k, v) in self.iter() {
            if let Some(new_k) = f(Arc::new(k.clone())).downcast_ref::<K>() {
                result.insert(new_k.clone(), g(v.clone_box()));
            }
        }
        Arc::new(result)
    }
}