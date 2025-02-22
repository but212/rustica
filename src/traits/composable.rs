use crate::traits::hkt::{TypeOps, AnyBox, HKT};
use std::collections::HashMap;
use std::hash::Hash;
use std::sync::Arc;

/// A trait for types that support function composition
///
/// # Laws
///
/// 1. Associativity: For any composable functions f, g, h:
///    `compose_with(x, compose(f, g)) = compose_with(compose_with(x, f), g)`
/// 2. Identity: For any composable function f and value x:
///    `compose_with(x, id) = x`
pub trait Composable: HKT {
    /// Composes this value with a function
    ///
    /// # Arguments
    ///
    /// * `f` - The function to compose with
    ///
    /// # Returns
    ///
    /// A new composed value
    fn compose_with(&self, f: Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>) -> AnyBox;

    /// Composes two functions
    ///
    /// This is a fundamental operation in category theory that composes
    /// two morphisms (functions) to create a new morphism.
    ///
    /// # Arguments
    ///
    /// * `f` - First function (will be applied first)
    /// * `g` - Second function (will be applied after f)
    ///
    /// # Returns
    ///
    /// A new function that is the composition of f and g (g ∘ f)
    fn compose(&self, f: Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>, g: Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>) -> Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>;
}

impl<T> Composable for Vec<T>
where
    T: TypeOps + 'static
{
    fn compose_with(&self, f: Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>) -> AnyBox {
        let mut result = Vec::new();
        for x in self {
            let input = x.clone_box();
            let output = f(input);
            result.push(output);
        }
        Arc::new(result)
    }

    fn compose(&self, f: Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>, g: Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>) -> Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync> {
        Arc::new(move |x| {
            let f = Arc::clone(&f);
            let g = Arc::clone(&g);
            g(f(x))
        })
    }
}

impl<T> Composable for Option<T>
where
    T: TypeOps + 'static
{
    fn compose_with(&self, f: Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>) -> AnyBox {
        match self {
            Some(x) => {
                let input = x.clone_box();
                Arc::new(Some(f(input)))
            }
            None => Arc::new(None::<AnyBox>),
        }
    }

    fn compose(&self, f: Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>, g: Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>) -> Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync> {
        Arc::new(move |x| {
            let f = Arc::clone(&f);
            let g = Arc::clone(&g);
            g(f(x))
        })
    }
}

impl<T, E> Composable for Result<T, E>
where
    T: TypeOps + 'static,
    E: TypeOps + Clone + 'static,
{
    fn compose_with(&self, f: Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>) -> AnyBox {
        match self {
            Ok(x) => {
                let input = x.clone_box();
                let result: Result<AnyBox, E> = Ok(f(input));
                Arc::new(result)
            }
            Err(e) => {
                let error = e.clone();
                let result: Result<AnyBox, E> = Err(error);
                Arc::new(result)
            }
        }
    }

    fn compose(&self, f: Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>, g: Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>) -> Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync> {
        Arc::new(move |x| {
            let f = Arc::clone(&f);
            let g = Arc::clone(&g);
            g(f(x))
        })
    }
}

impl<K, V> Composable for HashMap<K, V>
where
    K: Clone + Hash + Eq + Send + Sync + 'static,
    V: TypeOps + 'static,
{
    fn compose_with(&self, f: Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>) -> AnyBox {
        let mut result = HashMap::new();
        for (k, v) in self {
            let input = v.clone_box();
            let output = f(input);
            result.insert(k.clone(), output);
        }
        Arc::new(result)
    }

    fn compose(&self, f: Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>, g: Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>) -> Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync> {
        Arc::new(move |x| {
            let f = Arc::clone(&f);
            let g = Arc::clone(&g);
            g(f(x))
        })
    }
}

/// Helper module containing common composition utilities
pub mod compose {
    use super::*;

    /// Creates a composed function from two functions
    pub fn compose_fn(f: Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>, g: Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>) -> Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync> {
        Arc::new(move |x| {
            let f = Arc::clone(&f);
            let g = Arc::clone(&g);
            g(f(x))
        })
    }
}
