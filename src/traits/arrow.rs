use crate::traits::composable::Composable;
use crate::traits::hkt::{TypeOps, AnyBox};
use std::sync::Arc;

/// Arrow type class.
///
/// # Laws
///
/// An Arrow instance must satisfy these laws:
///
/// 1. Identity: For any arrow `a`,
///    `a.arrow(identity) = identity`
/// 2. Composition: For any arrow `a` and functions `f`, `g`,
///    `a.arrow(f >>> g) = a.arrow(f) >>> a.arrow(g)`
/// 3. First: For any arrow `a` and function `f`,
///    `a.first(a.arrow(f)) = a.arrow(first(f))`
/// 4. First Composition: For any arrow `a` and functions `f`, `g`,
///    `a.first(f >>> g) = a.first(f) >>> a.first(g)`
/// 5. Split: For any arrow `a` and functions `f`, `g`,
///    `a.split(f, g) = a.first(f) >>> a.second(g)`
pub trait Arrow: Composable {
    /// Creates an arrow from a function.
    ///
    /// # Arguments
    ///
    /// * `f` - Function to lift into an arrow
    ///
    /// # Returns
    ///
    /// A new arrow containing the function
    fn arrow(&self, f: AnyBox) -> AnyBox;

    /// Applies the first component of a pair.
    ///
    /// # Arguments
    ///
    /// * `f` - Function to apply to first component
    ///
    /// # Returns
    ///
    /// A new arrow that applies f to the first component
    fn first(&self, f: AnyBox) -> AnyBox;

    /// Applies the second component of a pair.
    ///
    /// # Arguments
    ///
    /// * `f` - Function to apply to second component
    ///
    /// # Returns
    ///
    /// A new arrow that applies f to the second component
    fn second(&self, f: AnyBox) -> AnyBox;

    /// Splits an arrow into two parallel arrows.
    ///
    /// # Arguments
    ///
    /// * `f` - First arrow
    /// * `g` - Second arrow
    ///
    /// # Returns
    ///
    /// A new arrow that applies both f and g in parallel
    fn split(&self, f: AnyBox, g: AnyBox) -> AnyBox;
}

impl<T: TypeOps + 'static> Arrow for Vec<T> {
    fn arrow(&self, f: AnyBox) -> AnyBox {
        Arc::clone(&f)
    }

    fn first(&self, f: AnyBox) -> AnyBox {
        Arc::new(Box::new(move |pair: AnyBox| {
            if let Some(pair) = pair.downcast_ref::<(AnyBox, AnyBox)>() {
                Arc::new((f.clone(), pair.1.clone()))
            } else {
                pair
            }
        }) as Box<dyn Fn(AnyBox) -> AnyBox + Send + Sync>)
    }

    fn second(&self, f: AnyBox) -> AnyBox {
        Arc::new(Box::new(move |pair: AnyBox| {
            if let Some(pair) = pair.downcast_ref::<(AnyBox, AnyBox)>() {
                Arc::new((pair.0.clone(), f.clone()))
            } else {
                pair
            }
        }) as Box<dyn Fn(AnyBox) -> AnyBox + Send + Sync>)
    }

    fn split(&self, f: AnyBox, g: AnyBox) -> AnyBox {
        Arc::new(Box::new(move |pair: AnyBox| {
            if let Some(_) = pair.downcast_ref::<(AnyBox, AnyBox)>() {
                Arc::new((f.clone(), g.clone()))
            } else {
                pair
            }
        }) as Box<dyn Fn(AnyBox) -> AnyBox + Send + Sync>)
    }
}

impl<T: TypeOps + 'static> Arrow for Option<T> {
    fn arrow(&self, f: AnyBox) -> AnyBox {
        Arc::clone(&f)
    }

    fn first(&self, f: AnyBox) -> AnyBox {
        Arc::new(Box::new(move |pair: AnyBox| {
            if let Some(pair) = pair.downcast_ref::<(AnyBox, AnyBox)>() {
                Arc::new((f.clone(), pair.1.clone()))
            } else {
                pair
            }
        }) as Box<dyn Fn(AnyBox) -> AnyBox + Send + Sync>)
    }

    fn second(&self, f: AnyBox) -> AnyBox {
        Arc::new(Box::new(move |pair: AnyBox| {
            if let Some(pair) = pair.downcast_ref::<(AnyBox, AnyBox)>() {
                Arc::new((pair.0.clone(), f.clone()))
            } else {
                pair
            }
        }) as Box<dyn Fn(AnyBox) -> AnyBox + Send + Sync>)
    }

    fn split(&self, f: AnyBox, g: AnyBox) -> AnyBox {
        Arc::new(Box::new(move |pair: AnyBox| {
            if let Some(_) = pair.downcast_ref::<(AnyBox, AnyBox)>() {
                Arc::new((f.clone(), g.clone()))
            } else {
                pair
            }
        }) as Box<dyn Fn(AnyBox) -> AnyBox + Send + Sync>)
    }
}

impl<K: TypeOps + Clone + 'static, V: TypeOps + Clone + 'static> Arrow for Result<K, V> {
    fn arrow(&self, f: AnyBox) -> AnyBox {
        Arc::clone(&f)
    }

    fn first(&self, f: AnyBox) -> AnyBox {
        Arc::new(Box::new(move |pair: AnyBox| {
            if let Some(pair) = pair.downcast_ref::<(AnyBox, AnyBox)>() {
                Arc::new((f.clone(), pair.1.clone()))
            } else {
                pair
            }
        }) as Box<dyn Fn(AnyBox) -> AnyBox + Send + Sync>)
    }

    fn second(&self, f: AnyBox) -> AnyBox {
        Arc::new(Box::new(move |pair: AnyBox| {
            if let Some(pair) = pair.downcast_ref::<(AnyBox, AnyBox)>() {
                Arc::new((pair.0.clone(), f.clone()))
            } else {
                pair
            }
        }) as Box<dyn Fn(AnyBox) -> AnyBox + Send + Sync>)
    }

    fn split(&self, f: AnyBox, g: AnyBox) -> AnyBox {
        Arc::new(Box::new(move |pair: AnyBox| {
            if let Some(_) = pair.downcast_ref::<(AnyBox, AnyBox)>() {
                Arc::new((f.clone(), g.clone()))
            } else {
                pair
            }
        }) as Box<dyn Fn(AnyBox) -> AnyBox + Send + Sync>)
    }
}