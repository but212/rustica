use crate::traits::applicative::Applicative;
use crate::traits::hkt::{HKT, TypeOps, AnyBox};
use std::sync::Arc;

/// A trait for monads in category theory.
///
/// Monads are a design pattern that allows for sequential composition of functions
/// that produce values wrapped in a computational context.
///
/// # Laws
///
/// A Monad instance must satisfy these laws:
///
/// 1. Left Identity: For any value `x` and function `f`,
///    `pure(x).bind(f) == f(x)`
/// 2. Right Identity: For any monad `m`,
///    `m.bind(pure) == m`
/// 3. Associativity: For any monad `m` and functions `f`, `g`,
///    `m.bind(f).bind(g) == m.bind(|x| f(x).bind(g))`
/// 4. Naturality: For any natural transformation `η` and monad `m`,
///    `η(m.bind(f)) == η(m).bind(|x| η(f(x)))`
/// 5. Monad-Applicative Consistency:
///    `m.bind(f) == m.fmap(f).join()`
pub trait Monad: Applicative {
    /// Binds a monadic function to this monad.
    ///
    /// This method applies the function `f` to the value inside the monad,
    /// and then flattens the resulting nested monad.
    ///
    /// # Arguments
    ///
    /// * `f` - A function that takes a value and returns a new monad.
    ///
    /// # Returns
    ///
    /// A new monad resulting from applying `f` and then flattening.
    fn bind(&self, f: Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>) -> AnyBox;

    /// Flattens a nested monad structure.
    ///
    /// This method takes a monad of a monad and flattens it into a single-layer monad.
    ///
    /// # Returns
    ///
    /// A flattened monad.
    fn join(&self) -> AnyBox;
}

impl<T> Monad for Vec<T>
where
    T: TypeOps + 'static
{
    fn bind(&self, f: Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>) -> AnyBox {
        let result = self.iter()
            .flat_map(|x| {
                let x_box = x.clone_box();
                if let Some(vec) = self.downcast(&f(x_box)) {
                    if let Some(inner_vec) = vec.downcast_ref::<Vec<AnyBox>>() {
                        inner_vec.clone()
                    } else {
                        Vec::new()
                    }
                } else {
                    Vec::new()
                }
            })
            .collect::<Vec<_>>();
        Arc::new(result)
    }

    fn join(&self) -> AnyBox {
        let result = self.iter()
            .flat_map(|x| {
                let x_box = x.clone_box();
                if let Some(inner) = self.downcast(&x_box) {
                    if let Some(vec) = inner.downcast_ref::<Vec<AnyBox>>() {
                        vec.clone()
                    } else {
                        Vec::new()
                    }
                } else {
                    Vec::new()
                }
            })
            .collect::<Vec<_>>();
        Arc::new(result)
    }
}

impl<T> Monad for Option<T>
where
    T: TypeOps + 'static
{
    fn bind(&self, f: Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>) -> AnyBox {
        match self {
            Some(x) => {
                let x_box = x.clone_box();
                if let Some(result) = self.downcast(&f(x_box)) {
                    if let Some(opt) = result.downcast_ref::<Option<AnyBox>>() {
                        Arc::new(opt.clone())
                    } else {
                        Arc::new(None::<AnyBox>)
                    }
                } else {
                    Arc::new(None::<AnyBox>)
                }
            }
            None => Arc::new(None::<AnyBox>)
        }
    }

    fn join(&self) -> AnyBox {
        match self {
            Some(x) => {
                let x_box = x.clone_box();
                if let Some(inner) = self.downcast(&x_box) {
                    if let Some(opt) = inner.downcast_ref::<Option<AnyBox>>() {
                        Arc::new(opt.clone())
                    } else {
                        Arc::new(None::<AnyBox>)
                    }
                } else {
                    Arc::new(None::<AnyBox>)
                }
            }
            None => Arc::new(None::<AnyBox>)
        }
    }
}

impl<T, E> Monad for Result<T, E>
where
    T: TypeOps + Clone + 'static,
    E: TypeOps + Clone + 'static
{
    fn bind(&self, f: Arc<dyn Fn(AnyBox) -> AnyBox + Send + Sync>) -> AnyBox {
        match self {
            Ok(x) => {
                let x_box = x.clone_box();
                if let Some(result) = self.downcast(&f(x_box)) {
                    if let Some(res) = result.downcast_ref::<Result<AnyBox, AnyBox>>() {
                        Arc::new(res.clone())
                    } else {
                        Arc::new(Err::<AnyBox, AnyBox>(Arc::new(())))
                    }
                } else {
                    Arc::new(Err::<AnyBox, AnyBox>(Arc::new(())))
                }
            }
            Err(e) => Arc::new(Err::<AnyBox, AnyBox>(e.clone_box()))
        }
    }

    fn join(&self) -> AnyBox {
        match self {
            Ok(x) => {
                let x_box = x.clone_box();
                if let Some(inner) = self.downcast(&x_box) {
                    if let Some(res) = inner.downcast_ref::<Result<AnyBox, AnyBox>>() {
                        Arc::new(res.clone())
                    } else {
                        Arc::new(Err::<AnyBox, AnyBox>(Arc::new(())))
                    }
                } else {
                    Arc::new(Err::<AnyBox, AnyBox>(Arc::new(())))
                }
            }
            Err(e) => Arc::new(Err::<AnyBox, AnyBox>(e.clone_box()))
        }
    }
}