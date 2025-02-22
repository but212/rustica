use crate::traits::hkt::{TypeOps, AnyBox};
use crate::traits::bifunctor::Bifunctor;
use crate::traits::foldable::Foldable;
use std::sync::Arc;

/// A trait for traversable structures that can be traversed with effects.
/// 
/// Traversable provides a way to:
/// 1. Transform elements inside the structure while preserving the structure
/// 2. Accumulate effects in a specific order
/// 3. Combine multiple effectful computations
/// 
/// # Laws
/// 
/// A Traversable instance must satisfy these laws:
/// 
/// 1. Naturality: For any natural transformation `t: F ~> G`,
///    `t(traverse_f(x)) = traverse_g(t ∘ f)(x)`
/// 2. Identity: `traverse_Identity(x) = Identity(x)`
/// 3. Composition: `traverse_Compose(f . g)(x) = Compose(traverse_f(traverse_g(x)))`
/// 4. Fmap Consistency: For any function `f`,
///    `fmap(f)(x) = traverse_Identity(f)(x)`
/// 5. Sequence Consistency: For any traversable `t`,
///    `sequence(t) = traverse_Identity(id)(t)`
/// 6. Fold Consistency: For any monoid `M` and function `f: A -> M`,
///    `fold_map(f)(t) = traverse_Const(f)(t)`
pub trait Traversable: Bifunctor + Foldable {
    /// Traverse this structure with effects.
    /// 
    /// This method allows you to:
    /// 1. Apply a function that produces effects to each element
    /// 2. Collect all effects in a specific order
    /// 3. Preserve the original structure
    /// 
    /// # Arguments
    /// 
    /// * `f` - A function that takes an element and returns an effect
    /// 
    /// # Returns
    /// 
    /// An `AnyBox` containing the traversed structure with effects
    /// 
    /// # Type Parameters
    /// 
    /// * `F` - The type of the function `f`
    /// 
    /// # Safety
    /// 
    /// The function `f` must be thread-safe and 'static
    fn traverse<F>(&self, f: Arc<F>) -> AnyBox 
    where 
        F: Fn(AnyBox) -> AnyBox + Send + Sync + 'static;

    /// Distribute a structure of effects into an effect of structure.
    /// 
    /// # Returns
    /// 
    /// An `AnyBox` containing the distributed structure of effects
    fn distribute(&self) -> AnyBox;
}

impl<T> Traversable for Vec<T>
where
    T: TypeOps + Clone + Send + Sync + 'static
{
    fn traverse<F>(&self, f: Arc<F>) -> AnyBox 
    where 
        F: Fn(AnyBox) -> AnyBox + Send + Sync + 'static
    {
        let mut result = Vec::new();
        for x in self {
            match f(x.clone_box()).downcast_ref::<Vec<AnyBox>>() {
                Some(fx) => result.extend(fx.iter().cloned()),
                None => return Arc::new(None::<Vec<T>>),
            }
        }
        Arc::new(Some(result))
    }

    fn distribute(&self) -> AnyBox {
        let mut result = Vec::new();
        for x in self {
            if let Some(fx) = x.clone_box().downcast_ref::<Vec<AnyBox>>() {
                result.extend(fx.iter().cloned());
            } else {
                return Arc::new(None::<Vec<T>>);
            }
        }
        Arc::new(Some(result))
    }
}

impl<T> Traversable for Option<T>
where
    T: TypeOps + Clone + Send + Sync + 'static
{
    fn traverse<F>(&self, f: Arc<F>) -> AnyBox 
    where 
        F: Fn(AnyBox) -> AnyBox + Send + Sync + 'static
    {
        match self {
            Some(x) => {
                let fx = f(x.clone_box());
                match fx.downcast_ref::<Option<AnyBox>>() {
                    Some(opt) => Arc::new(Some(opt.clone())),
                    None => Arc::new(None::<Option<T>>),
                }
            }
            None => Arc::new(Some(None::<AnyBox>)),
        }
    }

    fn distribute(&self) -> AnyBox {
        match self {
            Some(x) => {
                if let Some(opt) = x.clone_box().downcast_ref::<Option<AnyBox>>() {
                    Arc::new(Some(opt.clone()))
                } else {
                    Arc::new(None::<Option<T>>)
                }
            }
            None => Arc::new(Some(None::<AnyBox>)),
        }
    }
}

impl<T, E> Traversable for Result<T, E>
where
    T: TypeOps + Clone + Send + Sync + 'static,
    E: TypeOps + Clone + Send + Sync + 'static
{
    fn traverse<F>(&self, f: Arc<F>) -> AnyBox 
    where 
        F: Fn(AnyBox) -> AnyBox + Send + Sync + 'static
    {
        match self {
            Ok(x) => {
                let fx = f(x.clone_box());
                match fx.downcast_ref::<Result<AnyBox, AnyBox>>() {
                    Some(res) => Arc::new(Some(res.clone())),
                    None => Arc::new(None::<Result<T, E>>),
                }
            }
            Err(e) => Arc::new(Some(Err::<AnyBox, AnyBox>(e.clone_box()))),
        }
    }

    fn distribute(&self) -> AnyBox {
        match self {
            Ok(x) => {
                if let Some(res) = x.clone_box().downcast_ref::<Result<AnyBox, AnyBox>>() {
                    Arc::new(Some(res.clone()))
                } else {
                    Arc::new(None::<Result<T, E>>)
                }
            }
            Err(e) => Arc::new(Some(Err::<AnyBox, AnyBox>(e.clone_box()))),
        }
    }
}