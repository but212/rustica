use crate::traits::hkt::{TypeOps, AnyBox, HKT};
use std::sync::Arc;

/// A trait representing categories in category theory.
///
/// A category consists of:
/// * Objects (represented by types)
/// * Morphisms (represented by functions between objects)
/// * Identity morphisms for each object
/// * A composition operation for morphisms
///
/// # Laws
/// 
/// A Category instance must satisfy these laws:
/// 
/// 1. Left Identity: For any morphism `f`,
///    `compose(identity_morphism, f) = f`
/// 2. Right Identity: For any morphism `f`,
///    `compose(f, identity_morphism) = f`
/// 3. Associativity: For any morphisms `f`, `g`, and `h`,
///    `compose(compose(f, g), h) = compose(f, compose(g, h))`
pub trait Category: HKT {
    /// Returns the identity morphism for this category.
    ///
    /// # Returns
    /// A boxed value that represents this category's identity morphism.
    fn identity_morphism() -> AnyBox;

    /// Composes this category with another morphism.
    ///
    /// # Arguments
    /// * `other`: The morphism to compose with
    ///
    /// # Returns
    /// A new boxed value representing the composition of morphisms.
    fn compose_morphism(&self, other: &AnyBox) -> AnyBox;
}

impl<T> Category for Vec<T> 
where 
    T: TypeOps + Clone + Send + Sync + 'static 
{
    fn identity_morphism() -> AnyBox {
        Arc::new(Vec::<T>::new()) as AnyBox
    }

    fn compose_morphism(&self, other: &AnyBox) -> AnyBox {
        other.downcast_ref::<Vec<AnyBox>>()
            .map(|vec| {
                let mut result: Vec<T> = Vec::new();
                for x in vec {
                    if let Some(inner) = x.downcast_ref::<Vec<T>>() {
                        result.extend(inner.iter().cloned());
                    }
                }
                Arc::new(result) as AnyBox
            })
            .unwrap_or_else(|| Arc::new(Vec::<T>::new()) as AnyBox)
    }
}

impl<T> Category for Option<T> 
where 
    T: TypeOps + Default + Clone + Send + Sync + 'static 
{
    fn identity_morphism() -> AnyBox {
        Arc::new(Some(T::default())) as AnyBox
    }

    fn compose_morphism(&self, other: &AnyBox) -> AnyBox {
        if let Some(opt) = other.downcast_ref::<Option<T>>() {
            match (self, opt) {
                (Some(_), Some(b)) => Arc::new(Some(b.clone())) as AnyBox,
                _ => Arc::new(None::<T>) as AnyBox
            }
        } else {
            Arc::new(None::<T>) as AnyBox
        }
    }
}

impl<T, E> Category for Result<T, E> 
where 
    T: TypeOps + Default + Clone + Send + Sync + 'static,
    E: Send + Sync + Eq + Clone + Default + 'static
{
    fn identity_morphism() -> AnyBox {
        Arc::new(Ok::<T, E>(T::default())) as AnyBox
    }

    fn compose_morphism(&self, other: &AnyBox) -> AnyBox {
        if let Some(result) = other.downcast_ref::<Result<T, E>>() {
            match (self, result) {
                (Ok(_), Ok(b)) => Arc::new(Ok::<T, E>(b.clone())) as AnyBox,
                (Err(e), _) | (_, Err(e)) => Arc::new(Err::<T, E>(e.clone())) as AnyBox,
            }
        } else {
            Arc::new(Err::<T, E>(E::default())) as AnyBox
        }
    }
}
