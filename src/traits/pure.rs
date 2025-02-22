use crate::traits::hkt::{TypeOps, AnyBox, HKT};
use std::sync::Arc;

/// The Pure trait represents a type that can lift a value into a context.
/// 
/// This trait is a fundamental part of the Applicative Functor abstraction,
/// allowing for the creation of a minimal context around a value.
/// 
/// # Laws
/// 
/// An implementation of Pure must satisfy the following laws:
/// 
/// 1. Identity: For any value `v`,
///    `pure(id).apply(v) = v`
/// 2. Composition: For any values `u`, `v`, `w`,
///    `pure(compose).apply(u).apply(v).apply(w) = u.apply(v.apply(w))`
/// 3. Homomorphism: For any function `f` and value `x`,
///    `pure(f).apply(pure(x)) = pure(f(x))`
/// 4. Interchange: For any applicative `u` and value `y`,
///    `u.apply(pure(y)) = pure(|f| f(y)).apply(u)`
/// 5. Naturality: For any function `f` and applicatives `x`, `y`,
///    `fmap(f)(x.apply(y)) = x.apply(fmap(|g| f.compose(g))(y))`
/// 6. Functor Consistency: For any value `x` and function `f`,
///    `pure(x).fmap(f) = pure(f(x))`
pub trait Pure: HKT + 'static {
    /// Lifts a value into the context.
    ///
    /// # Arguments
    ///
    /// * `value` - The value to be lifted into the context.
    ///
    /// # Returns
    ///
    /// A new instance of the context containing the lifted value.
    fn pure(value: AnyBox) -> AnyBox;
}

impl<T> Pure for Vec<T>
where
    T: TypeOps + 'static
{
    fn pure(value: AnyBox) -> AnyBox {
        // Create a single-element vector containing the value
        Arc::new(vec![value])
    }
}

impl<T> Pure for Option<T>
where
    T: TypeOps + 'static
{
    fn pure(value: AnyBox) -> AnyBox {
        // Wrap the value in Some
        Arc::new(Some(value))
    }
}

impl<K, V> Pure for Result<K, V>
where
    K: TypeOps + 'static,
    V: TypeOps + 'static
{
    fn pure(value: AnyBox) -> AnyBox {
        // Create a successful Result containing the value
        Arc::new(Ok::<AnyBox, AnyBox>(value))
    }
}