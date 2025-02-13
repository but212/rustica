use crate::category::hkt::{HKT, TypeConstraints};

/// The Pure trait represents a type that can lift a value into a context.
/// 
/// # Type Parameters
/// * `T` - The type of the value to be lifted.
///
/// # Laws
/// A Pure instance must satisfy these laws:
/// 1. Identity Preservation: For any value `x`,
///    `pure(x).fmap(id) = pure(x)`
/// 2. Homomorphism: For any function `f` and value `x`,
///    `pure(f(x)) = pure(x).fmap(f)`
/// 3. Interchange: For any function `f` and value `x`,
///    `pure(f).apply(pure(x)) = pure(x).fmap(f)`
/// 4. Naturality: For any natural transformation `η: F ~> G`,
///    `η(pure(x)) = pure(x)`
///
pub trait Pure<T>: HKT
where
    T: TypeConstraints,
{
    /// Lift a value into the context.
    ///
    /// # Arguments
    /// - `value`: The value to be lifted into the context.
    ///
    /// # Returns
    /// A new instance of the context containing the lifted value.
    fn pure(value: T) -> Self::Output<T>;
}