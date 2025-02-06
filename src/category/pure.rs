use crate::category::hkt::{HKT, ReturnTypeConstraints};

/// The Pure trait represents a type that can lift a value into a context.
/// 
/// # Type Parameters
/// * `T` - The type of the value to be lifted.
///
/// # Laws
/// A Pure instance must satisfy these laws:
/// 1. Identity Preservation: For any value `x`,
///    `pure(x).map(id) = pure(x)`
/// 2. Homomorphism: For any function `f` and value `x`,
///    `pure(f(x)) = pure(x).map(f)`
/// 3. Interchange: For any function `f` and value `x`,
///    `pure(f).apply(pure(x)) = pure(x).map(f)`
/// 4. Naturality: For any natural transformation `η: F ~> G`,
///    `η(pure(x)) = pure(x)`
/// 5. Consistency with Applicative: For any value `x`,
///    `pure(x)` in Applicative context behaves the same as `pure(x)` in Pure context
/// 6. Consistency with Monad: For any value `x`,
///    `pure(x)` in Monad context behaves the same as `pure(x)` in Pure context
///
pub trait Pure<T>: HKT
where
    T: ReturnTypeConstraints,
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