use crate::category::hkt::{HKT, ReturnTypeConstraints};

/// The Pure trait represents a type that can lift a value into a context.
pub trait Pure<T>: HKT
where
    T: ReturnTypeConstraints,
{
    /// Lift a value into the context.
    ///
    /// # Parameters
    /// - `value`: The value to be lifted into the context.
    ///
    /// # Returns
    /// A new instance of the context containing the lifted value.
    fn pure(value: T) -> Self::Output<T>;
}