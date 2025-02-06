use crate::category::hkt::{HKT, ReturnTypeConstraints};

/// A trait for types that represent the identity element in a monoid.
/// 
/// # Type Parameters
/// * `T` - The type of the identity element.
pub trait Identity: HKT {
    /// The identity element of the type.
    /// 
    /// # Returns
    /// A new `Self` instance that is the identity element.
    fn identity<T>() -> Self::Output<T>
    where
        T: ReturnTypeConstraints;
}