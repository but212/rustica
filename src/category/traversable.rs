use crate::category::hkt::{HKT, ReturnTypeConstraints};
use crate::fntype::SendSyncFnTrait;

/// A trait for types that can be traversed.
pub trait Traversable: HKT {
    /// A method for traversing a type.
    /// 
    /// # Type Parameters
    /// * `T` - The type to be traversed.
    /// * `U` - The type to be returned.
    /// * `F` - The function to be applied to each element of the type.
    ///
    /// Returns
    /// * `Self::Output<U>` - The result of the traversal.
    fn traverse<T, U, F>(self, f: F) -> Self::Output<U>
    where
        T: ReturnTypeConstraints,
        U: ReturnTypeConstraints,
        F: SendSyncFnTrait<T, U>,
    ;
}