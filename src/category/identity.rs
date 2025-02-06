use crate::category::hkt::{HKT, ReturnTypeConstraints};

/// A trait for types that represent the identity element in a monoid.
/// 
/// # Type Parameters
/// * `T` - The type of the identity element.
///
/// # Laws
/// An identity instance must satisfy these laws:
/// 1. Left Identity: For any value `x`, `combine(identity(), x) = x`
/// 2. Right Identity: For any value `x`, `combine(x, identity()) = x`
/// 3. Uniqueness: For any value `x`, if `combine(x, y) = x` and `combine(y, x) = x` for all `x`,
///    then `y = identity()`
/// 4. Preservation Under Transformation: For any morphism `f`,
///    `f(identity()) = identity()`
/// 5. Natural Identity: For any natural transformation `η: F ~> G`,
///    `η(identity()) = identity()`
///
pub trait Identity: HKT {
    /// The identity element of the type.
    /// 
    /// # Returns
    /// A new `Self` instance that is the identity element.
    fn identity<T>() -> Self::Output<T>
    where
        T: ReturnTypeConstraints;
}