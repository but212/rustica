use crate::category::hkt::{HKT, ReturnTypeConstraints};
use crate::fntype::SendSyncFnTrait;

/// A trait for types that can be traversed.
///
/// # Laws
/// A Traversable instance must satisfy these laws:
/// 1. Naturality: For any natural transformation `η: F ~> G` and traversable `t`,
///    `η(traverse(t, f)) = traverse(t, η ∘ f)`
/// 2. Identity: For any traversable `t`,
///    `traverse(t, pure) = pure(t)`
/// 3. Composition: For any traversable `t` and applicative functors `F` and `G`,
///    `traverse(t, f ∘ g) = compose(traverse(t, f), traverse(t, g))`
/// 4. Functor: For any traversable `t` and function `f`,
///    `traverse(t, f).map(g) = traverse(t, f.map(g))`
/// 5. Sequence Consistency: For any traversable `t`,
///    `traverse(t, id) = sequence(t)`
/// 6. Effect Order: For any traversable `t`,
///    The order of effects in `traverse(t, f)` must match the structure of `t`
/// 7. Pure Traversal: For any traversable `t` and pure function `f`,
///    `traverse(t, f)` should not have any side effects beyond those in `f`
///
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