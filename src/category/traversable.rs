use crate::category::hkt::{HKT, ReturnTypeConstraints};
use crate::fntype::SendSyncFnTrait;

/// A trait for traversable structures that can be traversed with effects.
/// 
/// # Type Parameters
/// * `T` - The type of elements in the traversable structure
/// 
/// # Laws
/// A Traversable instance must satisfy these laws:
/// 1. Naturality: For any natural transformation `η: F ~> G`,
///    `η(traverse(f)(t)) = traverse(η ∘ f)(t)`
/// 2. Identity: For any traversable `t`,
///    `traverse(Identity)(t) = Identity(t)`
/// 3. Composition: For any traversable `t` and applicatives `F`, `G`,
///    `traverse(Compose ∘ map(g) ∘ f)(t) = Compose ∘ map(traverse(g)) ∘ traverse(f)(t)`
/// 4. Sequence Consistency: For any traversable `t`,
///    `traverse(id)(t) = sequence(t)`
/// 5. Functor Consistency: For any traversable `t` and function `f`,
///    `traverse(pure ∘ f)(t) = pure(map(f)(t))`
/// 6. Foldable Consistency: For any traversable `t`,
///    `fold_map(f) = getConst ∘ traverse(Const ∘ f)`
/// 7. Effect Order: For any traversable `t`,
///    Effects must be performed in a consistent order
/// 8. Structure Preservation: For any traversable `t`,
///    The shape and structure must be preserved after traversal
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