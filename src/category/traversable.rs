use crate::category::hkt::{HKT, ReturnTypeConstraints};
use crate::category::applicative::Applicative;
use crate::fntype::FnTrait;

/// A trait for traversable structures that can be traversed with effects.
/// 
/// Traversable provides a way to:
/// 1. Transform elements inside the structure while preserving the structure
/// 2. Accumulate effects in a specific order
/// 3. Combine multiple effectful computations
/// 
/// # Type Parameters
/// * `A` - The type of elements in the traversable structure
/// 
pub trait Traversable<A>: HKT 
where
    A: ReturnTypeConstraints,
{
    /// Traverse this structure with effects.
    /// 
    /// This method allows you to:
    /// 1. Apply a function that produces effects to each element
    /// 2. Collect all effects in a specific order
    /// 3. Preserve the original structure
    /// 
    /// # Type Parameters
    /// * `F` - The applicative functor that will contain the effects
    /// * `B` - The resulting type after applying the function
    /// * `Fn` - The function type that produces effects
    /// 
    /// # Returns
    /// A new structure wrapped in the effect type `F`
    fn traverse<F, B, Fn>(self, f: Fn) -> F::Output<Self::Output<B>>
    where
        F: Applicative<A>,
        B: ReturnTypeConstraints,
        Fn: FnTrait<A, F::Output<B>>;
}