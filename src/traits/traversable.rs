use crate::traits::hkt::TypeConstraints;
use crate::traits::applicative::Applicative;
use crate::traits::bifunctor::Bifunctor;
use crate::traits::foldable::Foldable;
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
/// # Laws
/// 1. Naturality: `t(traverse(f)) = traverse(t ∘ f)`
/// 2. Identity: `traverse(Identity) = Identity`
/// 3. Composition: `traverse(Compose(f, g)) = Compose(traverse(f), traverse(g))`
pub trait Traversable<A>: Bifunctor<A, A> + Foldable<A>
where
    A: TypeConstraints,
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
    fn traverse<F, B, Fn>(self, f: Fn) -> F::Output<<Self as Bifunctor<A, A>>::Output<B, B>>
    where
        F: Applicative<A>,
        B: TypeConstraints,
        Fn: FnTrait<A, F::Output<B>>;

    /// Distribute a structure of effects into an effect of structure
    fn distribute<F, B>(self) -> F::Output<<Self as Bifunctor<A, A>>::Output<B, B>>
    where
        F: Applicative<A>,
        B: TypeConstraints,
        Self: Sized;
}