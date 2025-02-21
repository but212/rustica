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
/// 
/// * `A` - The type of elements in the traversable structure
/// 
/// # Laws
/// 
/// A Traversable instance must satisfy these laws:
/// 
/// 1. Naturality: For any natural transformation `t: F ~> G`,
///    `t(traverse_f(x)) = traverse_g(t ∘ f)(x)`
/// 2. Identity: `traverse_Identity(x) = Identity(x)`
/// 3. Composition: `traverse_Compose(f . g)(x) = Compose(traverse_f(traverse_g(x)))`
/// 4. Fmap Consistency: For any function `f`,
///    `fmap(f)(x) = traverse_Identity(f)(x)`
/// 5. Sequence Consistency: For any traversable `t`,
///    `sequence(t) = traverse_Identity(id)(t)`
/// 6. Fold Consistency: For any monoid `M` and function `f: A -> M`,
///    `fold_map(f)(t) = traverse_Const(f)(t)`
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
    /// 
    /// * `F` - The applicative functor that will contain the effects
    /// * `B` - The resulting type after applying the function
    /// * `Fn` - The function type that produces effects
    /// 
    /// # Arguments
    /// 
    /// * `self` - The traversable structure
    /// * `f` - A function that maps elements of type `A` to `F<B>`
    /// 
    /// # Returns
    /// 
    /// An `F`-structure containing a new traversable structure with elements of type `B`
    fn traverse<F, B, Fn>(self, f: Fn) -> F::Output<<Self as Bifunctor<A, A>>::Output<B, B>>
    where
        F: Applicative<A>,
        B: TypeConstraints,
        Fn: FnTrait<A, F::Output<B>>;

    /// Distribute a structure of effects into an effect of structure.
    /// 
    /// This method is equivalent to `traverse(identity)`.
    /// 
    /// # Type Parameters
    /// 
    /// * `F` - The applicative functor representing the effects
    /// * `B` - The type of elements in the resulting structure
    /// 
    /// # Returns
    /// 
    /// An `F`-structure containing the original structure with effects distributed
    fn distribute<F, B>(self) -> F::Output<<Self as Bifunctor<A, A>>::Output<B, B>>
    where
        F: Applicative<A>,
        B: TypeConstraints,
        Self: Sized;
}