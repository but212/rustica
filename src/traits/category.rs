use crate::traits::composable::Composable;
use crate::traits::hkt::TypeConstraints;
use crate::fntype::FnTrait;

/// A trait for categories in category theory.
///
/// A category consists of:
/// * Objects (represented by types)
/// * Morphisms (represented by functions between objects)
/// * Identity morphisms for each object
/// * A composition operation for morphisms
///
/// # Type Parameters
/// * `A` - The type of objects in this category
///
/// # Laws
/// 1. Identity: `id_A ∘ f = f = f ∘ id_B` for any morphism f: A → B
/// 2. Associativity: `(f ∘ g) ∘ h = f ∘ (g ∘ h)` for composable morphisms
/// 3. Type Safety: Composition preserves source and target types
pub trait Category<A>: Composable<A>
where
    A: TypeConstraints,
{
    /// The type of morphisms in this category
    type Morphism<B, C>: FnTrait<B, C> where B: TypeConstraints, C: TypeConstraints;

    /// Returns the identity morphism for a given type
    fn identity_morphism<B: TypeConstraints>() -> Self::Morphism<B, B> {
        FnTrait::new(|x| x)
    }

    /// Composes two morphisms in this category
    fn compose_morphisms<B, C>(f: Self::Morphism<A, B>, g: Self::Morphism<B, C>) -> Self::Morphism<A, C>
    where
        B: TypeConstraints,
        C: TypeConstraints,
    {
        FnTrait::new(move |x| g.call(f.call(x)))
    }
}