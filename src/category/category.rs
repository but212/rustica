use crate::category::hkt::ReturnTypeConstraints;
use crate::category::identity::Identity;
use crate::category::composable::Composable;

/// A category in category theory.
/// 
/// # Type Parameters
/// * `A` - The base type for this category
/// * `Morphism<B, C>` - The type of morphisms from B to C in this category.
/// 
/// # Laws
/// A category must satisfy these laws:
/// 1. Identity: For any morphism f: B → C,
///    id_C ∘ f = f = f ∘ id_B
/// 2. Associativity: For morphisms f: B → C, g: C → D, h: D → E,
///    h ∘ (g ∘ f) = (h ∘ g) ∘ f
pub trait Category<A>: Identity + Composable 
where
    A: ReturnTypeConstraints,
{
    /// The type of morphisms in this category.
    type Morphism<B, C>: ReturnTypeConstraints
    where
        B: ReturnTypeConstraints,
        C: ReturnTypeConstraints;

    /// Returns the identity morphism for the given type.
    /// For any type B, returns a morphism id_B: B → B that satisfies:
    /// - For any morphism f: B → C, id_C ∘ f = f
    /// - For any morphism g: C → B, g ∘ id_B = g
    fn identity_morphism<B>() -> Self::Morphism<B, B>
    where
        B: ReturnTypeConstraints;

    /// Composes two morphisms.
    /// For f: B → C and g: C → D, returns g ∘ f: B → D.
    fn compose_morphisms<B, C, D>(
        f: Self::Morphism<B, C>,
        g: Self::Morphism<C, D>
    ) -> Self::Morphism<B, D>
    where
        B: ReturnTypeConstraints,
        C: ReturnTypeConstraints,
        D: ReturnTypeConstraints;
}