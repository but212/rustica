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

    /// Tests if this category satisfies the category laws for the given morphism.
    /// This is useful for testing implementations.
    fn test_category_laws<B, C>(
        f: Self::Morphism<B, C>
    ) -> bool
    where
        B: ReturnTypeConstraints,
        C: ReturnTypeConstraints,
        Self::Morphism<B, C>: PartialEq,
    {
        let id_b = Self::identity_morphism::<B>();
        let id_c = Self::identity_morphism::<C>();
        let f_clone = f.clone();

        // Left identity: id_C ∘ f = f
        let left_id = Self::compose_morphisms(f.clone(), id_c) == f_clone;

        // Right identity: f ∘ id_B = f
        let right_id = Self::compose_morphisms(id_b, f) == f_clone;

        left_id && right_id
    }

    /// Tests if this category satisfies the associativity law for the given morphisms.
    /// This is useful for testing implementations.
    fn test_associativity<B, C, D, E>(
        f: Self::Morphism<B, C>,
        g: Self::Morphism<C, D>,
        h: Self::Morphism<D, E>
    ) -> bool
    where
        B: ReturnTypeConstraints,
        C: ReturnTypeConstraints,
        D: ReturnTypeConstraints,
        E: ReturnTypeConstraints,
        Self::Morphism<B, E>: PartialEq,
    {
        // h ∘ (g ∘ f) = (h ∘ g) ∘ f
        let left = Self::compose_morphisms(
            Self::compose_morphisms(f.clone(), g.clone()),
            h.clone()
        );
        let right = Self::compose_morphisms(
            f,
            Self::compose_morphisms(g, h)
        );
        left == right
    }
}