use crate::traits::composable::Composable;
use crate::traits::hkt::TypeConstraints;
use crate::fntype::FnTrait;

/// A trait representing categories in category theory.
///
/// A category consists of:
/// * Objects (represented by types)
/// * Morphisms (represented by functions between objects)
/// * Identity morphisms for each object
/// * A composition operation for morphisms
///
/// # Type Parameters
/// * `A`: The type of objects in this category
///
/// # Laws
/// 
/// An Category instance must satisfy these laws:
/// 
/// 1. Identity: For any morphism `f: A → B`,
///    `id_A ∘ f = f = f ∘ id_B`
/// 2. Associativity: For composable morphisms `f`, `g`, `h`,
///    `(f ∘ g) ∘ h = f ∘ (g ∘ h)`
/// 3. Type Safety: Composition preserves source and target types
///
/// # Implementor's Guide
/// When implementing this trait, ensure that:
/// * The `Morphism` associated type correctly represents morphisms between objects
/// * `identity_morphism` returns a valid identity morphism for any object
/// * `compose_morphisms` correctly composes two morphisms, preserving type safety
pub trait Category<A>: Composable<A>
where
    A: TypeConstraints,
{
    /// The type of morphisms in this category
    type Morphism<B, C>: FnTrait<B, C> where B: TypeConstraints, C: TypeConstraints;

    /// Returns the identity morphism for a given type
    ///
    /// # Type Parameters
    /// * `B`: The type for which to create an identity morphism
    ///
    /// # Returns
    /// An identity morphism of type `Morphism<B, B>`
    fn identity_morphism<B: TypeConstraints>() -> Self::Morphism<B, B> {
        FnTrait::new(|x| x)
    }

    /// Composes two morphisms in this category
    ///
    /// # Type Parameters
    /// * `B`: The intermediate type in the composition
    /// * `C`: The target type of the composition
    ///
    /// # Parameters
    /// * `f`: A morphism from `A` to `B`
    /// * `g`: A morphism from `B` to `C`
    ///
    /// # Returns
    /// A new morphism representing the composition of `f` and `g`
    fn compose_morphisms<B, C>(f: Self::Morphism<A, B>, g: Self::Morphism<B, C>) -> Self::Morphism<A, C>
    where
        B: TypeConstraints,
        C: TypeConstraints,
    {
        FnTrait::new(move |x| g.call(f.call(x)))
    }
}