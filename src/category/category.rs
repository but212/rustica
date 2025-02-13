use crate::category::hkt::TypeConstraints;
use crate::category::identity::Identity;
use crate::category::composable::Composable;
use crate::fntype::FnTrait;

/// A category in category theory.
/// 
/// # Type Parameters
/// * `A` - The base type for this category
/// * `Morphism<B, C>` - The type of morphisms from B to C in this category.
/// 
/// # Laws
/// 1. Identity: For any morphism f: B → C, id_C ∘ f = f = f ∘ id_B
/// 2. Associativity: For morphisms f: B → C, g: C → D, h: D → E, h ∘ (g ∘ f) = (h ∘ g) ∘ f
/// 
/// # Example
/// ```
/// use rustica::prelude::*;
/// 
/// #[derive(Debug, Clone, PartialEq, Eq, Default)]
/// struct MyCategory;
/// 
/// impl HKT for MyCategory {
///     type Output<T> = MyCategory where T: TypeConstraints;
/// }
/// 
/// impl Identity for MyCategory {
///     fn identity<A: TypeConstraints>(x: A) -> A { x }
/// }
/// 
/// impl Composable for MyCategory {
///     fn compose<A, B, C, F, G>(f: F, g: G) -> FnType<A, C>
///     where
///         A: TypeConstraints,
///         B: TypeConstraints,
///         C: TypeConstraints,
///         F: FnTrait<A, B>,
///         G: FnTrait<B, C>,
///     {
///         FnType::new(move |x| g.call(f.call(x)))
///     }
/// }
/// 
/// impl Category for MyCategory {
///     type Morphism<B, C> = FnType<B, C>
///     where
///         B: TypeConstraints,
///         C: TypeConstraints;
/// 
///     fn identity_morphism<B: TypeConstraints>() -> Self::Morphism<B, B> {
///         FnType::new(|x| x)
///     }
/// 
///     fn compose_morphisms<B, C, D>(
///         f: Self::Morphism<B, C>,
///         g: Self::Morphism<C, D>
///     ) -> Self::Morphism<B, D>
///     where
///         B: TypeConstraints,
///         C: TypeConstraints,
///         D: TypeConstraints,
///     {
///         FnType::new(move |x| g.call(f.call(x)))
///     }
/// }
/// 
/// let f = MyCategory::identity_morphism::<i32>();
/// assert_eq!(f.call(5), 5);
/// ```
pub trait Category: Identity + Composable {
    /// Represents a morphism (arrow) in the category from type `B` to type `C`.
    ///
    /// # Type Parameters
    /// * `B`: The source type of the morphism, must satisfy `TypeConstraints`
    /// * `C`: The target type of the morphism, must satisfy `TypeConstraints`
    ///
    /// This associated type should implement `FnTrait<B, C>`, allowing it to be called as a function.
    type Morphism<B, C>: FnTrait<B, C>
    where
        B: TypeConstraints,
        C: TypeConstraints;

    /// Returns the identity morphism for a given type B.
    ///
    /// The identity morphism is a fundamental concept in category theory.
    /// For any object B, the identity morphism is a morphism from B to itself
    /// that leaves the object unchanged when composed with any other morphism.
    ///
    /// # Type Parameters
    /// * `B`: The type for which to create the identity morphism
    ///
    /// # Returns
    /// A morphism that represents the identity function for type B
    ///
    /// # Constraints
    /// * `B`: Must satisfy `TypeConstraints`
    fn identity_morphism<B: TypeConstraints>() -> Self::Morphism<B, B> {
        FnTrait::new(|x| x)
    }

    /// Composes two morphisms in the category.
    ///
    /// This function takes two morphisms, `f: B -> C` and `g: C -> D`,
    /// and returns their composition `g ∘ f: B -> D`.
    ///
    /// # Type Parameters
    /// * `B`: The source type of the first morphism
    /// * `C`: The target type of the first morphism and source type of the second morphism
    /// * `D`: The target type of the second morphism
    ///
    /// # Arguments
    /// * `f`: The first morphism to compose
    /// * `g`: The second morphism to compose
    ///
    /// # Returns
    /// A new morphism representing the composition of `f` and `g`
    fn compose_morphisms<B, C, D>(f: Self::Morphism<B, C>, g: Self::Morphism<C, D>) -> Self::Morphism<B, D>
    where
        B: TypeConstraints,
        C: TypeConstraints,
        D: TypeConstraints,
    {
        FnTrait::new(move |x| g.call(f.call(x)))
    }
}