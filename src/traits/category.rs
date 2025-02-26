use crate::traits::hkt::HKT;

/// A trait representing a category in category theory.
///
/// # Mathematical Definition
///
/// A category consists of:
/// 1. A collection of objects (types in our case)
/// 2. A collection of morphisms (functions) between objects
/// 3. A composition operation for morphisms
/// 4. An identity morphism for each object
///
/// # Laws
///
/// A category must satisfy these laws:
///
/// 1. Identity:
///    ```text
///    id ∘ f = f = f ∘ id
///    ```
///    Composing any morphism with identity leaves it unchanged.
///
/// 2. Associativity:
///    ```text
///    (f ∘ g) ∘ h = f ∘ (g ∘ h)
///    ```
///    The order of composition doesn't matter.
///
/// # Type Parameters
///
/// * `T`: The source type of the morphism
/// * `U`: The target type of the morphism
/// 
/// # Common Use Cases
///
/// 1. **Function Composition**
///    - Representing pure functions and their composition
///    - Building complex transformations from simple ones
///
/// 2. **Type-safe Transformations**
///    - Ensuring type safety in data transformations
///    - Modeling data flow between different types
///
/// 3. **Abstract Algebra**
///    - Implementing mathematical structures
///    - Defining algebraic data types
pub trait Category: HKT {
    type Morphism<S, T>;

    /// Creates an identity morphism for the current type.
    ///
    /// The identity morphism is a function that returns its input unchanged.
    /// It serves as the unit element for morphism composition.
    ///
    /// # Returns
    ///
    /// A new instance of Self that represents the identity morphism
    fn identity_morphism() -> Self::Morphism<Self::Source, Self::Output<Self::Source>>;

    /// Composes two morphisms in the category.
    ///
    /// Given morphisms f: A → B and g: B → C, produces a new morphism f ∘ g: A → C.
    ///
    /// # Type Parameters
    ///
    /// * `B`: The intermediate type in the composition
    /// * `C`: The result type of the composition
    ///
    /// # Arguments
    ///
    /// * `self`: The first morphism to compose (f)
    /// * `g`: The second morphism to compose with (g)
    ///
    /// # Returns
    ///
    /// A new morphism representing the composition of self and g
    fn compose_morphisms<A, B, C>(f: &Self::Morphism<A, B>, g: &Self::Morphism<B, C>) -> Self::Morphism<A, C>;
}