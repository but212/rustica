//! # Category
//!
//! This module provides the `Category` trait which represents a category in the sense of
//! category theory. Categories are a fundamental mathematical structure that help model
//! and organize various types of objects and the mappings between them.
//!
//! ## Mathematical Definition
//!
//! A category consists of:
//! - A collection of objects
//! - A collection of morphisms (arrows) between objects
//! - An identity morphism for each object
//! - A composition operation for morphisms
//!
//! **Note on Rust Implementation Limitations:**
//! In pure category theory, a category explicitly maintains a collection of objects.
//! However, in Rust's type system, objects are represented implicitly through the
//! type parameters of morphisms. This is a necessary compromise due to Rust's
//! static typing and the difficulty of representing arbitrary object collections
//! at the type level.
//!
//! ## Laws
//!
//! A valid category must satisfy these laws:
//!
//! 1. Identity:
//! ```text
//! f ??id = f = id ??f
//! ```
//! Composing any morphism with identity leaves it unchanged.
//!
//! 2. Associativity:
//! ```text
//! f ??(g ??h) = (f ??g) ??h
//! ```
//! The order of composition doesn't matter.
//!
//! ## Note on Composition Order
//!
//! In this crate, `compose_morphisms(g, f)` represents the mathematical composition `g ??f`.
//! That is, `f` is applied first, then `g`.
//!
//! ## Common Use Cases
//!
//! The Category trait is commonly used in scenarios where:
//!
//! 1. **Function Composition**
//!    - Representing pure functions and their composition
//!    - Building complex transformations from simple ones
//!
//! 2. **Type-safe Transformations**
//!    - Ensuring type safety in data transformations
//!    - Modeling data flow between different types
//!
//! 3. **Abstract Algebra**
//!    - Implementing mathematical structures
//!    - Defining algebraic data types
//!
//! ## Relationship with Other Functional Traits
//!
//! - **Functor**: Functors are mappings between categories that preserve structure.
//!   They build on the concept of categories.
//!
//! - **Monad**: Monads are a specific kind of functor with additional operations that
//!   follow certain laws. They can be seen as structures within a category.

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
///    f ??id = f = id ??f
///    ```
///    Composing any morphism with identity leaves it unchanged.
///
/// 2. Associativity:
///    ```text
///    f ??(g ??h) = (f ??g) ??h
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
#[deprecated(
    since = "0.13.0",
    note = "Category has only one implementor. Category will be removed in 0.14.0."
)]
pub trait Category {
    type Morphism<A, B>;

    /// Creates an identity morphism for the given types.
    ///
    /// The identity morphism is a function that returns its input unchanged.
    /// It serves as the unit element for morphism composition.
    /// Mathematical definition: id_A: A ??A where id_A(a) = a
    ///
    /// # Type Parameters
    /// * `A`: The type for which to create the identity morphism
    ///
    /// # Returns
    ///
    /// A morphism representing the identity function for type A
    fn identity_morphism<A>() -> Self::Morphism<A, A>;

    /// Composes two morphisms in the category.
    ///
    /// Given morphisms f: A ??B and g: B ??C, produces a new morphism (g ??f): A ??C.
    /// Mathematical definition: (g ??f)(x) = g(f(x))
    /// This means f is applied first, then g is applied to the result.
    ///
    /// # Parameter Order Convention
    ///
    /// This function follows the mathematical convention where compose_morphisms(g, f)
    /// produces g ??f, meaning f is applied first, then g. This matches the standard
    /// functional programming convention used in Haskell and other languages.
    ///
    /// # Type Parameters
    ///
    /// * `A`: The input type of the first morphism to be applied
    /// * `B`: The intermediate type (output of f, input of g)
    /// * `C`: The output type of the final result
    ///
    /// # Arguments
    ///
    /// * `g`: The second morphism to apply (B ??C)
    /// * `f`: The first morphism to apply (A ??B)
    ///
    /// # Returns
    ///
    /// A new morphism representing the composition (g ??f): A ??C
    fn compose_morphisms<A, B, C>(
        g: &Self::Morphism<B, C>, f: &Self::Morphism<A, B>,
    ) -> Self::Morphism<A, C>
    where
        A: 'static,
        B: 'static,
        C: 'static;
}
