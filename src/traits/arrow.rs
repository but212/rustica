use crate::traits::hkt::TypeConstraints;
use crate::traits::category::Category;
use crate::fntype::FnTrait;

/// Arrow type class.
///
/// Arrows generalize computation and provide a way to express computations
/// that may be more general than simple functions.
///
/// # Type Parameters
/// * `A` - The base type for this arrow
/// * `B` - The target type for this arrow
///
/// # Associated Types
/// * `Morphism<X, Y>` - The type of morphisms from X to Y in this category.
/// 
/// # Laws
/// 
/// An Arrow instance must satisfy these laws:
/// 
/// 1. Identity: For any arrow `f`,
///    `arrow id >>> f = f = f >>> arrow id`
/// 2. Composition: For any arrows `f`, `g`, `h`,
///    `(f >>> g) >>> h = f >>> (g >>> h)`
/// 3. First Composition: For any arrows `f`, `g`,
///    `first (f >>> g) = first f >>> first g`
/// 4. First Arrow: For any function `f`,
///    `first (arrow f) = arrow (f × id)`
/// 5. First and Second Commutativity: For any arrow `f` and function `g`,
///    `first f >>> arrow (id × g) = arrow (id × g) >>> first f`
/// 6. First and Fst: For any arrow `f`,
///    `first f >>> arrow fst = arrow fst >>> f`
/// 7. First Associativity: For any arrow `f`,
///    `first (first f) >>> arrow assoc = arrow assoc >>> first f`
pub trait Arrow<A: TypeConstraints, B: TypeConstraints>: Category<A> {
    /// Creates an arrow from a function.
    ///
    /// # Type Parameters
    /// * `F` - A function type that implements `FnTrait<A, B>`
    ///
    /// # Arguments
    /// * `f` - The function to be converted into an arrow
    ///
    /// # Returns
    /// A morphism representing the arrow created from the function
    fn arrow<F: FnTrait<A, B>>(f: F) -> Self::Morphism<A, B> {
        FnTrait::new(move |x| f.call(x))
    }

    /// Applies a morphism to the first component of a pair.
    ///
    /// # Type Parameters
    /// * `C` - The type of the second component of the pair
    ///
    /// # Arguments
    /// * `f` - The morphism to be applied to the first component
    ///
    /// # Returns
    /// A new morphism that applies `f` to the first component of a pair
    fn first<C>(f: Self::Morphism<A, B>) -> Self::Morphism<(A, C), (B, C)>
    where
        C: TypeConstraints,
    {
        FnTrait::new(move |x: (A, C)| (f.call(x.0), x.1))
    }

    /// Applies a morphism to the second component of a pair.
    ///
    /// # Type Parameters
    /// * `C` - The type of the first component of the pair
    ///
    /// # Arguments
    /// * `f` - The morphism to be applied to the second component
    ///
    /// # Returns
    /// A new morphism that applies `f` to the second component of a pair
    fn second<C>(f: Self::Morphism<A, B>) -> Self::Morphism<(C, A), (C, B)>
    where
        C: TypeConstraints,
    {
        FnTrait::new(move |x: (C, A)| (x.0, f.call(x.1)))
    }

    /// Splits a single input into two outputs using two different morphisms.
    ///
    /// # Type Parameters
    /// * `C` - The type of the second output
    ///
    /// # Arguments
    /// * `f` - The first morphism to be applied
    /// * `g` - The second morphism to be applied
    ///
    /// # Returns
    /// A new morphism that applies both `f` and `g` to the input and returns a pair of results
    fn split<C>(
        f: Self::Morphism<A, B>,
        g: Self::Morphism<A, C>
    ) -> Self::Morphism<A, (B, C)>
    where
        C: TypeConstraints,
    {
        FnTrait::new(move |x: A| (f.call(x.clone()), g.call(x)))
    }

    /// Combines two morphisms to operate on pairs.
    ///
    /// This method takes two morphisms, `f: A -> B` and `g: C -> D`, and combines them
    /// to create a new morphism that applies `f` to the first component of a pair and
    /// `g` to the second component.
    ///
    /// # Type Parameters
    /// * `C`: The input type of the second morphism
    /// * `D`: The output type of the second morphism
    ///
    /// # Arguments
    /// * `f`: The morphism to apply to the first component
    /// * `g`: The morphism to apply to the second component
    ///
    /// # Returns
    /// A new morphism that applies `f` and `g` to the respective components of a pair
    fn combine_morphisms<C, D>(
        f: Self::Morphism<A, B>,
        g: Self::Morphism<C, D>
    ) -> Self::Morphism<(A, C), (B, D)>
    where
        C: TypeConstraints,
        D: TypeConstraints,
    {
        FnTrait::new(move |x: (A, C)| (f.call(x.0), g.call(x.1)))
    }
}