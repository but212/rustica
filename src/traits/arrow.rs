use crate::traits::hkt::TypeConstraints;
use crate::traits::category::Category;
use crate::fntype::FnTrait;

/// Arrow type class.
///
/// # Type Parameters
/// * `A` - The base type for this arrow
/// * `Morphism<B, C>` - The type of morphisms from B to C in this category.
///
/// # Laws
/// An arrow must satisfy these laws:
/// 1. arrow id >>> f = f = f >>> arrow id
/// 2. (f >>> g) >>> h = f >>> (g >>> h)
/// 3. first (f >>> g) = first f >>> first g
/// 4. first (arrow f) = arrow (f × id)
/// 5. first f >>> arrow (id × g) = arrow (id × g) >>> first f
/// 6. first f >>> arrow fst = arrow fst >>> f
/// 7. first (first f) >>> arrow assoc = arrow assoc >>> first f
pub trait Arrow<A: TypeConstraints, B: TypeConstraints>: Category<A> {
    /// Creates an arrow from a function.
    fn arrow<F: FnTrait<A, B>>(f: F) -> Self::Morphism<A, B>
    {
        FnTrait::new(move |x| f.call(x))
    }

    /// Applies a morphism to the first component of a pair.
    fn first<C>(f: Self::Morphism<A, B>) -> Self::Morphism<(A, C), (B, C)>
    where
        C: TypeConstraints,
    {
        FnTrait::new(move |x: (A, C)| (f.call(x.0), x.1))
    }

    /// Applies a morphism to the second component of a pair.
    fn second<C>(f: Self::Morphism<A, B>) -> Self::Morphism<(C, A), (C, B)>
    where
        C: TypeConstraints,
    {
        FnTrait::new(move |x: (C, A)| (x.0, f.call(x.1)))
    }

    /// Splits a single input into two outputs using two different morphisms.
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
    /// This method takes two morphisms, `f: B -> C` and `g: D -> E`, and combines them
    /// to create a new morphism that applies `f` to the first component of a pair and
    /// `g` to the second component.
    ///
    /// # Type Parameters
    /// * `B`: The input type of the first morphism
    /// * `C`: The output type of the first morphism
    /// * `D`: The input type of the second morphism
    /// * `E`: The output type of the second morphism
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