use crate::traits::applicative::Applicative;

/// A trait for structures that can be traversed from left to right while preserving structure
/// and accumulating effects in an applicative functor.
///
/// # Mathematical Definition
///
/// For a type constructor `T`, a traversable instance consists of two operations:
/// - `traverse`: `(A -> F<B>) -> T<A> -> F<T<B>>`
/// - `sequence`: `T<F<A>> -> F<T<A>>`
///
/// where `F` is an applicative functor.
///
/// # Type Parameters
///
/// The trait is implemented on types that implement `Applicative`, where:
/// * `Source` is the type of elements in the traversable structure
/// * `Output<T>` represents the structure containing elements of type `T`
///
/// # Laws
///
/// For a valid `Traversable` implementation, the following laws must hold:
///
/// 1. Naturality:
/// ```text
/// t.traverse(f).map(g) = t.traverse(x -> f(x).map(g))
/// ```
/// Natural transformations commute with traversals.
///
/// 2. Identity:
/// ```text
/// t.traverse(Identity::pure) = Identity::pure(t)
/// ```
/// Traversing with the identity applicative functor is equivalent to pure.
///
/// 3. Composition:
/// ```text
/// t.traverse(Compose::pure) = Compose::pure(t.traverse(f).map(_.traverse(g)))
/// ```
/// Traversing with composed applicative functors is equivalent to composing traversals.
///
/// # Common Use Cases
///
/// The `Traversable` trait is commonly used in scenarios where:
/// - You need to sequence effects while maintaining structure
/// - You want to perform parallel or distributed computations
/// - You need to validate multiple values while collecting errors
/// - You want to transform a structure of effects into an effect of structure
pub trait Traversable: Applicative {
    /// Traverses the structure, applying the given function to each element and collecting the results.
    ///
    /// This method allows you to apply an effect-producing function to each element in the structure,
    /// and then collect all of these effects into a single effect containing the new structure.
    ///
    /// # Type Parameters
    ///
    /// * `F`: The applicative functor representing the effect
    /// * `B`: The type of elements in the resulting structure
    /// * `Func`: The type of the function to apply to each element
    ///
    /// # Arguments
    ///
    /// * `f`: A function that takes a reference to an element of type `Self::Source` and returns an effect `F::Output<B>`
    ///
    /// # Returns
    ///
    /// An effect `F::Output` containing the new structure `Self::Output<B>`
    fn traverse<F, B, Func>(&self, f: Func) -> F::Output<Self::Output<B>>
    where
        F: Applicative,
        Func: Fn(&Self::Source) -> F::Output<B>;

    /// Sequences a structure of effects into an effect of structure.
    ///
    /// This operation takes a structure where each element is an effect and
    /// reorders it into a single effect containing a structure of values.
    /// It is equivalent to `traverse(identity)` when the elements are already effects.
    ///
    /// # Type Parameters
    ///
    /// * `F`: The applicative functor containing the effects
    ///
    /// # Returns
    ///
    /// The reordered structure wrapped in a single effect
    fn sequence<F>(&self) -> F::Output<Self::Output<F::Source>>
    where
        F: Applicative,
        Self::Source: Into<F::Output<F::Source>>;
}