use crate::traits::monoid::Monoid;
use crate::traits::hkt::HKT;

/// A `Foldable` type is a data structure that can be "folded" into a summary value.
///
/// # Mathematical Definition
///
/// A foldable structure represents a container that supports a catamorphism operation,
/// which allows reducing the structure to a single value by applying a combining function
/// to its elements.
///
/// # Type Parameters
///
/// The trait is implemented on types that implement `HKT`, where:
/// * `Source` is the type of elements in the foldable structure
/// * `Output<T>` represents the structure containing elements of type `T`
///
/// # Laws
///
/// For a valid `Foldable` implementation, the following laws must hold:
///
/// 1. Identity:
/// ```text
/// t.fold_left(|x| x) = t.fold_right(|x| x)
/// ```
/// Left and right folds with the identity function should yield the same result.
///
/// 2. Composition:
/// ```text
/// t.fold_left(f).fold_left(g) = t.fold_left(|acc, x| g(f(acc, x)))
/// ```
/// Folding with f and then g should be equivalent to folding with their composition.
///
/// 3. Naturality:
/// ```text
/// η(t.fold_left(f)) = η(t).fold_left(f)
/// ```
/// Where η is a natural transformation.
///
/// 4. Monoid Consistency:
/// ```text
/// t.fold_left(M::combine)(M::empty()) = t.fold_right(M::combine)(M::empty())
/// ```
/// Folding with a monoid's combine operation should give the same result regardless
/// of association.
///
/// # Common Use Cases
///
/// The `Foldable` trait is commonly used in scenarios where:
/// - You need to reduce a collection to a single value
/// - You want to traverse a structure while accumulating results
/// - You need to combine elements using a monoid operation
/// - You want to perform operations like sum, product, or concatenation
pub trait Foldable: HKT {
    /// Left-associative fold of a structure.
    ///
    /// Reduces the structure to a single value by applying a combining function from
    /// left to right, starting with an initial value.
    ///
    /// # Type Parameters
    ///
    /// * `U`: The type of the accumulated value
    ///
    /// # Arguments
    ///
    /// * `init`: The initial value for the fold
    /// * `f`: The combining function that takes the accumulator and an element
    ///
    /// # Returns
    ///
    /// The final accumulated value
    fn fold_left<U>(&self, init: &U, f: &dyn Fn(&U, &Self::Source) -> U) -> U;

    /// Right-associative fold of a structure.
    ///
    /// Reduces the structure to a single value by applying a combining function from
    /// right to left, starting with an initial value.
    ///
    /// # Type Parameters
    ///
    /// * `U`: The type of the accumulated value
    ///
    /// # Arguments
    ///
    /// * `init`: The initial value for the fold
    /// * `f`: The combining function that takes an element and the accumulator
    ///
    /// # Returns
    ///
    /// The final accumulated value
    fn fold_right<U>(&self, init: &U, f: &dyn Fn(&Self::Source, U) -> U) -> U;

    /// Maps elements to a monoid and combines them.
    ///
    /// This operation first maps each element to a value in a monoid, then combines
    /// all these values using the monoid's combine operation.
    ///
    /// # Type Parameters
    ///
    /// * `M`: The monoid type that elements will be mapped to
    ///
    /// # Arguments
    ///
    /// * `f`: The function that maps elements to the monoid type
    ///
    /// # Returns
    ///
    /// The combined monoid value
    fn fold_map<M: Monoid>(&self, f: &dyn Fn(&Self::Source) -> M) -> M;

    /// Returns the number of elements in the structure.
    ///
    /// This is a convenience method that counts the number of elements by
    /// folding over the structure with a counter.
    ///
    /// # Returns
    ///
    /// The number of elements in the structure
    #[inline]
    fn length(&self) -> usize {
        self.fold_left(&0, &|acc, _| acc + 1)
    }

    /// Tests if the structure is empty.
    #[inline]
    fn is_empty(&self) -> bool {
        self.length() == 0
    }
}