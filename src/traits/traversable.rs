//! # Traversable
//!
//! A trait for structures that can be traversed from left to right while preserving structure
//! and accumulating effects in an applicative functor.
//!
//! # Mathematical Definition
//!
//! For a type constructor `T`, a traversable instance consists of two operations:
//! - `traverse`: `(A -> F<B>) -> T<A> -> F<T<B>>`
//! - `sequence`: `T<F<A>> -> F<T<A>>`
//!
//! where `F` is an applicative functor.
//!
//! # TODO
//!
//! - Add benchmarks for traversal operations
//! - Implement the Traversable trait for common types (Option, Result, Vec)
//! - Implement TraversableExt with additional utility methods such as:
//!   - for_each: Apply function for side effects only
//!   - flat_map: Map and flatten in one operation
//!   - traverse_map: Combine traverse and map
//!   - filter_a: Filter with applicative effects
//!   - zip_with: Combine two traversables

use crate::traits::applicative::Applicative;

/// A trait for structures that can be traversed from left to right while preserving structure
/// and accumulating effects in an applicative functor.
///
/// # Type Parameters
///
/// * `Source` is the type of elements in the traversable structure
/// * `Output<T>` represents the structure containing elements of type `T`
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
    fn traverse_ref<F, B, Func>(&self, f: Func) -> F::Output<Self::Output<B>>
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
    fn sequence_ref<F>(&self) -> F::Output<Self::Output<F::Source>>
    where
        F: Applicative,
        Self::Source: Into<F::Output<F::Source>> + Clone;

    /// Traverses the structure with ownership, applying the given function to each element and collecting the results.
    ///
    /// Similar to `traverse`, but takes ownership of the traversable structure, which can avoid unnecessary clones
    /// in certain situations.
    ///
    /// # Type Parameters
    ///
    /// * `F`: The applicative functor representing the effect
    /// * `B`: The type of elements in the resulting structure
    /// * `Func`: The type of the function to apply to each element
    ///
    /// # Arguments
    ///
    /// * `f`: A function that takes an element of type `Self::Source` and returns an effect `F::Output<B>`
    ///
    /// # Returns
    ///
    /// An effect `F::Output` containing the new structure `Self::Output<B>`
    fn traverse<F, B, Func>(self, f: Func) -> F::Output<Self::Output<B>>
    where
        F: Applicative,
        Func: FnOnce(Self::Source) -> F::Output<B>,
        Self: Sized;

    /// Sequences a structure of effects with ownership, into an effect of structure.
    ///
    /// Similar to `sequence_ref`, but takes ownership of the traversable structure, which can avoid
    /// unnecessary clones in certain situations.
    ///
    /// # Type Parameters
    ///
    /// * `F`: The applicative functor containing the effects
    ///
    /// # Returns
    ///
    /// The reordered structure wrapped in a single effect
    fn sequence<F>(self) -> F::Output<Self::Output<F::Source>>
    where
        F: Applicative,
        Self::Source: Into<F::Output<F::Source>>,
        Self: Sized;
}
