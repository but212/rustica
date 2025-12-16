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
//! # Laws
//!
//! For a valid Traversable implementation, the following laws must hold:
//!
//! 1. **Identity**:
//!    ```text
//!    traverse(pure) == pure
//!    ```
//!    Traversing with `pure` is the same as lifting the structure into the applicative.
//!
//! 2. **Composition**:
//!    ```text
//!    traverse(Compose . fmap(g) . f) == Compose . fmap(traverse(g)) . traverse(f)
//!    ```
//!    Traversing with a composed function is the same as composing traversals.
//!
//! 3. **Naturality**:
//!    ```text
//!    t . traverse(f) == traverse(t . f)
//!    ```
//!    For any applicative transformation `t`, traversing then transforming equals
//!    transforming then traversing.
//!
//! # Caveats
//!
//! ## `traverse_owned` and `FnOnce`
//!
//! The `traverse_owned` method uses `FnOnce` for its function parameter. This means:
//! - It works naturally for single-element containers (Option, Result)
//! - For multi-element containers (Vec), the function can only be called once,
//!   which limits its usefulness
//!
//! If you need to traverse a multi-element container with ownership semantics,
//! consider using `traverse` with explicit cloning or a different approach.

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
        Self::Source: Into<F::Output<F::Source>> + Clone,
    {
        self.traverse::<F, F::Source, _>(|x| x.clone().into())
    }

    /// Traverses the structure with ownership, applying the given function to each element and collecting the results.
    ///
    /// Similar to `traverse`, but takes ownership of the traversable structure, which can avoid unnecessary clones
    /// in certain situations.
    ///
    /// Note: with the current signature (`Func: FnOnce(Self::Source) -> ...`), this method is most
    /// naturally implementable for traversables that contain at most one element.
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
    fn traverse_owned<F, B, Func>(self, f: Func) -> F::Output<Self::Output<B>>
    where
        F: Applicative,
        Func: FnOnce(Self::Source) -> F::Output<B>,
        Self: Sized;

    /// Sequences a structure of effects with ownership, into an effect of structure.
    ///
    /// Similar to `sequence`, but takes ownership of the traversable structure, which can avoid
    /// unnecessary clones in certain situations.
    ///
    /// # Type Parameters
    ///
    /// * `F`: The applicative functor containing the effects
    ///
    /// # Returns
    ///
    /// The reordered structure wrapped in a single effect
    fn sequence_owned<F>(self) -> F::Output<Self::Output<F::Source>>
    where
        F: Applicative,
        Self::Source: Into<F::Output<F::Source>>,
        Self: Sized,
    {
        self.traverse_owned::<F, F::Source, _>(|x| x.into())
    }
}
