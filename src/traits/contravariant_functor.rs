//! # Contravariant Functor
//!
//! A contravariant functor is a type constructor that allows mapping functions in a way that reverses
//! their direction. While regular functors map functions forward (A -> B), contravariant functors map
//! functions backward (B -> A).
//!
//! # Mathematical Definition
//!
//! In category theory, a contravariant functor F from category C to category D is a functor that:
//! - Maps objects A in C to objects F(A) in D
//! - Maps morphisms f: A -> B in C to morphisms F(f): F(B) -> F(A) in D, reversing the arrow
//!
//! # Laws
//!
//! A valid contravariant functor must satisfy these laws:
//!
//! 1. Identity:
//!    ```text
//!    contravariant_map(id) = id
//!    ```
//!    Mapping the identity function should produce the identity function.
//!
//! 2. Composition:
//!    ```text
//!    contravariant_map(f . g) = contravariant_map(g) . contravariant_map(f)
//!    ```
//!    The mapping of a composition should equal the composition of the mappings in reverse order.
//!
//! # Common Use Cases
//!
//! 1. **Comparison Functions**
//!    - Transform comparisons to work with complex types
//!    - Create derived orderings based on specific fields or properties
//!
//! 2. **Predicates and Validation**
//!    - Transform predicates to work with different input types
//!    - Build complex validation rules from simpler ones
//!
//! 3. **Callbacks and Event Handlers**
//!    - Adapt callback signatures for different contexts
//!    - Transform event handlers to work with different event types

use crate::traits::hkt::HKT;

/// A contravariant functor is a type constructor that allows mapping functions in a way that reverses
/// their direction. While regular functors map functions forward (A -> B), contravariant functors map
/// functions backward (B -> A).
pub trait ContravariantFunctor: HKT {
    /// Maps a function that transforms values of type U into values of type Self::Source,
    /// producing a new contravariant functor that works with type U.
    ///
    /// This is the reference-based version of contramap, which only takes a reference to self.
    ///
    /// # Type Parameters
    ///
    /// * `U`: The new input type for the resulting functor
    ///
    /// # Arguments
    ///
    /// * `f`: Function that converts from references of the new type U to Self::Source
    ///
    /// # Returns
    ///
    /// A new contravariant functor that works with values of type U
    fn contramap<U, F>(&self, f: F) -> Self::Output<U>
    where
        F: Fn(&U) -> Self::Source,
        U: Clone;

    /// Maps a function that transforms values of type U into values of type Self::Source,
    /// producing a new contravariant functor that works with type U.
    ///
    /// This is the ownership-based version of contramap, which takes ownership of self.
    ///
    /// # Type Parameters
    ///
    /// * `U`: The new input type for the resulting functor
    ///
    /// # Arguments
    ///
    /// * `f`: Function that converts from the new type U to Self::Source
    ///
    /// # Returns
    ///
    /// A new contravariant functor that works with values of type U
    fn contramap_owned<U, F>(self, f: F) -> Self::Output<U>
    where
        F: Fn(U) -> Self::Source,
        U: Clone,
        Self: Sized;
}

/// Extension methods for contravariant functors, providing additional utility functions.
pub trait ContravariantFunctorExt: ContravariantFunctor {
    /// Chains contramap operations for convenient method chaining.
    ///
    /// This method makes it easier to chain multiple contramap operations together.
    ///
    /// # Type Parameters
    ///
    /// * `U`: The new input type for the resulting functor
    ///
    /// # Arguments
    ///
    /// * `f`: Function that converts from references of the new type U to Self::Source
    ///
    /// # Returns
    ///
    /// A new contravariant functor that works with values of type U
    #[inline]
    fn contramap_with<U, F>(&self, f: F) -> Self::Output<U>
    where
        F: Fn(&U) -> Self::Source,
        U: Clone,
    {
        self.contramap(f)
    }

    /// Contramaps with a function that ignores its input, effectively creating a constant function.
    ///
    /// This is useful when you want to create a contravariant functor that always uses a specific value
    /// regardless of the input.
    ///
    /// # Type Parameters
    ///
    /// * `U`: The new input type for the resulting functor
    ///
    /// # Arguments
    ///
    /// * `value`: The constant value to use for all inputs
    ///
    /// # Returns
    ///
    /// A new contravariant functor that works with values of type U
    #[inline]
    fn contramap_const<U>(&self, value: Self::Source) -> Self::Output<U>
    where
        Self::Source: Clone,
        U: Clone,
    {
        let value_clone = value.clone();
        self.contramap(move |_: &U| value_clone.clone())
    }

    /// Composes two contravariant functors, creating a chain of transformations.
    ///
    /// # Type Parameters
    ///
    /// * `G`: Another contravariant functor
    ///
    /// # Arguments
    ///
    /// * `g`: Another contravariant functor
    ///
    /// # Returns
    ///
    /// A composed contravariant functor
    #[inline]
    fn contra_compose<G>(&self, _g: &G) -> Self::Output<G::Source>
    where
        G: ContravariantFunctor,
        G::Source: Clone,
        Self::Source: From<G::Source>,
    {
        self.contramap(|x: &G::Source| Self::Source::from(x.clone()))
    }
}

// Blanket implementation for ContravariantFunctorExt
impl<T: ContravariantFunctor> ContravariantFunctorExt for T {}
