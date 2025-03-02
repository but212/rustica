use crate::traits::hkt::HKT;

/// A contravariant functor is a type constructor that allows mapping functions in a way that reverses
/// their direction. While regular functors map functions forward (A -> B), contravariant functors map
/// functions backward (B -> A).
///
/// # Mathematical Definition
///
/// In category theory, a contravariant functor F from category C to category D is a functor that:
/// - Maps objects A in C to objects F(A) in D
/// - Maps morphisms f: A -> B in C to morphisms F(f): F(B) -> F(A) in D, reversing the arrow
///
/// # Laws
///
/// A valid contravariant functor must satisfy these laws:
///
/// 1. Identity:
///    ```text
///    contravariant_map(id) = id
///    ```
///    Mapping the identity function should produce the identity function.
///
/// 2. Composition:
///    ```text
///    contravariant_map(f . g) = contravariant_map(g) . contravariant_map(f)
///    ```
///    The mapping of a composition should equal the composition of the mappings in reverse order.
///
/// # Common Use Cases
///
/// 1. **Comparison Functions**
///    - Transform comparisons to work with complex types
///    - Create derived orderings based on specific fields or properties
///
/// 2. **Predicates and Validation**
///    - Transform predicates to work with different input types
///    - Build complex validation rules from simpler ones
///
/// 3. **Callbacks and Event Handlers**
///    - Adapt callback signatures for different contexts
///    - Transform event handlers to work with different event types
pub trait ContravariantFunctor: HKT {
    /// Maps a function that transforms values of type U into values of type Self::Source,
    /// producing a new contravariant functor that works with type U.
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
        F: Fn(&U) -> Self::Source;
}
