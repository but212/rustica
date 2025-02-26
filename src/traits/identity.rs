use crate::traits::hkt::HKT;

/// A trait for types that represent identity functions in category theory.
///
/// In category theory, an identity morphism (or identity function) is a morphism that
/// leaves an object unchanged. The Identity trait provides functionality for working
/// with identity functions in a type-safe way.
///
/// # Type Parameters
/// The trait is implemented on types that implement `HKT`, where:
/// * `Source` is the type being transformed
/// * `Output<T>` represents the result type after transformation
///
/// # Laws
/// For a valid Identity implementation:
///
/// 1. Left Identity:
///    identity().compose(f) == f
///
/// 2. Right Identity:
///    f.compose(identity()) == f
///
/// 3. Uniqueness:
///    identity::<A>() == identity::<A>()
///
/// # Examples
///
/// Basic implementation:
/// ```rust
/// use rustica::traits::hkt::HKT;
/// use rustica::traits::identity::Identity;
///
/// struct Id<T>(T);
///
/// impl<T> HKT for Id<T> {
///     type Source = T;
///     type Output<U> = U;
/// }
///
/// impl<T> Identity for Id<T> {
///     fn value(&self) -> &Self::Source {
///         &self.0
///     }
/// }
/// ```
///
/// # Common Use Cases
///
/// Identity functions are commonly used in:
/// - Function composition, where they act as neutral elements
/// - Generic programming, to represent "no-op" transformations
/// - Testing and debugging, to verify the correctness of other functions
/// - Implementing certain algebraic structures in category theory
/// - As default or placeholder implementations in trait methods
pub trait Identity: HKT {
    /// Creates an identity function for the given type.
    ///
    /// The identity function returns its input unchanged, serving as the identity
    /// element in function composition.
    ///
    /// # Type Parameters
    /// * `T`: The type of value to create an identity function for
    ///
    /// # Arguments
    /// * `x`: The value to return unchanged
    ///
    /// # Returns
    /// The input value `x` unchanged
    fn value(&self) -> &Self::Source;

    /// Returns the input value unchanged, serving as the identity function.
    ///
    /// # Type Parameters
    ///
    /// * `A`: The type of the input value.
    ///
    /// # Arguments
    ///
    /// * `a`: The value to be returned unchanged.
    ///
    /// # Returns
    ///
    /// The input value `a` of type `A`.
    fn identity<A>(a: A) -> A {
        a
    }
}