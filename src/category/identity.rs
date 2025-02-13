use crate::category::hkt::{HKT, TypeConstraints};
use crate::category::category::Category;

/// A trait for types that represent the identity element in a monoid.
///
/// # Laws
/// 1. Identity: `identity(x) = x`
/// 2. Composition: `f(g(identity())) = f(g(x))`
/// 3. Naturality: `η(identity()) = identity()`
/// 4. Functor, Applicative, Monad Consistency: `f(identity()) = f(x)`
/// 5. Isomorphism: `identity()` is isomorphic to `x`
///
/// # Examples
/// ```
/// use rustica::prelude::*;
///
/// struct MyIdentity;
///
/// impl HKT for MyIdentity {
///     type Output<T> = T where T: TypeConstraints;
/// }
///
/// impl Identity for MyIdentity {}
///
/// assert_eq!(MyIdentity::identity(5), 5);
/// ```
pub trait Identity: HKT {
    /// Identity function for any type.
    ///
    /// This function returns the input value as-is. It works for all types `T`
    /// where `T` implements the `TypeConstraints` trait.
    ///
    /// # Arguments
    /// * `x` - The value to be returned
    ///
    /// # Returns
    /// Returns the input value `x` unchanged.
    fn identity<T: TypeConstraints>(x: T) -> T {
        x
    }

    /// Converts the identity element to a category morphism.
    ///
    /// This method creates an identity morphism in the context of a given category `C`
    /// for a specific type `T`.
    ///
    /// # Type Parameters
    /// * `T`: The type for which the identity morphism is created.
    /// * `C`: The category in which the morphism is defined.
    ///
    /// # Returns
    /// Returns the identity morphism for type `T` in category `C`.
    ///
    /// # Constraints
    /// * `T` must satisfy `TypeConstraints`.
    /// * `C` must implement the `Category` trait.
    fn to_morphism<T, C>() -> C::Morphism<T, T>
    where
        T: TypeConstraints,
        C: Category,
    {
        C::identity_morphism()
    }
}