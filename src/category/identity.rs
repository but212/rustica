use crate::category::hkt::{HKT, ReturnTypeConstraints};
use crate::category::category::Category;

/// A trait for types that represent the identity element in a monoid.
/// 
/// # Type Parameters
/// * `T` - The type of the identity element.
/// 
/// # Laws
/// An Identity instance must satisfy these laws:
/// 1. Identity: For any value `x`,
///    `identity()` is the identity element and `id(x) = x`.
/// 2. Composition: For any identity `i` and functions `f`, `g`,
///    `f(g(identity())) = f(g(x))` for any `x`.
/// 3. Naturality: For any natural transformation `η: F ~> G`,
///    `η(identity()) = identity()`
/// 4. Functor Consistency: For any value `x` and function `f`,
///    `f(identity()) = f(x)` for any `x`.
/// 5. Pure Consistency: For any value `x`,
///    `identity()` is the pure value of `x`.
/// 6. Applicative Consistency: For any values `x`, `y` and function `f`,
///    `f(identity()) = f(x)` for any `x`.
/// 7. Monad Consistency: For any value `x` and function `f`,
///    `f(identity()) = f(x)` for any `x`.
/// 8. Isomorphism: For any value `x`,
///    `identity()` is isomorphic to `x`.
///
pub trait Identity: HKT {
    /// The identity function for any type.
    /// 
    /// # Type Parameters
    /// * `T` - The type of the value.
    /// 
    /// # Arguments
    /// * `x` - The value to return.
    /// 
    /// # Returns
    /// The same value that was passed in.
    fn identity<T>(x: T) -> T
    where
        T: ReturnTypeConstraints,
    {
        x
    }

    /// Converts the identity element to a category morphism.
    /// 
    /// # Type Parameters
    /// * `T` - The type of the value.
    /// * `C` - The category type.
    /// 
    /// # Returns
    /// The identity morphism in the category.
    fn to_morphism<T, C>() -> C::Morphism<T, T>
    where
        T: ReturnTypeConstraints,
        C: Category<T>,
    {
        C::identity_morphism()
    }
}