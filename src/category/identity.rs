use crate::category::hkt::{HKT, ReturnTypeConstraints};

/// A trait for types that represent the identity element in a monoid.
/// 
/// # Type Parameters
/// * `T` - The type of the identity element.
/// 
/// # Laws
/// An Identity instance must satisfy these laws:
/// 1. Identity: For any value `x`,
///    `identity()` is the identity element.
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
    /// The identity element of the type.
    /// 
    /// # Returns
    /// A new `Self` instance that is the identity element.
    fn identity<T>() -> Self::Output<T>
    where
        T: ReturnTypeConstraints;
}