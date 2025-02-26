use crate::traits::hkt::HKT;

/// A trait for types that can lift values into a higher-kinded context.
///
/// The `Pure` trait represents the ability to take a pure value and lift it into
/// a higher-kinded context. This operation is also known as `return` or `unit` in
/// functional programming literature.
///
/// # Mathematical Definition
///
/// Given:
/// - A type constructor `F` (implementing `HKT`)
/// - A value `x` of type `A`
///
/// The `pure` operation creates an `F<A>` containing `x`.
///
/// # Type Parameters
///
/// The trait is implemented on types that implement `HKT`, where:
/// * `Source` is the type of value being lifted
/// * `Output<T>` is the higher-kinded context
///
/// # Laws
///
/// For a valid `Pure` implementation, the following laws must hold:
///
/// 1. Identity Law:
/// ```text
/// pure(x).map(|y| y) = pure(x)
/// ```
/// Lifting a value and then mapping the identity function over it should be
/// equivalent to just lifting the value.
///
/// 2. Homomorphism Law:
/// ```text
/// pure(f).apply(pure(x)) = pure(f(x))
/// ```
/// Applying a lifted function to a lifted value should be the same as
/// applying the function to the value and then lifting the result.
///
/// 3. Interchange Law:
/// ```text
/// u.apply(pure(y)) = pure(|f| f(y)).apply(u)
/// ```
/// Where `u` is an applicative containing a function.
///
/// # Common Use Cases
///
/// The `Pure` trait is commonly used in scenarios where:
/// - You need to lift values into a context (e.g., wrapping in `Option` or `Result`)
/// - You're implementing functors or applicatives
/// - You're working with higher-kinded types
/// - You need to chain operations that may fail or have side effects
///
/// Common implementations include:
/// - `Option`: Lifts values into `Some`
/// - `Result`: Lifts values into `Ok`
/// - `Vec`: Creates a single-element vector
/// - Custom effect types or monads
pub trait Pure: HKT {
    /// Lifts a value into a higher-kinded context.
    ///
    /// This operation takes a pure value of type `T` and wraps it in the higher-kinded
    /// context defined by `Self::Output`.
    ///
    /// # Type Parameters
    ///
    /// * `T`: The type of value to lift
    ///
    /// # Arguments
    ///
    /// * `value`: The value to lift into the higher-kinded context
    ///
    /// # Returns
    ///
    /// The value wrapped in the higher-kinded context
    fn pure<T: Clone>(value: T) -> Self::Output<T>;
}