use crate::traits::monad::Monad;
use crate::traits::hkt::TypeConstraints;
use crate::fntype::FnTrait;

/// A trait for comonads, which are the categorical dual of monads.
///
/// Comonads represent computations that provide a value along with a context,
/// and allow for operations that manipulate both the value and its context.
///
/// # Type Parameters
/// * `A`: The type of value contained in the comonad.
///
/// # Laws
/// 
/// A Comonad instance must satisfy these laws:
/// 
/// 1. Left Identity: For any comonad `w`,
///    `extract(duplicate(w)) = w`
/// 2. Right Identity: For any comonad `w`,
///    `duplicate(extract(w)) = w`
/// 3. Associativity: For any comonad `w`,
///    `duplicate(duplicate(w)) = fmap(duplicate)(duplicate(w))`
/// 4. Extend/Cobind: For any comonad `w` and function `f`,
///    `extend(f)(w) = fmap(f)(duplicate(w))`
/// 5. Extract Naturality: For any comonad `w` and function `f`,
///    `extract(fmap(f)(w)) = f(extract(w))`
pub trait Comonad<A>: Monad<A>
where
    A: TypeConstraints,
{
    /// Extracts the focused value from the comonad.
    ///
    /// This operation removes one layer of comonadic structure.
    ///
    /// # Returns
    /// The value of type `A` contained within the comonad.
    fn extract(self) -> A;

    /// Creates a nested comonad structure.
    ///
    /// This operation adds one layer of comonadic structure.
    ///
    /// # Returns
    /// A new comonad containing the original comonad as its value.
    ///
    /// # Type Parameters
    /// * `Self::Output<Self>`: The type of the resulting nested comonad.
    fn duplicate(self) -> Self::Output<Self>
    where
        Self: Sized;

    /// Maps a function over the comonad context.
    ///
    /// This operation applies a function that takes the whole comonad as input
    /// and produces a new value, which is then wrapped in the comonad structure.
    ///
    /// # Type Parameters
    /// * `B`: The type of the resulting value after applying the function.
    /// * `F`: The type of the function to be applied.
    ///
    /// # Parameters
    /// * `f`: A function that takes the comonad as input and produces a value of type `B`.
    ///
    /// # Returns
    /// A new comonad containing the result of applying the function.
    ///
    /// # Constraints
    /// * `B: TypeConstraints`: The resulting type must satisfy the type constraints.
    /// * `F: FnTrait<Self, B>`: The function must be compatible with the comonad and result type.
    /// * `Self: Sized`: The comonad type must have a known size.
    fn extend<B, F>(self, f: F) -> Self::Output<B>
    where
        B: TypeConstraints,
        F: FnTrait<Self, B>,
        Self: Sized;

    /// Extracts a value by applying a function to the comonad.
    ///
    /// This is a convenience method that combines `extract` and `extend`.
    ///
    /// # Type Parameters
    /// * `B`: The type of the resulting value after applying the function.
    /// * `F`: The type of the function to be applied.
    ///
    /// # Parameters
    /// * `f`: A function that takes the comonad as input and produces a value of type `B`.
    ///
    /// # Returns
    /// The result of applying the function to the comonad.
    ///
    /// # Constraints
    /// * `B: TypeConstraints`: The resulting type must satisfy the type constraints.
    /// * `F: FnTrait<Self, B>`: The function must be compatible with the comonad and result type.
    /// * `Self: Sized`: The comonad type must have a known size.
    fn extract_with<B, F>(self, f: F) -> B
    where
        B: TypeConstraints,
        F: FnTrait<Self, B>,
        Self: Sized;
}