use crate::fntype::{FnType, FnTrait};
use crate::traits::hkt::{HKT, TypeConstraints};

/// A trait for contravariant functors.
///
/// Contravariant functors allow mapping from a larger type to a smaller type,
/// which is the opposite of covariant functors.
///
/// # Type Parameters
/// * `T`: The type parameter of the contravariant functor.
///
/// # Laws
/// 
/// A ContravariantFunctor instance must satisfy these laws:
/// 
/// 1. Identity: For any contravariant functor `f`,
///    `f.contramap(|x| x) = f`
/// 2. Composition: For any contravariant functor `f` and functions `g`, `h`,
///    `f.contramap(|x| g(h(x))) = f.contramap(h).contramap(g)`
/// 3. Naturality: For any natural transformation `η` and contravariant functor `f`,
///    `η(f.contramap(g)) = η(f).contramap(g)`
/// 4. Type Safety: For `f: F[A]`, `g: B -> A`, then `f.contramap(g): F[B]`
/// 5. Consistency: For any contravariant functor `f` and functions `g`, `h`,
///    `f.contramap(g.compose(h)) = f.contramap(h).contramap(g)`
/// 6. Preservation of Structure: `contramap` must preserve the structure of the functor
pub trait ContravariantFunctor<T>: HKT + TypeConstraints
where
    T: TypeConstraints,
{
    /// Applies a function `f` to the input of the contravariant functor.
    ///
    /// # Type Parameters
    /// * `U`: The new input type for the contravariant functor.
    /// * `F`: The type of the function to apply.
    ///
    /// # Arguments
    /// * `f`: A function that maps from `U` to `T`.
    ///
    /// # Returns
    /// A new contravariant functor with input type `U`.
    fn contravariant_map<U, F>(self, f: F) -> Self::Output<U>
    where
        U: TypeConstraints,
        F: FnTrait<U, T>;

    /// Extracts the inner value from the contravariant functor.
    ///
    /// # Returns
    /// The inner value of type `T`.
    fn into_inner(self) -> T;

    /// Composes two functions in a contravariant manner.
    ///
    /// # Type Parameters
    /// * `U`: An intermediate type.
    /// * `V`: The initial input type.
    /// * `F`: The type of the first function.
    /// * `G`: The type of the second function.
    ///
    /// # Arguments
    /// * `f`: A function that maps from `U` to `T`.
    /// * `g`: A function that maps from `V` to `U`.
    ///
    /// # Returns
    /// A new function that maps from `V` to `T`.
    fn contravariant_compose<U, V, F, G>(f: F, g: G) -> impl FnTrait<V, T>
    where
        U: TypeConstraints,
        V: TypeConstraints,
        F: FnTrait<U, T>,
        G: FnTrait<V, U>,
    {
        FnType::new(move |v| f.call(g.call(v)))
    }
}