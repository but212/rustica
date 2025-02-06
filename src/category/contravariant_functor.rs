use crate::fntype::{SendSyncFn, SendSyncFnTrait};
use crate::category::hkt::{HKT, ReturnTypeConstraints};

/// A trait for contravariant functors, which are type constructors that can map a function over their contents
/// in a way that reverses the direction of the arrows.
/// 
/// # Type Parameters
/// * `T` - The type of value contained in the contravariant functor
/// 
/// # Laws
/// A Contravariant Functor instance must satisfy these laws:
/// 1. Identity: For any contravariant functor `f`,
///    `f.contramap(|x| x) = f`
/// 2. Composition: For any contravariant functor `f` and functions `g`, `h`,
///    `f.contramap(|x| g(h(x))) = f.contramap(h).contramap(g)`
/// 3. Structure Preservation: For any contravariant functor `f` and functions `g`, `h`,
///    `f.contramap(|x| g(h(x))) = f.contramap(h).contramap(g)`
/// 4. Naturality: For any natural transformation `η: F ~> G`,
///    `η(f.contramap(g)) = η(f).contramap(g)`
/// 5. Container Preservation: For any contravariant functor `f` and function `g`,
///    `f.contramap(g)` must preserve the structure of `f`
/// 6. Type Preservation: For any contravariant functor `f` and function `g`,
///    `f.contramap(g)` must maintain the same type constructor as `f`
/// 7. Parametricity: For any contravariant functor `f` and functions `g`, `h`,
///    If `g(x) = h(x)` for all `x`, then `f.contramap(g) = f.contramap(h)`
/// 8. Arrow Reversal: For any contravariant functor `f` and functions `g`, `h`,
///    `f.contramap(g).contramap(h) = f.contramap(|x| g(h(x)))`
pub trait ContravariantFunctor<T>: HKT + ReturnTypeConstraints
where
    T: ReturnTypeConstraints,
{
    /// Maps a function over the contents in a contravariant way.
    ///
    /// Unlike a regular functor's map which applies a function T -> U,
    /// contramap applies a function U -> T, effectively reversing the
    /// direction of the transformation.
    /// 
    /// # Type Parameters
    /// * `U` - The type of the mapped value.
    /// * `F` - The function to apply.
    /// 
    /// # Arguments
    /// * `self` - The contravariant functor instance.
    /// * `f` - The function to apply.
    /// 
    /// # Returns
    /// * `Self::Output<U>` - The mapped value.
    fn contravariant_map<U, F>(self, f: F) -> Self::Output<U>
    where
        U: ReturnTypeConstraints,
        F: SendSyncFnTrait<U, T>;

    /// Retrieves the inner value from the contravariant functor.
    /// 
    /// # Arguments
    /// * `self` - The contravariant functor instance.
    /// 
    /// # Returns
    /// * `T` - The inner value.
    fn into_inner(self) -> T;

    /// Composes two functions in a contravariant way.
    ///
    /// This is a helper method that composes two functions f: U -> T and g: V -> U
    /// to produce a function V -> T in a contravariant way.
    /// 
    /// # Type Parameters
    /// * `U` - The type of the first function's input.
    /// * `V` - The type of the second function's input.
    /// * `F` - The type of the first function.
    /// * `G` - The type of the second function.
    /// 
    /// # Arguments
    /// * `f` - The first function to compose.
    /// * `g` - The second function to compose.
    /// 
    /// # Returns
    /// * `SendSyncFn<V, T>` - The composed function.
    fn contravariant_compose<U, V, F, G>(f: F, g: G) -> SendSyncFn<V, T>
    where
        U: ReturnTypeConstraints,
        V: ReturnTypeConstraints,
        F: SendSyncFnTrait<U, T>,
        G: SendSyncFnTrait<V, U>,
    {
        SendSyncFn::new(move |v| f.call(g.call(v)))
    }
}
