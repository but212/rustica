use crate::fntype::{SendSyncFn, SendSyncFnTrait};
use crate::category::hkt::{HKT, ReturnTypeConstraints};

/// A contravariant functor is a type constructor that provides a way to map a function over its contents.
/// 
/// # Type Parameters
/// * `T` - The type of value contained in the contravariant functor
/// 
///  # Laws
/// A contravariant functor must satisfy these laws:
/// 1. Identity: `contravariant_map(|x| x) = contravariant_functor`
/// 2. Composition: `contravariant_map(f).contravariant_map(g) = contravariant_map(|x| g(f(x)))`
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
