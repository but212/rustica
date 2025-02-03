use crate::fntype::{SendSyncFn, SendSyncFnTrait};
use crate::category::hkt::{HKT, ReturnTypeConstraints};

/// A contravariant functor is a type constructor that provides a way to map a function over its contents
pub trait ContravariantFunctor<T>: HKT + ReturnTypeConstraints
where
    T: ReturnTypeConstraints,
{
    /// Maps a function over the contents in a contravariant way.
    ///
    /// Unlike a regular functor's map which applies a function T -> U,
    /// contramap applies a function U -> T, effectively reversing the
    /// direction of the transformation.
    fn contramap<U, F>(self, f: F) -> Self::Output<U>
    where
        U: ReturnTypeConstraints,
        F: SendSyncFnTrait<U, T>;

    /// Retrieves the inner value from the contravariant functor.
    fn into_inner(self) -> T;

    /// Composes two functions in a contravariant way.
    ///
    /// This is a helper method that composes two functions f: U -> T and g: V -> U
    /// to produce a function V -> T in a contravariant way.
    fn compose<U, V, F, G>(f: F, g: G) -> SendSyncFn<V, T>
    where
        U: ReturnTypeConstraints,
        V: ReturnTypeConstraints,
        F: SendSyncFnTrait<U, T>,
        G: SendSyncFnTrait<V, U>,
    {
        SendSyncFn::new(move |v| f.call(g.call(v)))
    }
}