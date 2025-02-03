use crate::fntype::{SendSyncFn, SendSyncFnTrait};
use crate::category::hkt::{HKT, ReturnTypeConstraints};

/// A ContravariantFunctor is a type constructor that provides a way to map a function over its contents
/// in a contravariant way. Unlike regular functors that map from A to B, contravariant functors map
/// from B to A, effectively reversing the direction of the transformation.
///
/// # Type Parameters
/// * `T` - The type of value contained in the contravariant functor
///
/// # Laws
/// A contravariant functor must satisfy these laws:
/// 1. Identity: `f.contramap(|x| x) = f`
/// 2. Composition: `f.contramap(g).contramap(h) = f.contramap(|x| g(h(x)))`
///
/// # Example
/// ```rust
/// // Predicate is a contravariant functor that wraps a function from T -> bool
/// struct Predicate<T>(Box<dyn Fn(T) -> bool>);
///
/// impl<T> ContravariantFunctor<T> for Predicate<T> {
///     fn contramap<U, F>(self, f: F) -> Predicate<U>
///     where
///         F: SendSyncFnTrait<U, T>
///     {
///         Predicate(Box::new(move |x| (self.0)(f.call(x))))
///     }
/// }
/// ```
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