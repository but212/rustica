use crate::fntype::{FnType, FnTrait};
use crate::category::hkt::{HKT, TypeConstraints};

/// A trait for contravariant functors.
///
/// # Laws
/// 1. Identity: `f.contramap(|x| x) = f`
/// 2. Composition: `f.contramap(|x| g(h(x))) = f.contramap(h).contramap(g)`
/// 3. Naturality: `η(f.contramap(g)) = η(f).contramap(g)`
///
/// # Examples
///
/// ```
/// use rustica::prelude::*;
///
/// #[derive(Clone, Debug, PartialEq, Eq, Default)]
/// struct Predicate<A: TypeConstraints>(FnType<A, bool>);
///
/// impl<A: TypeConstraints> HKT for Predicate<A> {
///     type Output<T> = Predicate<T> where T: TypeConstraints;
/// }
///
/// impl<A: TypeConstraints> ContravariantFunctor<A> for Predicate<A> {
///     fn contravariant_map<B, F>(self, f: F) -> <Predicate<A> as rustica::prelude::HKT>::Output<B>
///     where
///         B: TypeConstraints,
///         F: FnTrait<B, A>,
///     {
///         Predicate(FnType::new(move |b| self.0.call(f.call(b))))
///     }
///
///     fn into_inner(self) -> A {
///         unimplemented!("Predicate does not have a meaningful inner value")
///     }
/// }
///
/// let greater_than_5 = Predicate(FnType::new(|x: i32| x > 5));
/// let length_greater_than_5 = greater_than_5.contravariant_map(FnType::new(|s: String| s.len() as i32));
///
/// assert!(length_greater_than_5.0.call("123456".to_string()));
/// assert!(!length_greater_than_5.0.call("1234".to_string()));
/// ```
pub trait ContravariantFunctor<T>: HKT + TypeConstraints
where
    T: TypeConstraints,
{
    fn contravariant_map<U, F>(self, f: F) -> Self::Output<U>
    where
        U: TypeConstraints,
        F: FnTrait<U, T>;

    fn into_inner(self) -> T;

    fn contravariant_compose<U, V, F, G>(f: F, g: G) -> FnType<V, T>
    where
        U: TypeConstraints,
        V: TypeConstraints,
        F: FnTrait<U, T>,
        G: FnTrait<V, U>,
    {
        FnType::new(move |v| f.call(g.call(v)))
    }
}
