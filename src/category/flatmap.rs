use crate::category::hkt::ReturnTypeConstraints;
use crate::fntype::FnTrait;
use crate::category::monad::Monad;

/// A trait for types that support flattening of nested structures.
///
/// # Type Parameters
/// * `T` - The type of the value within the structure.
///
/// # Laws
/// 1. Associativity: `m.flat_map(f).flat_map(g) = m.flat_map(|x| f(x).flat_map(g))`
/// 2. Consistency with FMap: `m.flat_map(|x| pure(f(x))) = m.fmap(f)`
/// 3. Flattening Identity: `flatten(pure(m)) = m`
/// 4. Map-Flatten Consistency: `m.flat_map(f) = flatten(fmap(f)(m))`
///
pub trait FlatMap<T>: Monad<T>
where
    T: ReturnTypeConstraints,
{
    fn flat_map<U, F>(self, f: F) -> Self::Output<U>
    where
        U: ReturnTypeConstraints,
        F: FnTrait<T, Self::Output<U>>,
        Self: Sized,
    {
        self.bind(f)
    }
}
