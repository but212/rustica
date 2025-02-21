use crate::traits::hkt::TypeConstraints;
use crate::traits::semigroup::Semigroup;
use std::collections::{HashMap, HashSet};
use std::hash::Hash;

/// A trait for monoids, which are semigroups with an identity element.
/// 
/// # Type Parameters
/// * `T` - The type of elements in the monoid
/// 
/// # Laws
/// A Monoid instance must satisfy these laws:
/// 1. Identity: For any value `x`,
///    `x.combine(empty()) = x = empty().combine(x)`
/// 2. Associativity: For any values `x`, `y`, `z`,
///    `x.combine(y.combine(z)) = (x.combine(y)).combine(z)`
/// 3. Empty Uniqueness: For any monoid `M`,
///    There exists a unique empty element `e` such that `e.combine(x) = x = x.combine(e)`
/// 4. Naturality: For any natural transformation `η: F ~> G`,
///    `η(x.combine(y)) = η(x).combine(η(y))`
/// 5. Empty Preservation: For any natural transformation `η`,
///    `η(empty()) = empty()`
pub trait Monoid<T>: Semigroup<T>
where
    T: TypeConstraints,
{
    /// Returns the identity element of the monoid.
    fn empty() -> Self;

    /// Combines all elements in an iterator.
    ///
    /// Unlike Semigroup's combine_all, this always returns a value
    /// by using the empty element when the iterator is empty.
    fn combine_all<I>(iter: I) -> Self
    where
        I: IntoIterator<Item = Self>,
        Self: Sized,
    {
        iter.into_iter().fold(Self::empty(), |a, b| a.combine(b))
    }
}

impl<T> Monoid<T> for Vec<T>
where
    T: TypeConstraints,
{
    fn empty() -> Self {
        Vec::new()
    }
}

impl Monoid<char> for String {
    fn empty() -> Self {
        String::new()
    }
}

impl<T> Monoid<T> for HashSet<T>
where
    T: TypeConstraints + Eq + Hash,
{
    fn empty() -> Self {
        HashSet::new()
    }
}

impl<K, V> Monoid<V> for HashMap<K, V>
where
    K: TypeConstraints + Eq + Hash,
    V: TypeConstraints,
{
    fn empty() -> Self {
        HashMap::new()
    }
}

impl<A, B> Monoid<(A, B)> for (A, B)
where
    A: Monoid<A> + TypeConstraints,
    B: Monoid<B> + TypeConstraints,
{
    fn empty() -> Self {
        (A::empty(), B::empty())
    }
}

impl<A, B, C> Monoid<(A, B, C)> for (A, B, C)
where
    A: Monoid<A> + TypeConstraints,
    B: Monoid<B> + TypeConstraints,
    C: Monoid<C> + TypeConstraints,
{
    fn empty() -> Self {
        (A::empty(), B::empty(), C::empty())
    }
}
