use std::collections::{HashMap, HashSet};
use std::hash::Hash;
use crate::traits::hkt::TypeConstraints;

/// A trait for semigroups, which are types with an associative binary operation.
/// 
/// # Type Parameters
/// 
/// * `T` - The type of elements in the semigroup
/// 
/// # Laws
/// 
/// A Semigroup instance must satisfy these laws:
/// 
/// 1. Associativity: For any values `x`, `y`, `z`,
///    `x.combine(y.combine(z)) = (x.combine(y)).combine(z)`
/// 2. Closure: For any values `x`, `y`,
///    `x.combine(y)` must be of the same type as `x` and `y`
/// 3. Naturality: For any natural transformation `η: F ~> G`,
///    `η(x.combine(y)) = η(x).combine(η(y))`
pub trait Semigroup<T>
where
    T: TypeConstraints,
{
    /// Combines two values of the same type.
    ///
    /// # Arguments
    ///
    /// * `other` - Another value of the same type
    ///
    /// # Returns
    ///
    /// The combined result
    fn combine(self, other: Self) -> Self;

    /// Combines all elements in an iterator using the semigroup operation.
    ///
    /// # Type Parameters
    ///
    /// * `I` - The type of the iterator
    ///
    /// # Arguments
    ///
    /// * `iter` - An iterator over elements of the semigroup
    ///
    /// # Returns
    ///
    /// The combined result, or None if the iterator is empty
    fn combine_all<I>(iter: I) -> Option<Self>
    where
        I: IntoIterator<Item = Self>,
        Self: Sized,
    {
        iter.into_iter().reduce(|a, b| a.combine(b))
    }
}

// Basic type implementations
impl<T> Semigroup<T> for Vec<T>
where
    T: TypeConstraints,
{
    fn combine(mut self, other: Self) -> Self {
        self.extend(other);
        self
    }
}

impl Semigroup<char> for String {
    fn combine(mut self, other: Self) -> Self {
        self.push_str(&other);
        self
    }
}

impl<T> Semigroup<T> for HashSet<T>
where
    T: TypeConstraints + Eq + Hash,
{
    fn combine(mut self, other: Self) -> Self {
        self.extend(other);
        self
    }
}

impl<K, V> Semigroup<V> for HashMap<K, V>
where
    K: TypeConstraints + Eq + Hash,
    V: TypeConstraints,
{
    fn combine(mut self, other: Self) -> Self {
        self.extend(other);
        self
    }
}

// Tuple implementations
impl<A, B> Semigroup<(A, B)> for (A, B)
where
    A: Semigroup<A> + TypeConstraints,
    B: Semigroup<B> + TypeConstraints,
{
    fn combine(self, other: Self) -> Self {
        (self.0.combine(other.0), self.1.combine(other.1))
    }
}

impl<A, B, C> Semigroup<(A, B, C)> for (A, B, C)
where
    A: Semigroup<A> + TypeConstraints,
    B: Semigroup<B> + TypeConstraints,
    C: Semigroup<C> + TypeConstraints,
{
    fn combine(self, other: Self) -> Self {
        (
            self.0.combine(other.0),
            self.1.combine(other.1),
            self.2.combine(other.2),
        )
    }
}
