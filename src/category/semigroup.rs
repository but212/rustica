use std::collections::{HashMap, HashSet};
use std::hash::Hash;
use crate::category::hkt::TypeConstraints;

/// A trait for semigroups, which are types with an associative binary operation.
/// 
/// # Type Parameters
/// * `T` - The type of elements in the semigroup
/// 
/// # Laws
/// A Semigroup instance must satisfy these laws:
/// 1. Associativity: For any values `x`, `y`, `z`,
///    `x.combine(y.combine(z)) = (x.combine(y)).combine(z)`
/// 2. Closure: For any values `x`, `y`,
///    `x.combine(y)` must be of the same type as `x` and `y`
/// 3. Naturality: For any natural transformation `η: F ~> G`,
///    `η(x.combine(y)) = η(x).combine(η(y))`
/// 4. Totality: For any values `x`, `y`,
///    `x.combine(y)` must be defined for all `x` and `y`
/// 5. Well-Defined: For any values `x`, `y`,
///    `x.combine(y)` must be deterministic
/// 6. Non-Empty: For any semigroup `S`,
///    There must exist at least one element
/// 7. Commutativity (if applicable): For any values `x`, `y`,
///    `x.combine(y) = y.combine(x)`
/// 8. Idempotency (if applicable): For any value `x`,
///    `x.combine(x) = x`
pub trait Semigroup: TypeConstraints {
    /// Combines two values of the same type.
    ///
    /// # Arguments
    /// * `other` - Another value of the same type
    ///
    /// # Returns
    /// The combined result
    fn combine(self, other: Self) -> Self;

    /// Combines all elements in an iterator using the semigroup operation.
    ///
    /// # Type Parameters
    /// * `I` - The type of the iterator
    ///
    /// # Arguments
    /// * `iter` - An iterator over elements of the semigroup
    ///
    /// # Returns
    /// The combined result, or None if the iterator is empty
    fn combine_all<I>(mut iter: I) -> Option<Self>
    where
        I: Iterator<Item = Self>,
    {
        iter.next().map(|first| iter.fold(first, |acc, x| acc.combine(x)))
    }

    /// Combines all elements in an iterator with an initial value.
    ///
    /// # Type Parameters
    /// * `I` - The type of the iterator
    ///
    /// # Arguments
    /// * `init` - The initial value
    /// * `iter` - An iterator over elements of the semigroup
    ///
    /// # Returns
    /// The combined result starting with the initial value
    fn combine_all_with<I>(&self, iter: I) -> Self
    where
        I: IntoIterator<Item = Self>,
    {
        iter.into_iter().fold(self.clone(), |acc, x| acc.combine(x))
    }
}

// Basic type implementations
impl Semigroup for String {
    fn combine(self, other: Self) -> Self {
        self + &other
    }
}

impl<T: Clone + Send + Sync + 'static> Semigroup for Vec<T>
where
    T: TypeConstraints,
{
    fn combine(mut self, other: Self) -> Self {
        self.extend(other);
        self
    }
}

impl<T: Eq + Hash + Clone + Send + Sync + 'static> Semigroup for HashSet<T>
where
    T: TypeConstraints,
{
    fn combine(mut self, other: Self) -> Self {
        self.extend(other);
        self
    }
}

impl<K, V> Semigroup for HashMap<K, V>
where
    K: Eq + Hash + TypeConstraints,
    V: Semigroup,
{
    fn combine(mut self, other: Self) -> Self {
        for (k, v) in other {
            match self.remove(&k) {
                Some(existing) => {
                    self.insert(k, existing.combine(v));
                }
                None => {
                    self.insert(k, v);
                }
            }
        }
        self
    }
}

// Tuple implementations
impl<A: Semigroup, B: Semigroup> Semigroup for (A, B) {
    fn combine(self, other: Self) -> Self {
        (self.0.combine(other.0), self.1.combine(other.1))
    }
}

impl<A: Semigroup, B: Semigroup, C: Semigroup> Semigroup for (A, B, C) {
    fn combine(self, other: Self) -> Self {
        (
            self.0.combine(other.0),
            self.1.combine(other.1),
            self.2.combine(other.2),
        )
    }
}

/// Combines multiple Semigroup elements with an initial value.
///
/// # Type Parameters
/// * `S` - The type of the semigroup
///
/// # Arguments
/// * `init` - The initial value
/// * `items` - A vector of semigroup elements
///
/// # Returns
/// The combined result
pub fn combine_all_with<S: Semigroup>(init: S, items: Vec<S>) -> S {
    items.into_iter().fold(init, |acc, x| acc.combine(x))
}
