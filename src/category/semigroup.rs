use std::collections::{HashMap, HashSet};
use std::hash::Hash;
use crate::category::hkt::ReturnTypeConstraints;

/// A Semigroup is a type with an associative binary operation.
///
/// # Laws
/// A Semigroup instance must satisfy these laws:
/// 1. Associativity: For all `a`, `b`, and `c`,
///    `(a.combine(b)).combine(c) = a.combine(b.combine(c))`
/// 2. Closure: For all `a` and `b`,
///    `a.combine(b)` must be a valid value of the same type
/// 3. Well-Defined: For all `a` and `b`,
///    `a.combine(b)` must be deterministic and total
/// 4. Homomorphism: For any semigroup homomorphism `f`,
///    `f(x.combine(y)) = f(x).combine(f(y))`
/// 5. Naturality: For any natural transformation `η: F ~> G` between semigroup functors,
///    `η(x.combine(y)) = η(x).combine(η(y))`
/// 6. Consistency with Monoid (if applicable): For types that are also Monoids,
///    the combine operation must be consistent with the monoid's combine operation
pub trait Semigroup: ReturnTypeConstraints {
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
    T: ReturnTypeConstraints,
{
    fn combine(mut self, other: Self) -> Self {
        self.extend(other);
        self
    }
}

impl<T: Eq + Hash + Clone + Send + Sync + 'static> Semigroup for HashSet<T>
where
    T: ReturnTypeConstraints,
{
    fn combine(mut self, other: Self) -> Self {
        self.extend(other);
        self
    }
}

impl<K, V> Semigroup for HashMap<K, V>
where
    K: Eq + Hash + ReturnTypeConstraints,
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
