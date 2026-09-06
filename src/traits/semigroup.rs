//! # Semigroup
//!
//! This module provides the `Semigroup` trait which represents an associative binary operation.
//!
//! In abstract algebra, a semigroup is an algebraic structure consisting of a set together
//! with an associative binary operation. The binary operation combines two elements from the set
//! to produce another element from the same set.
//!
//! ```rust
//! use rustica::traits::semigroup::Semigroup;
//! use rustica::datatypes::wrapper::{
//! product::Product,
//!     sum::Sum
//! };
//!
//! // Using the Sum wrapper for addition
//! let a = Sum(5);
//! let b = Sum(10);
//! let combined = a.combine(b);
//! assert_eq!(combined, Sum(15));
//!
//! // Using the Product wrapper for multiplication
//! let x = Product(2);
//! let y = Product(3);
//! let multiplied = x.combine(y);
//! assert_eq!(multiplied, Product(6));
//! ```

use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::hash::Hash;
use std::num::NonZeroUsize;

/// A trait for semigroups, which are algebraic structures with an associative binary operation.
/// A semigroup consists of a set together with a binary operation that combines two elements
/// of the set to yield a third element of the set, and the operation must be associative.
///
/// The associative property means that for any elements a, b, and c:
/// `(a ⋄ b) ⋄ c = a ⋄ (b ⋄ c)`
///
/// # Laws
///
/// If `a`, `b`, and `c` are values of a type that implements `Semigroup`, then:
///
/// ```text
/// (a.combine(b)).combine(c) == a.combine(b.combine(c))  // Associativity
/// ```
///
/// This allows chaining of operations without concern for the order of operations.
///
/// # Methods
///
/// The trait provides:
/// - `combine`: Combines two values by consuming them
///
/// Additional helper methods like `combine_n` are provided by `SemigroupExt`.
///
pub trait Semigroup: Sized {
    /// Combines two values by consuming them to produce a new value.
    ///
    /// # Parameters
    /// * `other`: Another value of the same type, which will be consumed
    ///
    /// # Returns
    /// A new value of the same type, which is the result of combining `self` and `other`.
    ///
    /// # Examples
    /// ```rust
    /// use rustica::traits::semigroup::Semigroup;
    ///
    /// let a = vec![1, 2, 3];
    /// let b = vec![4, 5, 6];
    /// let combined = a.combine(b);
    /// assert_eq!(combined, vec![1, 2, 3, 4, 5, 6]);
    /// ```
    fn combine(self, other: Self) -> Self;
}

/// Extension methods for semigroups, providing additional functionality.
pub trait SemigroupExt: Semigroup {
    /// Combines `self` with all the values in an iterator.
    #[inline]
    fn combine_all<I>(self, others: I) -> Self
    where
        I: IntoIterator<Item = Self>,
        Self: Sized,
    {
        others.into_iter().fold(self, |acc, x| acc.combine(x))
    }

    /// Combines the semigroup value with itself a specified number of times.
    #[inline]
    fn combine_n(self, n: NonZeroUsize) -> Self
    where
        Self: Clone,
    {
        let seed = self.clone();
        let mut acc = self;
        for _ in 1..n.get() {
            acc = acc.combine(seed.clone());
        }
        acc
    }
}

// Default implementation for all types implementing Semigroup
impl<T: Semigroup> SemigroupExt for T {}

// Standard library implementations

impl Semigroup for String {
    #[inline]
    fn combine(self, other: Self) -> Self {
        self + &other
    }
}

impl<T> Semigroup for Vec<T> {
    #[inline]
    fn combine(mut self, other: Self) -> Self {
        self.extend(other);
        self
    }
}

impl<K: Eq + Hash, V: Semigroup> Semigroup for HashMap<K, V> {
    #[inline]
    fn combine(mut self, other: Self) -> Self {
        for (k, v) in other {
            match self.remove(&k) {
                Some(existing) => {
                    self.insert(k, existing.combine(v));
                },
                None => {
                    self.insert(k, v);
                },
            }
        }
        self
    }
}

impl<T: Eq + Hash> Semigroup for HashSet<T> {
    #[inline]
    fn combine(mut self, other: Self) -> Self {
        self.extend(other);
        self
    }
}

impl<K: Ord, V: Semigroup> Semigroup for BTreeMap<K, V> {
    #[inline]
    fn combine(mut self, other: Self) -> Self {
        for (k, v) in other {
            match self.remove(&k) {
                Some(existing) => {
                    self.insert(k, existing.combine(v));
                },
                None => {
                    self.insert(k, v);
                },
            }
        }
        self
    }
}

impl<T: Ord> Semigroup for BTreeSet<T> {
    #[inline]
    fn combine(mut self, other: Self) -> Self {
        self.extend(other);
        self
    }
}

// Tuple implementations

impl<A: Semigroup, B: Semigroup> Semigroup for (A, B) {
    #[inline]
    fn combine(self, other: Self) -> Self {
        (self.0.combine(other.0), self.1.combine(other.1))
    }
}

impl<A: Semigroup, B: Semigroup, C: Semigroup> Semigroup for (A, B, C) {
    #[inline]
    fn combine(self, other: Self) -> Self {
        (
            self.0.combine(other.0),
            self.1.combine(other.1),
            self.2.combine(other.2),
        )
    }
}

impl<A: Semigroup, B: Semigroup, C: Semigroup, D: Semigroup> Semigroup for (A, B, C, D) {
    #[inline]
    fn combine(self, other: Self) -> Self {
        (
            self.0.combine(other.0),
            self.1.combine(other.1),
            self.2.combine(other.2),
            self.3.combine(other.3),
        )
    }
}

// Option implementations

impl<T: Semigroup> Semigroup for Option<T> {
    #[inline]
    fn combine(self, other: Self) -> Self {
        match (self, other) {
            (Some(a), Some(b)) => Some(a.combine(b)),
            (Some(a), None) => Some(a),
            (None, Some(b)) => Some(b),
            (None, None) => None,
        }
    }
}

// Function to combine a sequence of semigroup values
/// Combines a sequence of semigroup values into a single result.
#[inline]
pub fn combine_all_values<T, I>(values: I) -> Option<T>
where
    T: Semigroup,
    I: IntoIterator<Item = T>,
{
    let mut iter = values.into_iter();
    let first = iter.next()?;
    Some(iter.fold(first, |acc, x| acc.combine(x)))
}

// Function to combine a sequence of semigroup values with a provided initial value
/// Combines a sequence of semigroup values, starting with an initial value.
#[inline]
pub fn combine_values<T, I>(initial: T, values: I) -> T
where
    T: Semigroup,
    I: IntoIterator<Item = T>,
{
    values.into_iter().fold(initial, |acc, x| acc.combine(x))
}

#[cfg(test)]
mod tests {
    use super::{Semigroup, SemigroupExt, combine_all_values};
    use crate::datatypes::wrapper::sum::Sum;
    use std::num::NonZeroUsize;

    #[test]
    fn combine_n_repeats_value() {
        let n = NonZeroUsize::new(3).unwrap();
        assert_eq!(Sum(2).combine_n(n), Sum(6));
    }

    #[test]
    fn empty_sequence_is_option() {
        let values: Vec<Sum<i32>> = Vec::new();
        assert_eq!(combine_all_values(values), None);
    }

    #[derive(Clone, Debug, PartialEq, Eq)]
    struct Max(i32);

    impl super::Semigroup for Max {
        fn combine(self, other: Self) -> Self {
            Max(self.0.max(other.0))
        }
    }

    #[test]
    fn custom_semigroup_combines_values() {
        assert_eq!(Max(5).combine(Max(10)), Max(10));
    }

    #[test]
    fn strings_combine_by_concatenation() {
        let hello = "Hello, ".to_owned();
        assert_eq!(hello.combine("world!".to_owned()), "Hello, world!");
    }
}
