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
//! let combined = a.combine(&b);
//! assert_eq!(combined, Sum(15));
//!
//! // Using the Product wrapper for multiplication
//! let x = Product(2);
//! let y = Product(3);
//! let multiplied = x.combine(&y);
//! assert_eq!(multiplied, Product(6));
//! ```
//!
//! ## TODO: Future Improvements
//!
//! - **Additional Implementations**: Add implementations for more numeric types and custom containers
//! - **Performance Optimization**: Add benchmarks for combine operations and optimize hot paths
//! - **Composition Operations**: Add tools for composing and transforming semigroups
//! - **Generic Operators**: Support operator overloading for more ergonomic usage
//! - **SemigroupExt Enhancements**: Add more utility methods to the extension trait
//! - **Advanced Examples**: Add comprehensive examples showing practical applications
//! - **Property Testing**: Implement property-based tests for semigroup laws
//! - **Concurrent Combining**: Support combining values concurrently for large collections

use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};
use std::hash::Hash;

/// A trait for semigroups, which are algebraic structures with an associative binary operation.
/// A semigroup consists of a set together with a binary operation that combines two elements
/// of the set to yield a third element of the set, and the operation must be associative.
///
/// The associative property means that for any elements a, b, and c:
/// `(a combine b) combine c = a combine (b combine c)`
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
/// The trait provides the following methods:
///
/// - `combine`: Combines two values by reference
/// - `combine_owned`: Combines two values by consuming them
/// - `combine_n`: Combines a value with itself n times (by reference)
/// - `combine_n_owned`: Combines a value with itself n times (by consuming the value)
///
/// Additionally, there are default implementations of other useful methods for working with semigroups.
///
/// # Example: Custom implementation
///
/// ```rust
/// use rustica::traits::semigroup::Semigroup;
///
/// // A simple wrapper type for demonstrating Semigroup
/// #[derive(Debug, Clone, PartialEq, Eq)]
/// struct Max(i32);
///
/// impl Semigroup for Max {
///     fn combine(&self, other: &Self) -> Self {
///         Max(std::cmp::max(self.0, other.0))
///     }
///     
///     fn combine_owned(self, other: Self) -> Self {
///         Max(std::cmp::max(self.0, other.0))
///     }
/// }
///
/// // Using our custom Semigroup implementation
/// let a = Max(5);
/// let b = Max(10);
/// let c = a.combine(&b);
/// assert_eq!(c, Max(10)); // Max takes the maximum value
/// ```
pub trait Semigroup: Sized {
    /// Combines two values by reference to produce a new value.
    ///
    /// This is the primary operation of the Semigroup trait. It takes references to two values
    /// and produces a new value that is their combination.
    ///
    /// # Parameters
    ///
    /// * `other`: A reference to another value of the same type
    ///
    /// # Returns
    ///
    /// A new value of the same type, which is the result of combining `self` and `other`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::traits::semigroup::Semigroup;
    ///
    /// // Combining strings (concatenation is a semigroup operation)
    /// let hello = "Hello, ".to_string();
    /// let world = "world!".to_string();
    /// let message = hello.combine(&world);
    /// assert_eq!(message, "Hello, world!");
    /// ```
    fn combine(&self, other: &Self) -> Self;

    /// Combines two values by consuming them to produce a new value.
    ///
    /// This method is an ownership-based variant of `combine` that consumes both values
    /// instead of operating on references. This can be more efficient when the original
    /// values are no longer needed.
    ///
    /// # Parameters
    ///
    /// * `other`: Another value of the same type, which will be consumed
    ///
    /// # Returns
    ///
    /// A new value of the same type, which is the result of combining `self` and `other`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::traits::semigroup::Semigroup;
    ///
    /// let a = vec![1, 2, 3];
    /// let b = vec![4, 5, 6];
    /// let combined = a.combine_owned(b); // Consumes both vectors
    /// assert_eq!(combined, vec![1, 2, 3, 4, 5, 6]);
    /// ```
    fn combine_owned(self, other: Self) -> Self;
}

/// Adapter struct to provide extension methods for semigroups.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SemigroupExtAdapter<T>(T);

/// Extension methods for semigroups, providing additional functionality.
pub trait SemigroupExt: Semigroup {
    /// Combines `self` with all the values in an iterator.
    ///
    /// This method applies the semigroup operation to combine `self` with each value
    /// in the iterator in sequence.
    ///
    /// # Parameters
    ///
    /// * `others` - An iterator yielding values to combine with `self`.
    ///
    /// # Returns
    ///
    /// The result of combining `self` with all the elements in `others`
    fn combine_all<I>(self, others: I) -> Self
    where
        I: IntoIterator<Item = Self>;

    /// Extension methods for semigroups.
    ///
    /// # Examples
    ///
    /// Combining multiple values at once:
    /// ```rust
    /// use rustica::traits::semigroup::{Semigroup, SemigroupExt};
    ///
    /// let a = vec![1, 2];
    /// let b = vec![3, 4];
    /// let c = vec![5, 6];
    ///
    /// let result = a.clone().combine_all_owned(vec![b.clone(), c.clone()]);
    /// assert_eq!(result, vec![1, 2, 3, 4, 5, 6]);
    /// ```
    fn combine_all_owned<I>(self, others: I) -> Self
    where
        I: IntoIterator<Item = Self>;

    /// Combines the semigroup value with itself a specified number of times.
    ///
    /// # Parameters
    ///
    /// * `n` - The number of times to combine `self` with itself.
    ///   If `n` is 0, returns `self`.
    ///   If `n` is negative, the behavior is undefined and may panic.
    ///
    /// # Returns
    ///
    /// The result of combining `self` with itself `n` times.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::traits::semigroup::{Semigroup, SemigroupExt};
    ///
    /// // Create a wrapper type for i32 to avoid orphan rule violations
    /// #[derive(Debug, Clone, PartialEq, Eq)]
    /// struct AddInt(i32);
    ///
    /// // Implement Semigroup for our wrapper type
    /// impl Semigroup for AddInt {
    ///     fn combine(&self, other: &Self) -> Self {
    ///         AddInt(self.0 + other.0)
    ///     }
    ///     
    ///     fn combine_owned(self, other: Self) -> Self {
    ///         AddInt(self.0 + other.0)
    ///     }
    /// }
    ///
    /// // Using combine_n
    /// let x = AddInt(5);
    /// assert_eq!(x.combine_n(&3), AddInt(15));  // 5 + 5 + 5 = 15
    /// assert_eq!(x.combine_n(&0), AddInt(5));   // Identity
    /// ```
    fn combine_n(&self, n: &usize) -> Self
    where
        Self: Clone;

    /// Combines the semigroup value with itself a specified number of times, by reference.
    ///
    /// # Parameters
    ///
    /// * `n` - The number of times to combine `self` with itself.
    ///   If `n` is 0, returns a clone of `self`.
    ///   If `n` is negative, the behavior is undefined and may panic.
    ///
    /// # Returns
    ///
    /// The result of combining `self` with itself `n` times.
    fn combine_n_owned(self, n: usize) -> Self
    where
        Self: Clone;
}

// Default implementation for all types implementing Semigroup
impl<T: Semigroup> SemigroupExt for T {
    #[inline]
    fn combine_all<I>(self, others: I) -> Self
    where
        I: IntoIterator<Item = Self>,
    {
        let mut result = self;
        for other in others {
            result = result.combine_owned(other);
        }
        result
    }

    #[inline]
    fn combine_all_owned<I>(self, others: I) -> Self
    where
        I: IntoIterator<Item = Self>,
    {
        let mut result = self;
        for other in others {
            result = result.combine_owned(other);
        }
        result
    }

    #[inline]
    fn combine_n_owned(self, n: usize) -> Self
    where
        Self: Clone,
    {
        if n == 0 {
            return self;
        }

        let mut result = self.clone();
        for _ in 1..n {
            result = result.combine_owned(self.clone());
        }
        result
    }

    #[inline]
    fn combine_n(&self, n: &usize) -> Self
    where
        Self: Clone,
    {
        if *n == 0 {
            return self.clone();
        }

        let mut result = self.clone();
        for _ in 1..*n {
            result = result.combine(self);
        }
        result
    }
}

// Implement extension methods
impl<T: Semigroup> SemigroupExtAdapter<T> {
    /// Combines `self` with all the values in an iterator.
    pub fn combine_all<I>(self, others: I) -> T
    where
        I: IntoIterator<Item = T>,
    {
        self.0.combine_all(others)
    }

    /// Combines the semigroup value with itself a specified number of times.
    pub fn combine_n_owned(self, n: usize) -> T
    where
        T: Clone,
    {
        self.0.combine_n_owned(n)
    }

    /// Combines the semigroup value with itself a specified number of times by reference.
    pub fn combine_n(&self, n: &usize) -> T
    where
        T: Clone,
    {
        self.0.combine_n(n)
    }
}

// Standard library implementations

impl Semigroup for String {
    #[inline]
    fn combine(&self, other: &Self) -> Self {
        self.clone() + other
    }

    #[inline]
    fn combine_owned(self, other: Self) -> Self {
        self + &other
    }
}

impl<T: Clone> Semigroup for Vec<T> {
    #[inline]
    fn combine(&self, other: &Self) -> Self {
        let mut result = self.clone();
        result.extend(other.iter().cloned());
        result
    }

    #[inline]
    fn combine_owned(self, other: Self) -> Self {
        let mut result = self;
        result.extend(other);
        result
    }
}

impl<K: Eq + Hash + Clone, V: Semigroup + Clone> Semigroup for HashMap<K, V> {
    #[inline]
    fn combine(&self, other: &Self) -> Self {
        let mut result = self.clone();
        for (k, v) in other {
            result.entry(k.clone()).and_modify(|e| *e = e.combine(v)).or_insert(v.clone());
        }
        result
    }

    #[inline]
    fn combine_owned(self, other: Self) -> Self {
        let mut result = self;
        for (k, v) in other {
            match result.get_mut(&k) {
                Some(existing) => {
                    let combined = existing.clone().combine_owned(v);
                    *existing = combined;
                },
                None => {
                    result.insert(k, v);
                },
            }
        }
        result
    }
}

impl<T: Eq + Hash + Clone> Semigroup for HashSet<T> {
    #[inline]
    fn combine(&self, other: &Self) -> Self {
        let mut result = self.clone();
        result.extend(other.iter().cloned());
        result
    }

    fn combine_owned(self, other: Self) -> Self {
        let mut result = self;
        result.extend(other);
        result
    }
}

impl<K: Ord + Clone, V: Semigroup + Clone> Semigroup for BTreeMap<K, V> {
    #[inline]
    fn combine(&self, other: &Self) -> Self {
        let mut result = self.clone();
        for (k, v) in other {
            result.entry(k.clone()).and_modify(|e| *e = e.combine(v)).or_insert(v.clone());
        }
        result
    }

    #[inline]
    fn combine_owned(self, other: Self) -> Self {
        let mut result = self;
        for (k, v) in other {
            match result.get_mut(&k) {
                Some(existing) => {
                    let combined = existing.clone().combine_owned(v);
                    *existing = combined;
                },
                None => {
                    result.insert(k, v);
                },
            }
        }
        result
    }
}

impl<T: Ord + Clone> Semigroup for BTreeSet<T> {
    #[inline]
    fn combine(&self, other: &Self) -> Self {
        let mut result = self.clone();
        result.extend(other.iter().cloned());
        result
    }

    #[inline]
    fn combine_owned(self, other: Self) -> Self {
        let mut result = self;
        result.extend(other);
        result
    }
}

// Tuple implementations

impl<A: Semigroup, B: Semigroup> Semigroup for (A, B) {
    #[inline]
    fn combine(&self, other: &Self) -> Self {
        (self.0.combine(&other.0), self.1.combine(&other.1))
    }

    #[inline]
    fn combine_owned(self, other: Self) -> Self {
        (self.0.combine_owned(other.0), self.1.combine_owned(other.1))
    }
}

impl<A: Semigroup, B: Semigroup, C: Semigroup> Semigroup for (A, B, C) {
    #[inline]
    fn combine(&self, other: &Self) -> Self {
        (
            self.0.combine(&other.0),
            self.1.combine(&other.1),
            self.2.combine(&other.2),
        )
    }

    #[inline]
    fn combine_owned(self, other: Self) -> Self {
        (
            self.0.combine_owned(other.0),
            self.1.combine_owned(other.1),
            self.2.combine_owned(other.2),
        )
    }
}

impl<A: Semigroup, B: Semigroup, C: Semigroup, D: Semigroup> Semigroup for (A, B, C, D) {
    #[inline]
    fn combine(&self, other: &Self) -> Self {
        (
            self.0.combine(&other.0),
            self.1.combine(&other.1),
            self.2.combine(&other.2),
            self.3.combine(&other.3),
        )
    }

    #[inline]
    fn combine_owned(self, other: Self) -> Self {
        (
            self.0.combine_owned(other.0),
            self.1.combine_owned(other.1),
            self.2.combine_owned(other.2),
            self.3.combine_owned(other.3),
        )
    }
}

// Option implementations

impl<T: Semigroup + Clone> Semigroup for Option<T> {
    #[inline]
    fn combine(&self, other: &Self) -> Self {
        match (self, other) {
            (Some(a), Some(b)) => Some(a.combine(b)),
            (Some(a), None) => Some(a.clone()),
            (None, Some(b)) => Some(b.clone()),
            (None, None) => None,
        }
    }

    #[inline]
    fn combine_owned(self, other: Self) -> Self {
        match (self, other) {
            (Some(a), Some(b)) => Some(a.combine_owned(b)),
            (Some(a), None) => Some(a),
            (None, Some(b)) => Some(b),
            (None, None) => None,
        }
    }
}

// Function to combine a sequence of semigroup values
/// Combines a sequence of semigroup values into a single result.
///
/// # Type Parameters
///
/// * `T` - A type that implements `Semigroup`
/// * `I` - An iterator type that yields values of type `T`
///
/// # Returns
///
/// * `Some(result)` - If the iterator is non-empty, where `result` is the combination of all values
/// * `None` - If the iterator is empty
///
/// # Examples
///
/// ```rust
/// use rustica::traits::semigroup::{self, Semigroup};
/// use rustica::datatypes::wrapper::sum::Sum;
///
/// // Define a semigroup for integers under addition
/// let values = vec![Sum(1), Sum(2), Sum(3), Sum(4)];
/// let result = semigroup::combine_all_values(values);
/// assert_eq!(result, Some(Sum(10)));  // 1 + 2 + 3 + 4 = 10
///
/// // Empty list returns None
/// let empty: Vec<Sum<i32>> = vec![];
/// let result = semigroup::combine_all_values(empty);
/// assert_eq!(result, None);
/// ```
#[inline]
pub fn combine_all_values<T, I>(values: I) -> Option<T>
where
    T: Semigroup,
    I: IntoIterator<Item = T>,
{
    let mut iter = values.into_iter();
    let first = iter.next()?;
    Some(iter.fold(first, |acc, x| acc.combine_owned(x)))
}

// Function to combine a sequence of semigroup values with a provided initial value
/// Combines a sequence of semigroup values, starting with an initial value.
///
/// # Type Parameters
///
/// * `T` - A type that implements `Semigroup`
/// * `I` - An iterator type that yields values of type `T`
///
/// # Parameters
///
/// * `initial` - The initial value to start combining with
/// * `values` - An iterator of values to combine with the initial value
///
/// # Returns
///
/// The result of combining the initial value with all values in the iterator
///
/// # Examples
///
/// ```rust
/// use rustica::traits::semigroup::{self, Semigroup};
/// use rustica::datatypes::wrapper::product::Product;
///
/// let initial = Product(2);
/// let values = vec![Product(3), Product(4)];
/// let result = semigroup::combine_values(initial, values);
/// assert_eq!(result, Product(24));  // 2 * 3 * 4 = 24
/// ```
#[inline]
pub fn combine_values<T, I>(initial: T, values: I) -> T
where
    T: Semigroup,
    I: IntoIterator<Item = T>,
{
    values.into_iter().fold(initial, |acc, x| acc.combine_owned(x))
}
