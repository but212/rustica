use std::collections::HashMap;
use std::hash::Hash;

/// A trait for semigroups, which are algebraic structures with an associative binary operation.
/// A semigroup consists of a set together with a binary operation that combines two elements
/// of the set to produce another element of the set.
///
/// # Mathematical Definition
///
/// A semigroup is a pair (S, •) where:
/// - S is a non-empty set
/// - • is a binary operation S × S → S
///
/// # Laws
///
/// 1. Associativity:
///    ```text
///    (a • b) • c = a • (b • c)
///    ```
///    For all a, b, c in S
///
/// 2. Closure:
///    ```text
///    a • b ∈ S
///    ```
///    For all a, b in S
///
/// # Examples
///
/// ```rust
/// use rustica::traits::semigroup::Semigroup;
///
/// // String concatenation forms a semigroup
/// let hello = String::from("Hello, ");
/// let world = String::from("World!");
/// assert_eq!(hello.combine(&world), "Hello, World!");
///
/// // Vector concatenation forms a semigroup
/// let v1 = vec![1, 2];
/// let v2 = vec![3, 4];
/// assert_eq!(v1.combine(&v2), vec![1, 2, 3, 4]);
///
/// // Numbers under addition form a semigroup
/// #[derive(Debug, PartialEq)]
/// struct Sum(i32);
///
/// impl Semigroup for Sum {
///     fn combine(&self, other: &Self) -> Self {
///         Sum(self.0 + other.0)
///     }
/// }
///
/// let a = Sum(5);
/// let b = Sum(3);
/// let c = Sum(2);
///
/// // Demonstrating associativity
/// assert_eq!(a.combine(&b.combine(&c)), (a.combine(&b)).combine(&c));
/// ```
///
/// # Common Use Cases
///
/// 1. **Collection Operations**
///    - Concatenating strings or lists
///    - Merging maps or sets
///    - Combining sequences
///
/// 2. **Numeric Operations**
///    - Addition of numbers
///    - Multiplication of numbers
///    - Finding minimum or maximum values
///
/// 3. **Data Aggregation**
///    - Combining partial results
///    - Merging statistics
///    - Accumulating values
///
/// 4. **Parallel Processing**
///    - Combining partial results from parallel computations
///    - Reducing distributed data
///
/// # Type Parameters
///
/// The Semigroup trait is implemented for various types that support an associative
/// binary operation. Common implementations include:
///
/// - `String`: Concatenation
/// - `Vec<T>`: List concatenation
/// - `HashMap<K, V>`: Map union with value combination
/// - Numeric types wrapped in newtype patterns
pub trait Semigroup {
    /// Combines two values of the same type using an associative operation.
    ///
    /// # Arguments
    ///
    /// * `other` - Another value of the same type to combine with `self`
    ///
    /// # Returns
    ///
    /// The result of combining `self` with `other`
    fn combine(&self, other: &Self) -> Self;
}

impl Semigroup for String {
    fn combine(&self, other: &Self) -> Self {
        self.clone() + other
    }
}

impl<T: Clone> Semigroup for Vec<T> {
    fn combine(&self, other: &Self) -> Self {
        let mut result = self.clone();
        result.extend(other.iter().cloned());
        result
    }
}

impl<K: Eq + Hash + Clone, V: Semigroup + Clone> Semigroup for HashMap<K, V> {
    fn combine(&self, other: &Self) -> Self {
        let mut result = self.clone();
        for (k, v) in other {
            result
                .entry(k.clone())
                .and_modify(|e| *e = e.combine(v))
                .or_insert(v.clone());
        }
        result
    }
}

impl<A: Semigroup, B: Semigroup> Semigroup for (A, B) {
    fn combine(&self, other: &Self) -> Self {
        (self.0.combine(&other.0), self.1.combine(&other.1))
    }
}

impl<A: Semigroup, B: Semigroup, C: Semigroup> Semigroup for (A, B, C) {
    fn combine(&self, other: &Self) -> Self {
        (
            self.0.combine(&other.0),
            self.1.combine(&other.1),
            self.2.combine(&other.2),
        )
    }
}