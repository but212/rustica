//! # Monoid Trait
//!
//! This module provides the [`Monoid`] trait, which extends [`Semigroup`] to add an identity element.
//!
//! A monoid extends a semigroup by providing an identity element that, when combined with any other
//! element, returns that element unchanged. This makes monoids particularly useful for operations
//! like addition (identity: 0), multiplication (identity: 1), and string concatenation (identity: empty string).
//!
//! ## Example
//!
//! ```rust
//! use rustica::traits::monoid::Monoid;
//! use rustica::traits::semigroup::Semigroup;
//!
//! // String monoid under concatenation
//! let s1 = String::from("Hello, ");
//! let s2 = String::from("world!");
//! let s3 = s1.clone().combine_owned(s2.clone());
//! assert_eq!(s3, "Hello, world!");
//!
//! // The empty string is the identity element
//! let empty = String::empty();
//! assert_eq!(s1.clone().combine_owned(empty.clone()), s1.clone());
//! assert_eq!(empty.combine_owned(s2.clone()), s2);
//! ```
//!
//! ## Extension Trait
//!
//! The [`MonoidExt`] trait adds extension methods to all types implementing [`Monoid`].
//!
//! ## TODO: Future Improvements
//!
//! - **Common Implementations**: Add implementations for more standard types (e.g., Option, Result)
//! - **Performance Optimization**: Add benchmarks and optimize performance critical operations
//! - **Parallel Combine**: Implement parallel combination for large collections
//! - **Monoid Product Types**: Support for product and sum types of monoids
//! - **Foldable Integration**: Enhance integration with Foldable trait
//! - **Documentation Examples**: Add more comprehensive examples showing practical use cases
//! - **Laws Testing**: Add property-based testing for monoid laws

use crate::traits::semigroup::Semigroup;

/// A Monoid is a Semigroup with an identity element.
///
/// # Mathematical Definition
///
/// A monoid is an algebraic structure consisting of:
/// - A set `M`
/// - An associative binary operation `combine: M × M → M`
/// - An identity element `empty() ∈ M`
///
/// # Laws
///
/// For any value `x` of type implementing `Monoid`:
/// ```text
/// x.combine(Monoid::empty()) = x           // Right identity
/// Monoid::empty().combine(x) = x           // Left identity
/// ```
///
/// Additionally, since `Monoid` extends `Semigroup`, the associativity law must hold:
/// ```text
/// (a.combine(b)).combine(c) = a.combine(b.combine(c))
/// ```
///
/// # Examples
///
/// ```rust
/// use rustica::traits::monoid::Monoid;
/// use rustica::traits::semigroup::Semigroup;
///
/// // String monoid under concatenation
/// let hello = String::from("Hello");
/// let empty_string = String::empty();
///
/// // Owned value identity laws
/// assert_eq!(hello.clone().combine_owned(empty_string.clone()), hello.clone());  // Right identity
/// assert_eq!(String::empty().combine_owned(hello.clone()), hello.clone());       // Left identity
///
/// // Reference identity laws
/// assert_eq!(hello.combine(&empty_string), hello.clone());           // Right identity
/// assert_eq!(empty_string.combine(&hello), hello);                   // Left identity
///
/// // Vec monoid under concatenation
/// let numbers = vec![1, 2, 3];
/// let empty_vec = Vec::<i32>::empty();
///
/// // Owned value identity laws
/// assert_eq!(numbers.clone().combine_owned(empty_vec.clone()), numbers.clone());  // Right identity
/// assert_eq!(Vec::<i32>::empty().combine_owned(numbers.clone()), numbers.clone()); // Left identity
///
/// // Reference identity laws
/// assert_eq!(numbers.combine(&empty_vec), numbers.clone());            // Right identity
/// assert_eq!(empty_vec.combine(&numbers), numbers);                    // Left identity
/// ```
///
/// # Common Use Cases
///
/// Monoids are particularly useful in scenarios where:
/// - You need to combine elements with a neutral element
/// - You're implementing data structures that require an empty state
/// - You're working with collection types
/// - You need to perform parallel or distributed computations
///
/// Some common monoids include:
/// - Strings under concatenation (empty string as identity)
/// - Lists/Vectors under concatenation (empty list as identity)
/// - Numbers under addition (0 as identity)
/// - Numbers under multiplication (1 as identity)
/// - Booleans under conjunction (true as identity)
/// - Booleans under disjunction (false as identity)
pub trait Monoid: Semigroup {
    /// Returns the identity element of the monoid.
    ///
    /// The identity element is a special value that, when combined with any other value `x`,
    /// yields `x` itself. This must hold true whether the identity is combined from the left
    /// or the right.
    ///
    /// # Returns
    ///
    /// The identity element of the monoid.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::traits::monoid::Monoid;
    /// use rustica::traits::semigroup::Semigroup;
    ///
    /// let empty_string = String::empty();
    /// let hello = String::from("Hello");
    ///
    /// // Owned identity laws
    /// assert_eq!(hello.clone().combine_owned(empty_string.clone()), hello.clone());
    /// assert_eq!(String::empty().combine_owned(hello.clone()), hello.clone());
    ///
    /// // Reference identity laws
    /// assert_eq!(hello.combine(&empty_string), hello.clone());
    /// assert_eq!(empty_string.combine(&hello), hello);
    /// ```
    fn empty() -> Self;
}

// Implement Monoid for Vec
impl<T: Clone> Monoid for Vec<T> {
    fn empty() -> Self {
        Vec::new()
    }
}

// Implement Monoid for String
impl Monoid for String {
    fn empty() -> Self {
        String::new()
    }
}

/// Utility function to combine all monoid values with the identity element
///
/// This function takes an iterator of monoid values and combines them all,
/// returning the identity element if the iterator is empty.
///
/// # Type Parameters
///
/// * `M` - A type implementing `Monoid`
/// * `I` - An iterator type yielding values of type `M`
///
/// # Returns
///
/// The combined result of all values or the identity element if the iterator is empty
///
/// # Examples
///
/// ```rust
/// use rustica::traits::monoid::{self, Monoid};
/// use rustica::traits::semigroup::Semigroup;
///
/// // Combining strings
/// let strings = vec![String::from("Hello"), String::from(" "), String::from("World")];
/// let result = monoid::combine_all(strings);
/// assert_eq!(result, String::from("Hello World"));
///
/// // Empty iterator returns the identity element
/// let empty: Vec<String> = vec![];
/// let result = monoid::combine_all(empty);
/// assert_eq!(result, String::empty());
/// ```
#[inline]
pub fn combine_all<M, I>(values: I) -> M
where
    M: Monoid,
    I: IntoIterator<Item = M>,
{
    let mut iter = values.into_iter();
    match iter.next() {
        Some(first) => iter.fold(first, |acc, x| acc.combine_owned(x)),
        None => M::empty(),
    }
}

/// A trait providing extension methods for monoid operations
///
/// This trait is automatically implemented for all types that implement `Monoid`.
pub trait MonoidExt: Monoid {
    /// Combines multiple monoid values with this value
    ///
    /// # Type Parameters
    ///
    /// * `I` - An iterator type yielding values of type `Self`
    ///
    /// # Parameters
    ///
    /// * `others` - An iterator of monoid values to combine with this value
    ///
    /// # Returns
    ///
    /// The combined result of this value and all other values
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::traits::monoid::{Monoid, MonoidExt};
    /// use rustica::traits::semigroup::Semigroup;
    ///
    /// let base = String::from("Hello");
    /// let others = vec![String::from(" "), String::from("World")];
    /// let result = base.combine_all(others);
    /// assert_eq!(result, String::from("Hello World"));
    /// ```
    fn combine_all<I>(self, others: I) -> Self
    where
        I: IntoIterator<Item = Self>;
}

impl<T: Monoid> MonoidExt for T {
    fn combine_all<I>(self, others: I) -> Self
    where
        I: IntoIterator<Item = Self>,
    {
        others.into_iter().fold(self, |acc, x| acc.combine_owned(x))
    }
}
