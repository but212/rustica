//! # Monoid Trait
//!
//! This module provides the Monoid trait, which extends `Semigroup` to add an identity element.
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
//! let s3 = s1.clone().combine(s2.clone());
//! assert_eq!(s3, "Hello, world!");
//!
//! // The empty string is the identity element
//! let empty = String::empty();
//! assert_eq!(s1.clone().combine(empty.clone()), s1.clone());
//! assert_eq!(empty.combine(s2.clone()), s2);
//! ```

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
/// For any value `x` of type implementing Monoid:
/// ```text
/// x.combine(Self::empty()) = x           // Right identity
/// Self::empty().combine(x) = x           // Left identity
/// ```
///
/// Additionally, since Monoid extends `Semigroup`, the associativity law must hold:
/// ```text
/// (a.combine(b)).combine(c) = a.combine(b.combine(c))
/// ```
///
/// # Examples
///
/// ```rust
/// use rustica::traits::semigroup::Semigroup;
///
/// let hello = String::from("Hello");
/// let world = String::from(", world!");
/// assert_eq!(hello.combine(world), "Hello, world!");
/// ```
///
/// The complete identity and associativity checks are maintained in
/// `tests/traits/merging_laws.rs`.
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
    /// // Identity laws
    /// assert_eq!(hello.clone().combine(empty_string.clone()), hello.clone());
    /// assert_eq!(String::empty().combine(hello.clone()), hello.clone());
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
/// * `M` - A type implementing Monoid
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
        Some(first) => iter.fold(first, |acc, x| acc.combine(x)),
        None => M::empty(),
    }
}

/// Creates a monoid by repeating an element a specified number of times.
///
/// This function creates a new monoid value by combining n copies of the provided value.
/// If n is 0, it returns the identity element.
/// If n is 1, returns the value itself.
/// For exponents > 1, combines the value with itself that many times.
///
/// # Type Parameters
///
/// * `M` - A type implementing Monoid
///
/// # Arguments
///
/// * `value` - The value to repeat
/// * `n` - Number of times to repeat the value
///
/// # Returns
///
/// A new monoid value consisting of n copies of the input combined together
///
/// # Examples
///
/// ```rust
/// use rustica::traits::monoid::{self, Monoid};
/// use rustica::traits::semigroup::Semigroup;
///
/// // Repeating a string
/// let hello = String::from("Hello");
/// let repeated = monoid::repeat(hello, 3);
/// assert_eq!(repeated, "HelloHelloHello");
///
/// // Zero repetitions returns the identity
/// let zero_repeat = monoid::repeat(String::from("World"), 0);
/// assert_eq!(zero_repeat, String::empty());
/// ```
#[inline]
pub fn repeat<M>(value: M, n: usize) -> M
where
    M: Monoid + Clone,
{
    if n == 0 {
        return M::empty();
    }

    // Special case optimization for n == 1
    if n == 1 {
        return value;
    }

    let mut result = value.clone();
    for _ in 1..n {
        result = result.combine(value.clone());
    }
    result
}
