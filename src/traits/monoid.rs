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
//! The `MonoidExt` trait adds extension methods to all types implementing Monoid.
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
/// For any value `x` of type implementing Monoid:
/// ```text
/// x.combine(Monoid::empty()) = x           // Right identity
/// Monoid::empty().combine(x) = x           // Left identity
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
        Some(first) => iter.fold(first, |acc, x| acc.combine_owned(x)),
        None => M::empty(),
    }
}

/// A trait providing extension methods for monoid operations
///
/// This trait is automatically implemented for all types that implement Monoid.
pub trait MonoidExt: Monoid {
    /// Combines `self` with all elements in the provided iterator.
    ///
    /// # Type Parameters
    ///
    /// * `I` - An iterator type yielding values of this monoid type
    ///
    /// # Returns
    ///
    /// The result of combining `self` with all elements in the iterator
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::traits::monoid::{Monoid, MonoidExt};
    /// use rustica::traits::semigroup::Semigroup;
    ///
    /// let base = String::from("Hello");
    /// let others = vec![String::from(", "), String::from("World!")];
    /// let result = base.combine_all(others);
    /// assert_eq!(result, "Hello, World!");
    /// ```
    #[inline]
    fn combine_all<I>(self, others: I) -> Self
    where
        I: IntoIterator<Item = Self>,
    {
        others.into_iter().fold(self, |acc, x| acc.combine_owned(x))
    }

    /// Checks if this monoid value is equal to the identity element.
    ///
    /// # Returns
    ///
    /// `true` if the value equals the identity element, `false` otherwise.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::traits::monoid::{Monoid, MonoidExt};
    ///
    /// let empty_string = String::empty();
    /// assert!(empty_string.is_empty_monoid());
    ///
    /// let non_empty = String::from("Hello");
    /// assert!(!non_empty.is_empty_monoid());
    ///
    /// let empty_vec: Vec<i32> = Vec::empty();
    /// assert!(empty_vec.is_empty_monoid());
    /// ```
    #[inline]
    fn is_empty_monoid(&self) -> bool
    where
        Self: PartialEq,
    {
        self == &Self::empty()
    }
}

impl<T: Monoid> MonoidExt for T {}

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
        result = result.combine_owned(value.clone());
    }
    result
}

/// Combines a slice of monoid values.
///
/// This function takes a slice of monoid values and combines them all,
/// returning the identity element if the slice is empty.
///
/// # Type Parameters
///
/// * `M` - A type implementing Monoid
///
/// # Arguments
///
/// * `values` - A slice of monoid values to combine
///
/// # Returns
///
/// The combined result of all values in the slice or the identity element if the slice is empty
///
/// # Examples
///
/// ```rust
/// use rustica::traits::monoid::{self, Monoid};
/// use rustica::traits::semigroup::Semigroup;
///
/// // Combining strings
/// let strings = [
///     String::from("Hello"),
///     String::from(" "),
///     String::from("World")
/// ];
/// let result = monoid::mconcat(&strings);
/// assert_eq!(result, "Hello World");
///
/// // Empty slice returns the identity element
/// let empty: [String; 0] = [];
/// let result = monoid::mconcat(&empty);
/// assert_eq!(result, String::empty());
/// ```
#[inline]
pub fn mconcat<M>(values: &[M]) -> M
where
    M: Monoid + Clone,
{
    if values.is_empty() {
        return M::empty();
    }

    let mut result = values[0].clone();
    for value in &values[1..] {
        result = result.combine(value);
    }
    result
}

/// Creates a monoid that is combined with itself a specified number of times (raised to a power).
///
/// If the exponent is 0, returns the identity element.
/// If the exponent is 1, returns the value itself.
/// For exponents > 1, combines the value with itself that many times.
///
/// # Type Parameters
///
/// * `M` - A type implementing Monoid
///
/// # Arguments
///
/// * `value` - The base value
/// * `exponent` - The power to raise the value to
///
/// # Returns
///
/// The value combined with itself `exponent` times
///
/// # Examples
///
/// ```rust
/// use rustica::traits::monoid::{self, Monoid};
/// use rustica::traits::semigroup::Semigroup;
///
/// // String power
/// let base = String::from("ab");
/// assert_eq!(monoid::power(base.clone(), 0), String::empty());
/// assert_eq!(monoid::power(base.clone(), 1), "ab");
/// assert_eq!(monoid::power(base.clone(), 3), "ababab");
///
/// // Vec power
/// let nums = vec![1, 2];
/// assert_eq!(monoid::power(nums.clone(), 0), Vec::<i32>::empty());
/// assert_eq!(monoid::power(nums.clone(), 1), vec![1, 2]);
/// assert_eq!(monoid::power(nums.clone(), 3), vec![1, 2, 1, 2, 1, 2]);
/// ```
#[inline]
pub fn power<M>(value: M, exponent: usize) -> M
where
    M: Monoid + Clone,
{
    match exponent {
        0 => M::empty(),
        1 => value,
        _ => repeat(value, exponent),
    }
}
