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
/// x.combine(&Monoid::empty()) = x           // Right identity
/// Monoid::empty().combine(&x) = x           // Left identity
/// ```
///
/// Additionally, since `Monoid` extends `Semigroup`, the associativity law must hold:
/// ```text
/// (a.combine(&b)).combine(&c) = a.combine(&b.combine(&c))
/// ```
///
/// # Examples
///
/// ```rust
/// use rustica::traits::monoid::Monoid;
/// use rustica::traits::semigroup::Semigroup;
///
/// let hello = String::from("Hello");
/// assert_eq!(hello.combine(&Monoid::empty()), hello.clone());  // Right identity
/// assert_eq!(String::empty().combine(&hello), hello.clone());  // Left identity
///
/// let numbers = vec![1, 2, 3];
/// assert_eq!(numbers.combine(&Monoid::empty()), numbers.clone());  // Right identity
/// assert_eq!(Vec::empty().combine(&numbers), numbers.clone());  // Left identity
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
    /// // Identity laws
    /// assert_eq!(hello.combine(&empty_string), hello.clone());
    /// assert_eq!(empty_string.combine(&hello), hello);
    /// ```
    fn empty() -> Self;
}

impl<T: Clone> Monoid for Vec<T> {
    fn empty() -> Self {
        Vec::new()
    }
}

impl Monoid for String {
    fn empty() -> Self {
        String::new()
    }
}
