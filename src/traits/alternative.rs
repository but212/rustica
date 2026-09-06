//! # Alternative Functors
//!
//! The `Alternative` trait represents applicative functors that also have a monoid structure.
//! It extends the `Applicative` trait with operations for choice and failure.
//!
//! ## Core Operations
//!
//! - `empty_alt`: Provides an identity element (representing failure)
//! - `alt`: Combines two alternatives (representing choice)
//!
//! ## Laws
//!
//! For a valid Alternative implementation, the following laws must hold:
//!
//! 1. Left identity: `empty_alt().alt(x) == x`
//! 2. Right identity: `x.alt(empty_alt()) == x`
//! 3. Associativity: `a.alt(b).alt(c) == a.alt(b.alt(c))`
//! 4. Distributivity (applicative): applying a function in context should distribute over choice.
//! 5. Annihilation (applicative): applying a failed function context should yield failure.
//!
//! ## Common Use Cases
//!
//! - Representing failure and recovery in computations
//! - Parsing with multiple possible alternatives
//! - Collecting multiple possible results
//!
//! ## Example
//!
//! ```rust
//! use rustica::traits::alternative::Alternative;
//!
//! // Vec as Alternative
//! let a = vec![1, 2];
//! let b = vec![3, 4];
//! let empty: Vec<i32> = <Vec<i32> as Alternative>::empty_alt::<i32>();
//!
//! // alt combines alternatives
//! assert_eq!(a.alt(b), vec![1, 2]);
//! assert_eq!(empty.alt(vec![3, 4]), vec![3, 4]);
//!
//! // guard for conditional inclusion
//! assert_eq!(Vec::<i32>::guard(true), vec![()]);
//! assert_eq!(Vec::<i32>::guard(false), Vec::<()>::new());
//!
//! // many for repetition (Vec only)
//! let xs = vec![42];
//! assert_eq!(xs.many(), vec![vec![42]]);
//! ```
use crate::traits::applicative::Applicative;

/// A trait for types that provide an alternative computation strategy.
///
/// `Alternative` extends `Applicative` with operations for choice and failure.
/// It represents applicative functors that also have a monoid structure.
///
pub trait Alternative: Applicative {
    /// Returns an empty value representing failure for the alternative computation.
    ///
    /// This is the identity element for the `alt` operation.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::traits::alternative::Alternative;
    ///
    /// assert_eq!(Option::<i32>::empty_alt::<i32>(), None);
    /// assert_eq!(Vec::<i32>::empty_alt::<i32>(), Vec::new());
    /// ```
    fn empty_alt<T>() -> Self::Output<T>;

    /// Combines two alternatives, choosing the first success.
    ///
    /// If `self` succeeds, it is returned. Otherwise, `other` is used.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::traits::alternative::Alternative;
    ///
    /// let a = Some(1);
    /// let b = Some(2);
    /// let c: Option<i32> = None;
    ///
    /// assert_eq!(a.alt(b), Some(1));
    /// assert_eq!(c.alt(Some(2)), Some(2));
    /// assert_eq!(Option::<i32>::None.alt(None), None);
    /// ```
    fn alt(self, other: Self) -> Self;

    /// Returns a value if the condition is true, otherwise returns the empty value.
    ///
    /// # Laws
    ///
    /// - Identity: `Alternative::guard(true)` is not empty, `Alternative::guard(false)` is empty.
    ///
    /// # Examples
    /// ```rust
    /// use rustica::traits::alternative::Alternative;
    /// assert_eq!(Vec::<i32>::guard(true), vec![()]);
    /// assert_eq!(Vec::<i32>::guard(false), Vec::<()>::new());
    /// assert_eq!(Option::<i32>::guard(true), Some(()));
    /// assert_eq!(Option::<i32>::guard(false), None);
    /// ```
    fn guard(condition: bool) -> Self::Output<()>;

    /// Returns a collected result when this alternative is successful.
    ///
    /// Note: in this crate's default implementations, this is a lightweight helper:
    ///
    /// - For `Option<T>`: `Some(x).many() == Some(vec![x])`, `None.many() == None`
    /// - For `Vec<T>`: non-empty `xs.many() == vec![xs]`, empty `Vec::new().many() == Vec::new()`
    ///
    /// # Laws
    ///
    /// - If `self` is empty, the result is empty.
    /// - If `self` is non-empty, the result is non-empty.
    ///
    /// # Examples
    /// ```rust
    /// use rustica::traits::alternative::Alternative;
    /// let empty: Vec<i32> = Vec::new();
    /// assert_eq!(empty.many(), Vec::<Vec<i32>>::new());
    /// let xs = vec![1,2];
    /// assert_eq!(xs.many(), vec![vec![1,2]]);
    ///
    /// let none: Option<i32> = None;
    /// let some = Some(42);
    /// assert_eq!(none.many(), None);
    /// assert_eq!(some.many(), Some(vec![42]));
    /// ```
    fn many(self) -> Self::Output<Vec<Self::Source>>;
}

impl<T> Alternative for Option<T> {
    fn empty_alt<U>() -> Self::Output<U> {
        None
    }

    fn alt(self, other: Self) -> Self {
        self.or(other)
    }

    fn guard(condition: bool) -> Self::Output<()> {
        condition.then_some(())
    }

    fn many(self) -> Self::Output<Vec<Self::Source>> {
        self.map(|value| vec![value])
    }
}

impl<T> Alternative for Vec<T> {
    fn empty_alt<U>() -> Self::Output<U> {
        Vec::new()
    }

    fn alt(self, other: Self) -> Self {
        if self.is_empty() { other } else { self }
    }

    fn guard(condition: bool) -> Self::Output<()> {
        if condition { vec![()] } else { Vec::new() }
    }

    fn many(self) -> Self::Output<Vec<Self::Source>> {
        if self.is_empty() {
            Vec::new()
        } else {
            vec![self]
        }
    }
}

#[cfg(test)]
mod unit_tests {
    use super::Alternative;

    #[derive(Debug, PartialEq)]
    struct MoveOnly(i32);

    #[test]
    fn option_and_vec_choose_the_first_available_value() {
        let none: Option<i32> = None;
        let some = Some(42);
        assert_eq!(Alternative::alt(none, some), Some(42));
        assert_eq!(Option::<i32>::guard(true), Some(()));
        assert_eq!(Option::<i32>::guard(false), None);

        let first = vec![1];
        let second = vec![2];
        assert_eq!(Vec::<i32>::empty_alt().alt(first.clone()), first);
        assert_eq!(first.alt(second), vec![1]);
    }

    #[test]
    fn alternative_supports_move_only_types() {
        let none: Option<MoveOnly> = None;
        let some = Some(MoveOnly(42));
        assert_eq!(none.alt(some), Some(MoveOnly(42)));

        let v_empty: Vec<MoveOnly> = Vec::new();
        let v_items = vec![MoveOnly(1)];
        assert_eq!(v_empty.alt(v_items), vec![MoveOnly(1)]);
    }
}
