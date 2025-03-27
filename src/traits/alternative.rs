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
//! 4. Distributivity: `f.ap(a.alt(b)) == f.ap(a).alt(f.ap(b))`
//! 5. Annihilation: `empty_alt().ap(a) == empty_alt()`
//!
//! ## Common Use Cases
//!
//! - Representing failure and recovery in computations
//! - Parsing with multiple possible alternatives
//! - Collecting multiple possible results

use crate::traits::applicative::Applicative;

/// A trait for types that provide an alternative computation strategy.
///
/// `Alternative` extends `Applicative` with operations for choice and failure.
pub trait Alternative: Applicative {
    /// Returns an empty value representing failure for the alternative computation.
    fn empty_alt<T>() -> Self::Output<T>;

    /// Combines two alternatives, choosing the first success.
    ///
    /// If `self` succeeds, it is returned. Otherwise, `other` is used.
    fn alt(&self, other: &Self) -> Self
    where
        Self: Sized + Clone;

    /// Creates a conditional computation.
    ///
    /// Returns an empty alternative if the condition is false, or a successful
    /// unit value if true.
    fn guard(condition: bool) -> Self::Output<()>;

    /// Applies the alternative computation zero or more times.
    ///
    /// Returns a vector of all successful results.
    fn many(&self) -> Self::Output<Vec<Self::Source>>
    where
        Self::Source: Clone;
}

impl<T> Alternative for Option<T>
where
    T: Clone,
{
    fn empty_alt<U>() -> Self::Output<U> {
        None
    }

    fn alt(&self, other: &Self) -> Self {
        self.clone().or_else(|| other.clone())
    }

    fn guard(condition: bool) -> Self::Output<()> {
        condition.then_some(())
    }

    fn many(&self) -> Self::Output<Vec<Self::Source>>
    where
        Self::Source: Clone,
    {
        self.as_ref().map(|value| vec![value.clone()])
    }
}

impl<T> Alternative for Vec<T>
where
    T: Clone,
{
    fn empty_alt<U>() -> Self::Output<U> {
        Vec::new()
    }

    fn alt(&self, other: &Self) -> Self {
        if self.is_empty() {
            other.clone()
        } else {
            self.clone()
        }
    }

    fn guard(condition: bool) -> Self::Output<()> {
        if condition {
            vec![()]
        } else {
            Vec::new()
        }
    }

    fn many(&self) -> Self::Output<Vec<Self::Source>>
    where
        Self::Source: Clone,
    {
        if self.is_empty() {
            Vec::new()
        } else {
            vec![self.clone()]
        }
    }
}
