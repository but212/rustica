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
