use crate::traits::hkt::AnyBox;
use crate::traits::traversable::Traversable;

/// A trait for types that can be sequenced.
/// This trait provides a way to sequence a structure of effects into an effect of structure.
///
/// # Examples
///
/// ```rust
/// // Vec<Option<T>> -> Option<Vec<T>>
/// let v: Vec<Option<i32>> = vec![Some(1), Some(2), Some(3)];
/// let sequenced: Option<Vec<i32>> = v.sequence();
/// assert_eq!(sequenced, Some(vec![1, 2, 3]));
///
/// // Vec<Result<T, E>> -> Result<Vec<T>, E>
/// let v: Vec<Result<i32, &str>> = vec![Ok(1), Ok(2), Ok(3)];
/// let sequenced: Result<Vec<i32>, &str> = v.sequence();
/// assert_eq!(sequenced, Ok(vec![1, 2, 3]));
/// ```
///
/// # Laws
///
/// A Sequence instance must satisfy these laws:
///
/// 1. Naturality:
///    `t.map(f).sequence() = f(t.sequence())`
///
/// 2. Identity:
///    `t.sequence().map(identity) = t`
///
/// 3. Composition:
///    `t.map(Compose).sequence() = Compose(t.sequence().map(sequence))`
pub trait Sequence: Traversable {
    /// Evaluates each action in the structure from left to right, and collects the results.
    ///
    /// This method transforms a structure where each element is an effect (like `Vec<Option<T>>`)
    /// into an effect of the structure (like `Option<Vec<T>>`).
    ///
    /// # Returns
    ///
    /// Returns an `AnyBox` containing the sequenced structure.
    fn sequence(&self) -> AnyBox;
}