use crate::category::monoid::Monoid;
use crate::fntype::{SendSyncFn, SendSyncFnTrait};
use crate::category::hkt::ReturnTypeConstraints;

/// A `Foldable` type is a data structure that can be "folded" into a summary value.
/// It provides methods to iterate over the structure and combine its elements.
///
/// # Type Parameters
/// * `T` - The type of elements contained in the foldable structure
///
/// # Laws
/// A Foldable instance must satisfy these laws:
/// 1. Identity: For any foldable structure `t`,
///    `t.fold_left(|x| x) = t.fold_right(|x| x)`
/// 2. Composition: For any foldable structure `t` and functions `f`, `g`,
///    `t.fold_left(f).fold_left(g) = t.fold_left(|acc, x| g(f(acc, x)))`
/// 3. Naturality: For any natural transformation `η: F ~> G`,
///    `η(t.fold_left(f)) = η(t).fold_left(f)`
/// 4. Monoid Consistency: For any foldable structure `t` and monoid `M`,
///    `t.fold_left(M.combine)(M.empty) = t.fold_right(M.combine)(M.empty)`
pub trait Foldable<T>
where
    T: ReturnTypeConstraints,
{
    /// Left-associative fold of a structure.
    ///
    /// Combines elements from left to right using the provided function.
    /// 
    /// # Arguments
    /// * `init` - The initial value to combine the elements with.
    /// * `f` - The function to combine the elements.
    /// 
    /// # Returns
    /// The result of the fold operation.
    fn fold_left<U, F>(self, init: U, f: F) -> U
    where
        U: ReturnTypeConstraints,
        F: SendSyncFnTrait<(U, T), U>;

    /// Right-associative fold of a structure.
    ///
    /// Combines elements from right to left using the provided function.
    /// 
    /// # Arguments
    /// * `init` - The initial value to combine the elements with.
    /// * `f` - The function to combine the elements.
    /// 
    /// # Returns
    /// The result of the fold operation.
    fn fold_right<U, F>(self, init: U, f: F) -> U
    where
        U: ReturnTypeConstraints,
        F: SendSyncFnTrait<(T, U), U>;

    /// Maps elements to a monoid and combines them.
    ///
    /// This is equivalent to mapping each element to a monoid value and then
    /// combining all the results using the monoid's combine operation.
    /// 
    /// # Arguments
    /// * `f` - The function to map elements to a monoid value.
    /// 
    /// # Returns
    /// The combined result.
    fn fold_map<M, F>(self, f: F) -> M
    where
        M: Monoid + ReturnTypeConstraints,
        F: SendSyncFnTrait<T, M>;

    /// Returns the number of elements in the structure.
    /// 
    /// # Returns
    /// The number of elements in the structure.
    #[inline]
    fn length(self) -> usize
    where
        Self: Sized,
    {
        self.fold_left(0, SendSyncFn::new(|(acc, _)| acc + 1))
    }

    /// Tests if the structure is empty.
    /// 
    /// # Returns
    /// `true` if the structure is empty, `false` otherwise.
    #[inline]
    fn is_empty(self) -> bool
    where
        Self: Sized,
    {
        self.length() == 0
    }
}

impl<T> Foldable<T> for Vec<T>
where
    T: ReturnTypeConstraints,
{
    fn fold_left<U, F>(self, init: U, f: F) -> U
    where
        U: ReturnTypeConstraints,
        F: SendSyncFnTrait<(U, T), U>,
    {
        self.into_iter().fold(init, |acc, x| f.call((acc, x)))
    }

    fn fold_right<U, F>(self, init: U, f: F) -> U
    where
        U: ReturnTypeConstraints,
        F: SendSyncFnTrait<(T, U), U>,
    {
        self.into_iter().rev().fold(init, |acc, x| f.call((x, acc)))
    }

    fn fold_map<M, F>(self, f: F) -> M
    where
        M: Monoid + ReturnTypeConstraints,
        F: SendSyncFnTrait<T, M>,
    {
        self.into_iter()
            .map(|x| f.call(x))
            .fold(M::empty(), |acc, x| M::combine(acc, x))
    }
}

impl<T> Foldable<T> for Option<T>
where
    T: ReturnTypeConstraints,
{
    fn fold_left<U, F>(self, init: U, f: F) -> U
    where
        U: ReturnTypeConstraints,
        F: SendSyncFnTrait<(U, T), U>,
    {
        match self {
            Some(x) => f.call((init, x)),
            None => init,
        }
    }

    fn fold_right<U, F>(self, init: U, f: F) -> U
    where
        U: ReturnTypeConstraints,
        F: SendSyncFnTrait<(T, U), U>,
    {
        match self {
            Some(x) => f.call((x, init)),
            None => init,
        }
    }

    fn fold_map<M, F>(self, f: F) -> M
    where
        M: Monoid + ReturnTypeConstraints,
        F: SendSyncFnTrait<T, M>,
    {
        match self {
            Some(x) => f.call(x),
            None => M::empty(),
        }
    }
}