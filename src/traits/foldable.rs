use crate::traits::monoid::Monoid;
use crate::fntype::{FnType, FnTrait};
use crate::traits::hkt::{HKT, TypeConstraints};

/// A trait for types that can be "folded" into a summary value.
/// 
/// # Type Parameters
/// * `T` - The type of elements in the foldable structure
/// 
/// # Laws
/// 1. Identity: `fold_left(id) = fold_right(id)`
/// 2. Composition: `fold_left(f).fold_left(g) = fold_left(|acc, x| g(f(acc, x)))`
/// 3. Naturality: `η(fold_left(f)) = η(t).fold_left(f)`
/// 4. Monoid Consistency: `fold_left(M::combine)(M::empty()) = fold_right(M::combine)(M::empty())`
pub trait Foldable<T>: HKT
where
    T: TypeConstraints,
{
    /// Left-associative fold of a structure
    fn fold_left<U, F>(self, init: U, f: F) -> U
    where
        U: TypeConstraints,
        F: FnTrait<(U, T), U>;

    /// Right-associative fold of a structure
    fn fold_right<U, F>(self, init: U, f: F) -> U
    where
        U: TypeConstraints,
        F: FnTrait<(T, U), U>;

    /// Maps elements to a monoid and combines them
    fn fold_map<M, F>(self, f: F) -> M
    where
        M: Monoid<T> + TypeConstraints,
        F: FnTrait<T, M>;

    /// Returns the number of elements in the structure
    #[inline]
    fn length(self) -> usize
    where
        Self: Sized,
    {
        self.fold_left(0, FnType::new(|(acc, _)| acc + 1))
    }

    /// Tests if the structure is empty
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
    T: TypeConstraints,
{
    fn fold_left<U, F>(self, init: U, f: F) -> U
    where
        U: TypeConstraints,
        F: FnTrait<(U, T), U>,
    {
        self.into_iter().fold(init, |acc, x| f.call((acc, x)))
    }

    fn fold_right<U, F>(self, init: U, f: F) -> U
    where
        U: TypeConstraints,
        F: FnTrait<(T, U), U>,
    {
        self.into_iter().rev().fold(init, |acc, x| f.call((x, acc)))
    }

    fn fold_map<M, F>(self, f: F) -> M
    where
        M: Monoid<T> + TypeConstraints,
        F: FnTrait<T, M>,
    {
        self.into_iter()
            .map(|x| f.call(x))
            .fold(M::empty(), |acc, x| acc.combine(x))
    }
}

impl<T> Foldable<T> for Option<T>
where
    T: TypeConstraints,
{
    fn fold_left<U, F>(self, init: U, f: F) -> U
    where
        U: TypeConstraints,
        F: FnTrait<(U, T), U>,
    {
        match self {
            Some(x) => f.call((init, x)),
            None => init,
        }
    }

    fn fold_right<U, F>(self, init: U, f: F) -> U
    where
        U: TypeConstraints,
        F: FnTrait<(T, U), U>,
    {
        match self {
            Some(x) => f.call((x, init)),
            None => init,
        }
    }

    fn fold_map<M, F>(self, f: F) -> M
    where
        M: Monoid<T> + TypeConstraints,
        F: FnTrait<T, M>,
    {
        match self {
            Some(x) => f.call(x),
            None => M::empty(),
        }
    }
}