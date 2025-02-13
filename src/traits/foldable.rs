use crate::traits::monoid::Monoid;
use crate::fntype::{FnType, FnTrait};
use crate::traits::hkt::TypeConstraints;

/// A `Foldable` type is a data structure that can be "folded" into a summary value.
///
/// # Laws
/// 1. Identity: `t.fold_left(|x| x) = t.fold_right(|x| x)`
/// 2. Composition: `t.fold_left(f).fold_left(g) = t.fold_left(|acc, x| g(f(acc, x)))`
/// 3. Naturality: `η(t.fold_left(f)) = η(t).fold_left(f)`
/// 4. Monoid Consistency: `t.fold_left(M.combine)(M.empty) = t.fold_right(M.combine)(M.empty)`
pub trait Foldable<T: TypeConstraints> {

    /// Left-associative fold of a structure.
    fn fold_left<U: TypeConstraints, F: FnTrait<(U, T), U>>(self, init: U, f: F) -> U;

    /// Right-associative fold of a structure.
    fn fold_right<U: TypeConstraints, F: FnTrait<(T, U), U>>(self, init: U, f: F) -> U;

    /// Maps elements to a monoid and combines them.
    fn fold_map<M: Monoid + TypeConstraints, F: FnTrait<T, M>>(self, f: F) -> M;

    /// Returns the number of elements in the structure.
    #[inline]
    fn length(self) -> usize where Self: Sized {
        self.fold_left(0, FnType::new(|(acc, _)| acc + 1))
    }

    /// Tests if the structure is empty.
    #[inline]
    fn is_empty(self) -> bool where Self: Sized {
        self.length() == 0
    }
}

impl<T: TypeConstraints> Foldable<T> for Vec<T> {
    fn fold_left<U: TypeConstraints, F: FnTrait<(U, T), U>>(self, init: U, f: F) -> U {
        self.into_iter().fold(init, |acc, x| f.call((acc, x)))
    }

    fn fold_right<U: TypeConstraints, F: FnTrait<(T, U), U>>(self, init: U, f: F) -> U {
        self.into_iter().rev().fold(init, |acc, x| f.call((x, acc)))
    }

    fn fold_map<M: Monoid + TypeConstraints, F: FnTrait<T, M>>(self, f: F) -> M {
        self.into_iter()
            .map(|x| f.call(x))
            .fold(M::empty(), |acc, x| M::combine(acc, x))
    }
}

impl<T: TypeConstraints> Foldable<T> for Option<T> {
    fn fold_left<U: TypeConstraints, F: FnTrait<(U, T), U>>(self, init: U, f: F) -> U {
        match self {
            Some(x) => f.call((init, x)),
            None => init,
        }
    }

    fn fold_right<U: TypeConstraints, F: FnTrait<(T, U), U>>(self, init: U, f: F) -> U {
        match self {
            Some(x) => f.call((x, init)),
            None => init,
        }
    }

    fn fold_map<M: Monoid + TypeConstraints, F: FnTrait<T, M>>(self, f: F) -> M {
        match self {
            Some(x) => f.call(x),
            None => M::empty(),
        }
    }
}