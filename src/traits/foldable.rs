use crate::traits::monoid::Monoid;
use crate::fntype::{FnType, FnTrait};
use crate::traits::hkt::{HKT, TypeConstraints};

/// A trait for types that can be "folded" into a summary value.
/// 
/// This trait defines methods for reducing a structure into a single value
/// through various folding operations.
/// 
/// # Type Parameters
/// * `T` - The type of elements in the foldable structure
/// 
/// # Laws
/// 
/// A Foldable instance must satisfy these laws:
/// 
/// 1. Identity: For any foldable `t`,
///    `t.fold_left(|acc, x| x, init) == t.fold_right(|x, acc| x, init)`
/// 2. Composition: For any foldable `t` and functions `f`, `g`,
///    `t.fold_left(g, init).fold_left(f, init) == t.fold_left(|acc, x| f(g(acc, x), x), init)`
/// 3. Homomorphism: For any monoid `M` and foldable `t`,
///    `t.fold_map(|x| x) == t.fold_left(M::combine, M::empty())`
/// 4. Interchange: For any foldable `t` and function `f`,
///    `t.fold_right(f, init) == t.fold_left(|acc, x| f(x, acc), init)`
/// 5. Naturality: For any natural transformation `η` and foldable `t`,
///    `η(t.fold_left(f, init)) == η(t).fold_left(f, init)`
/// 6. Monoid Consistency: For any monoid `M` and foldable `t`,
///    `t.fold_left(M::combine, M::empty()) == t.fold_right(M::combine, M::empty())`
pub trait Foldable<T>: HKT
where
    T: TypeConstraints,
{
    /// Performs a left-associative fold of the structure.
    ///
    /// # Type Parameters
    /// * `U` - The type of the accumulated value
    /// * `F` - The type of the folding function
    ///
    /// # Arguments
    /// * `init` - The initial value for the fold
    /// * `f` - The folding function
    ///
    /// # Returns
    /// The final accumulated value
    fn fold_left<U, F>(self, init: U, f: F) -> U
    where
        U: TypeConstraints,
        F: FnTrait<(U, T), U>;

    /// Performs a right-associative fold of the structure.
    ///
    /// # Type Parameters
    /// * `U` - The type of the accumulated value
    /// * `F` - The type of the folding function
    ///
    /// # Arguments
    /// * `init` - The initial value for the fold
    /// * `f` - The folding function
    ///
    /// # Returns
    /// The final accumulated value
    fn fold_right<U, F>(self, init: U, f: F) -> U
    where
        U: TypeConstraints,
        F: FnTrait<(T, U), U>;

    /// Maps elements to a monoid and combines them.
    ///
    /// # Type Parameters
    /// * `M` - The type of the monoid
    /// * `F` - The type of the mapping function
    ///
    /// # Arguments
    /// * `f` - The mapping function
    ///
    /// # Returns
    /// The combined monoid value
    fn fold_map<M, F>(self, f: F) -> M
    where
        M: Monoid<T> + TypeConstraints,
        F: FnTrait<T, M>;

    /// Returns the number of elements in the structure.
    ///
    /// # Returns
    /// The count of elements as a `usize`
    #[inline]
    fn length(self) -> usize
    where
        Self: Sized,
    {
        self.fold_left(0, FnType::new(|(acc, _)| acc + 1))
    }

    /// Tests if the structure is empty.
    ///
    /// # Returns
    /// `true` if the structure contains no elements, `false` otherwise
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