//! Trait implementations for persistent vectors.
//!
//! This module provides implementations of various functional programming traits
//! for [`PersistentVector`], enabling use with the Rustica categorical framework.
//!
//! # Implemented Traits
//!
//! ## Category Theory Traits
//!
//! - [`HKT`]: Higher-kinded type support for generic programming
//! - [`Functor`]: Structure-preserving mapping via `fmap`
//! - [`Foldable`]: Left and right folds over elements
//!
//! ## Algebraic Traits
//!
//! - [`Semigroup`]: Concatenation via `combine`
//! - [`Monoid`]: Empty vector as identity element
//!
//! # Examples
//!
//! ```
//! use rustica::pvec::PersistentVector;
//! use rustica::traits::functor::Functor;
//! use rustica::traits::foldable::Foldable;
//! use rustica::traits::monoid::Monoid;
//! use rustica::traits::semigroup::Semigroup;
//!
//! // Functor: map over elements
//! let vec = PersistentVector::from_slice(&[1, 2, 3]);
//! let doubled: PersistentVector<i32> = vec.clone().fmap(|x| x * 2);
//! assert_eq!(doubled.to_vec(), vec![2, 4, 6]);
//!
//! // Foldable: reduce elements
//! let sum = vec.fold_left(0, |acc, x| acc + x);
//! assert_eq!(sum, 6);
//!
//! // Monoid: empty and combine
//! let empty: PersistentVector<i32> = PersistentVector::empty();
//! let combined = vec.combine(PersistentVector::from_slice(&[4, 5]));
//! assert_eq!(combined.to_vec(), vec![1, 2, 3, 4, 5]);
//! ```

use crate::traits::{
    foldable::Foldable, functor::Functor, hkt::HKT, monoid::Monoid, semigroup::Semigroup,
};

use super::core::PersistentVector;

/// Higher-kinded type implementation for `PersistentVector`.
///
/// This enables `PersistentVector` to be used with generic functions that
/// operate on type constructors (e.g., `F<A>` -> `F<B>`).
impl<T> HKT for PersistentVector<T> {
    type Source = T;
    type Output<U> = PersistentVector<U>;
}

/// Functor implementation for `PersistentVector`.
///
/// Enables structure-preserving transformations over vector elements.
/// The functor laws are satisfied:
/// - Identity: `vec.fmap(|x| x) == vec`
/// - Composition: `vec.fmap(f).fmap(g) == vec.fmap(|x| g(f(x)))`
impl<T: Clone> Functor for PersistentVector<T> {
    #[inline]
    fn fmap<B, F>(self, f: F) -> Self::Output<B>
    where
        F: FnMut(Self::Source) -> B,
    {
        PersistentVector::from_iter(self.into_iter().map(f))
    }
}

/// Foldable implementation for `PersistentVector`.
///
/// Provides left and right folds for reducing vector elements to a single value.
/// Note: This implementation does not require `T: Clone`.
impl<T> Foldable for PersistentVector<T> {
    /// Folds elements from left to right.
    #[inline]
    fn fold_left<U, F>(&self, init: U, mut f: F) -> U
    where
        F: FnMut(U, &Self::Source) -> U,
    {
        let mut acc = init;
        for item in self {
            acc = f(acc, item);
        }
        acc
    }

    /// Folds elements from right to left.
    ///
    /// Uses `DoubleEndedIterator` for efficient reverse traversal.
    #[inline]
    fn fold_right<U, F>(&self, init: U, mut f: F) -> U
    where
        F: FnMut(&Self::Source, U) -> U,
    {
        self.iter().rev().fold(init, |acc, item| f(item, acc))
    }

    #[inline]
    fn length(&self) -> usize {
        self.len()
    }
}

/// Semigroup implementation for `PersistentVector`.
///
/// Concatenation is the associative binary operation:
/// `(a.combine(b)).combine(c) == a.combine(b.combine(c))`
impl<T: Clone> Semigroup for PersistentVector<T> {
    /// Concatenates two vectors.
    #[inline]
    fn combine(self, other: Self) -> Self {
        self.concat(&other)
    }
}

/// Monoid implementation for `PersistentVector`.
///
/// The empty vector serves as the identity element:
/// - `empty().combine(x) == x`
/// - `x.combine(empty()) == x`
impl<T: Clone> Monoid for PersistentVector<T> {
    #[inline]
    fn empty() -> Self {
        PersistentVector::new()
    }
}
