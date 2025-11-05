//! Trait implementations for persistent vectors.
//!
//! This module provides implementations of various functional programming traits
//! for [`PersistentVector`], enabling use with the rustica categorical framework.

use crate::traits::{
    foldable::Foldable, functor::Functor, hkt::HKT, identity::Identity, monoid::Monoid,
    semigroup::Semigroup,
};

use super::core::PersistentVector;

impl<T> HKT for PersistentVector<T> {
    type Source = T;
    type Output<U> = PersistentVector<U>;
}

impl<T: Clone> Identity for PersistentVector<T> {
    #[inline]
    fn value(&self) -> &Self::Source {
        self.first().expect("PersistentVector is empty")
    }

    #[inline]
    fn try_value(&self) -> Option<&Self::Source> {
        self.first()
    }

    #[inline]
    fn into_value(self) -> Self::Source {
        self.into_iter().next().expect("PersistentVector is empty")
    }

    #[inline]
    fn try_into_value(self) -> Option<Self::Source> {
        self.into_iter().next()
    }
}

impl<T: Clone> Functor for PersistentVector<T> {
    #[inline]
    fn fmap<B, F>(&self, f: F) -> Self::Output<B>
    where
        F: Fn(&Self::Source) -> B,
        B: Clone,
    {
        self.map(f)
    }

    #[inline]
    fn fmap_owned<B, F>(self, f: F) -> Self::Output<B>
    where
        F: Fn(Self::Source) -> B,
        B: Clone,
        Self: Sized,
    {
        PersistentVector::from_iter(self.into_iter().map(f))
    }
}

impl<T: Clone> Foldable for PersistentVector<T> {
    #[inline]
    fn fold_left<U: Clone, F>(&self, init: &U, f: F) -> U
    where
        F: Fn(&U, &Self::Source) -> U,
    {
        let mut acc = init.clone();
        for item in self {
            acc = f(&acc, item);
        }
        acc
    }

    #[inline]
    fn fold_right<U: Clone, F>(&self, init: &U, f: F) -> U
    where
        F: Fn(&Self::Source, &U) -> U,
    {
        let mut acc = init.clone();
        for i in (0..self.len()).rev() {
            if let Some(item) = self.get(i) {
                acc = f(item, &acc);
            }
        }
        acc
    }

    #[inline]
    fn length(&self) -> usize {
        self.len()
    }
}

impl<T: Clone> Semigroup for PersistentVector<T> {
    #[inline]
    fn combine(&self, other: &Self) -> Self {
        self.concat(other)
    }

    #[inline]
    fn combine_owned(self, other: Self) -> Self {
        self.concat(&other)
    }
}

impl<T: Clone> Monoid for PersistentVector<T> {
    #[inline]
    fn empty() -> Self {
        PersistentVector::new()
    }
}
