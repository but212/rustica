//! # Choice (`Choice<T>`)
//!
//! The `Choice<T>` datatype represents a primary value along with a list of alternative values,
//! all of type `T`. It is statically guaranteed to never be empty.

#[cfg(any(test, feature = "quickcheck"))]
use quickcheck::{Arbitrary, Gen};
use smallvec::SmallVec;
use std::fmt::{Debug, Display, Formatter};
use std::hash::Hash;

use crate::datatypes::error::ChoiceError;
use crate::prelude::traits::*;

/// A type representing a primary value along with zero or more alternative values.
///
/// `Choice<T>` is statically guaranteed to be non-empty.
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Choice<T> {
    pub(crate) primary: T,
    pub(crate) alternatives: SmallVec<[T; 7]>,
}

impl<T> Choice<T> {
    /// Creates a new `Choice` with a primary value and a collection of alternatives.
    #[inline]
    pub fn new<I>(primary: T, alternatives: I) -> Self
    where
        I: IntoIterator<Item = T>,
    {
        Self {
            primary,
            alternatives: alternatives.into_iter().collect(),
        }
    }

    /// Creates a single-value `Choice` with no alternatives.
    #[inline]
    pub fn single(primary: T) -> Self {
        Self {
            primary,
            alternatives: SmallVec::new(),
        }
    }

    /// Returns a reference to the primary value.
    #[inline]
    pub fn primary(&self) -> &T {
        &self.primary
    }

    /// Returns a reference to the first (primary) value.
    #[inline]
    pub fn first(&self) -> &T {
        &self.primary
    }

    /// Returns a slice containing all alternative values.
    #[inline]
    pub fn alternatives(&self) -> &[T] {
        &self.alternatives
    }

    /// Returns the total number of values (1 primary + alternatives count).
    #[inline]
    pub fn len(&self) -> usize {
        1 + self.alternatives.len()
    }

    /// Returns whether the `Choice` is empty. Always `false`.
    #[inline]
    pub fn is_empty(&self) -> bool {
        false
    }

    /// Creates a `Choice` from an iterator if it yields at least one element.
    #[inline]
    pub fn of_many<I>(many: I) -> Option<Self>
    where
        I: IntoIterator<Item = T>,
    {
        let mut iter = many.into_iter();
        let primary = iter.next()?;
        let alternatives = iter.collect();
        Some(Self {
            primary,
            alternatives,
        })
    }

    /// Filters values in the `Choice`. Returns `None` if all values are filtered out.
    pub fn filter_values<F>(&self, mut predicate: F) -> Option<Self>
    where
        T: Clone,
        F: FnMut(&T) -> bool,
    {
        let mut kept = SmallVec::<[T; 8]>::new();
        if predicate(&self.primary) {
            kept.push(self.primary.clone());
        }
        for alt in &self.alternatives {
            if predicate(alt) {
                kept.push(alt.clone());
            }
        }

        if kept.is_empty() {
            None
        } else {
            let mut iter = kept.into_iter();
            let primary = iter.next().unwrap();
            let alternatives = iter.collect();
            Some(Self {
                primary,
                alternatives,
            })
        }
    }

    /// Returns an iterator over all values (primary first, followed by alternatives).
    #[inline]
    pub fn iter(&self) -> impl Iterator<Item = &T> {
        std::iter::once(&self.primary).chain(self.alternatives.iter())
    }

    /// Safely flattens a `Choice` of iterable items.
    pub fn try_flatten<I>(&self) -> Result<Choice<I>, ChoiceError>
    where
        T: IntoIterator<Item = I> + Clone,
        I: Clone,
    {
        let primary_iter = self.primary.clone().into_iter();
        let mut primary_iter = primary_iter;

        match primary_iter.next() {
            Some(first_item) => {
                let alternatives = primary_iter
                    .chain(
                        self.alternatives
                            .iter()
                            .flat_map(|val| val.clone().into_iter()),
                    )
                    .collect::<SmallVec<[I; 7]>>();

                Ok(Choice {
                    primary: first_item,
                    alternatives,
                })
            },
            None => Err(ChoiceError::EmptyPrimaryIterator),
        }
    }

    /// Flattens a `Choice` of iterable items, returning `None` if the primary iterator is empty.
    pub fn flatten<I>(&self) -> Option<Choice<I>>
    where
        T: IntoIterator<Item = I> + Clone,
        I: Clone,
    {
        self.try_flatten().ok()
    }
}

impl<T> HKT for Choice<T> {
    type Source = T;
    type Output<U> = Choice<U>;
}

impl<T> Pure for Choice<T> {
    fn pure<A>(value: A) -> Self::Output<A> {
        Choice::single(value)
    }
}

impl<T> Functor for Choice<T> {
    fn fmap<B, F>(self, mut f: F) -> Self::Output<B>
    where
        F: FnMut(Self::Source) -> B,
    {
        Choice {
            primary: f(self.primary),
            alternatives: self.alternatives.into_iter().map(f).collect(),
        }
    }
}

impl<T> Applicative for Choice<T> {
    fn apply<A, B>(self, value: Self::Output<A>) -> Self::Output<B>
    where
        Self::Source: Fn(A) -> B,
        A: Clone,
    {
        let primary = (self.primary)(value.primary.clone());
        let mut alternatives = SmallVec::<[B; 7]>::new();

        for val_alt in &value.alternatives {
            alternatives.push((self.primary)(val_alt.clone()));
        }

        for fn_alt in self.alternatives {
            alternatives.push(fn_alt(value.primary.clone()));
            for val_alt in &value.alternatives {
                alternatives.push(fn_alt(val_alt.clone()));
            }
        }

        Choice {
            primary,
            alternatives,
        }
    }

    fn lift2<A, B, C, F>(f: F, fa: Self::Output<A>, fb: Self::Output<B>) -> Self::Output<C>
    where
        F: Fn(A, B) -> C,
        A: Clone,
        B: Clone,
    {
        let primary = f(fa.primary.clone(), fb.primary.clone());
        let mut alternatives = SmallVec::<[C; 7]>::new();

        for b in &fb.alternatives {
            alternatives.push(f(fa.primary.clone(), b.clone()));
        }

        for a in fa.alternatives {
            alternatives.push(f(a.clone(), fb.primary.clone()));
            for b in &fb.alternatives {
                alternatives.push(f(a.clone(), b.clone()));
            }
        }

        Choice {
            primary,
            alternatives,
        }
    }

    fn lift3<A, B, C, D, F>(
        f: F, fa: Self::Output<A>, fb: Self::Output<B>, fc: Self::Output<C>,
    ) -> Self::Output<D>
    where
        F: Fn(A, B, C) -> D,
        A: Clone,
        B: Clone,
        C: Clone,
    {
        let a_vals: Vec<A> = fa.into();
        let b_vals: Vec<B> = fb.into();
        let c_vals: Vec<C> = fc.into();

        let primary = f(a_vals[0].clone(), b_vals[0].clone(), c_vals[0].clone());
        let mut alternatives = SmallVec::<[D; 7]>::new();

        let mut first = true;
        for a in &a_vals {
            for b in &b_vals {
                for c in &c_vals {
                    if first {
                        first = false;
                    } else {
                        alternatives.push(f(a.clone(), b.clone(), c.clone()));
                    }
                }
            }
        }

        Choice {
            primary,
            alternatives,
        }
    }
}

impl<T> Monad for Choice<T> {
    #[inline]
    fn bind<U, F>(self, mut f: F) -> Self::Output<U>
    where
        F: FnMut(Self::Source) -> Self::Output<U>,
    {
        let primary_choice = f(self.primary);
        let mut alternatives = primary_choice.alternatives;

        for alt in self.alternatives {
            let alt_choice = f(alt);
            alternatives.push(alt_choice.primary);
            alternatives.extend(alt_choice.alternatives);
        }

        Choice {
            primary: primary_choice.primary,
            alternatives,
        }
    }

    #[inline]
    fn join<U>(self) -> Self::Output<U>
    where
        Self::Source: Into<Self::Output<U>>,
    {
        let primary_choice: Self::Output<U> = self.primary.into();
        let mut alternatives = primary_choice.alternatives;

        for alt in self.alternatives {
            let alt_choice: Self::Output<U> = alt.into();
            alternatives.push(alt_choice.primary);
            alternatives.extend(alt_choice.alternatives);
        }

        Choice {
            primary: primary_choice.primary,
            alternatives,
        }
    }
}

impl<T> Semigroup for Choice<T> {
    fn combine(mut self, other: Self) -> Self {
        self.alternatives.push(other.primary);
        self.alternatives.extend(other.alternatives);
        self
    }
}

impl<T: Clone> Choice<Option<T>> {
    /// Sequences a `Choice` of `Option`s into an `Option` of a `Choice`.
    pub fn sequence(self) -> Option<Choice<T>> {
        let primary = self.primary?;
        let mut alternatives = SmallVec::<[T; 7]>::with_capacity(self.alternatives.len());
        for alt in self.alternatives {
            alternatives.push(alt?);
        }
        Some(Choice {
            primary,
            alternatives,
        })
    }
}

impl<'a, T> IntoIterator for &'a Choice<T> {
    type Item = &'a T;
    type IntoIter = std::iter::Chain<std::iter::Once<&'a T>, std::slice::Iter<'a, T>>;

    fn into_iter(self) -> Self::IntoIter {
        std::iter::once(&self.primary).chain(self.alternatives.iter())
    }
}

impl<T> IntoIterator for Choice<T> {
    type Item = T;
    type IntoIter = std::iter::Chain<std::iter::Once<T>, smallvec::IntoIter<[T; 7]>>;

    fn into_iter(self) -> Self::IntoIter {
        std::iter::once(self.primary).chain(self.alternatives)
    }
}

impl<T: Display> Display for Choice<T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.primary)?;
        if !self.alternatives.is_empty() {
            let alt_strs: Vec<String> = self.alternatives.iter().map(|a| a.to_string()).collect();
            write!(f, " | {}", alt_strs.join(", "))?;
        }
        Ok(())
    }
}

impl<T> Foldable for Choice<T> {
    fn fold_left<B, F>(&self, initial: B, mut f: F) -> B
    where
        F: FnMut(B, &Self::Source) -> B,
    {
        let acc = f(initial, &self.primary);
        self.alternatives.iter().fold(acc, f)
    }

    fn fold_right<B, F>(&self, initial: B, mut f: F) -> B
    where
        F: FnMut(&Self::Source, B) -> B,
    {
        let acc = self.alternatives.iter().rev().fold(initial, |a, v| f(v, a));
        f(&self.primary, acc)
    }
}

impl<T> TryFrom<Vec<T>> for Choice<T> {
    type Error = ChoiceError;

    fn try_from(values: Vec<T>) -> Result<Self, Self::Error> {
        Self::of_many(values).ok_or(ChoiceError::EmptyInput)
    }
}

impl<T: Clone> TryFrom<&[T]> for Choice<T> {
    type Error = ChoiceError;

    fn try_from(values: &[T]) -> Result<Self, Self::Error> {
        Self::of_many(values.iter().cloned()).ok_or(ChoiceError::EmptyInput)
    }
}

impl<T> From<Choice<T>> for Vec<T> {
    fn from(choice: Choice<T>) -> Self {
        let mut v = Vec::with_capacity(1 + choice.alternatives.len());
        v.push(choice.primary);
        v.extend(choice.alternatives);
        v
    }
}

impl<T: Default> Default for Choice<T> {
    fn default() -> Self {
        Self {
            primary: T::default(),
            alternatives: SmallVec::new(),
        }
    }
}

#[cfg(any(test, feature = "quickcheck"))]
impl<T: Arbitrary + Clone + 'static> Arbitrary for Choice<T> {
    fn arbitrary(g: &mut Gen) -> Self {
        let primary: T = Arbitrary::arbitrary(g);
        let alternatives: Vec<T> = Arbitrary::arbitrary(g);
        Choice::new(primary, alternatives)
    }
}

#[cfg(test)]
mod unit_tests {
    use super::Choice;
    use crate::prelude::*;

    #[test]
    fn monad_laws_hold_for_choice() {
        let m = Choice::new(1, vec![2]);
        let f = |x: i32| Choice::new(x + 1, vec![]);
        let g = |x: i32| Choice::new(x * 2, vec![]);

        assert_eq!(Choice::<i32>::pure(10).bind(f), f(10));
        assert_eq!(m.clone().bind(Choice::<i32>::pure), m);
        assert_eq!(m.clone().bind(f).bind(g), m.bind(|x| f(x).bind(g)));
    }

    #[test]
    fn choice_construction_and_filtering_preserve_values() {
        let c = Choice::new(1, vec![2, 3, 4]);
        assert_eq!(*c.first(), 1);
        assert_eq!(*c.primary(), 1);
        assert_eq!(c.alternatives(), &[2, 3, 4]);
        assert_eq!(c.len(), 4);
        assert!(!c.is_empty());

        let empty: Result<Choice<i32>, _> = Vec::new().try_into();
        assert_eq!(empty, Err(crate::datatypes::error::ChoiceError::EmptyInput));
        let choice: Choice<i32> = vec![10, 20, 30].try_into().unwrap();
        assert_eq!(choice.iter().copied().collect::<Vec<_>>(), vec![10, 20, 30]);

        assert_eq!(Choice::of_many(Vec::<i32>::new()), None);
        let evens = c.filter_values(|&x| x % 2 == 0).expect("should have evens");
        assert_eq!(*evens.first(), 2);
        assert_eq!(evens.alternatives(), &[4]);
        assert_eq!(c.filter_values(|&x| x > 100), None);
    }
}
