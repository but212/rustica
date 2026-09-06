//! # Choice (`Choice<T>`)
//!
//! A non-empty ordered collection where the **primary** value is always tried first,
//! and **alternatives** serve as fallback options tried in order when the primary fails.
//!
//! # When to Use
//! Use `Choice<T>` when a function requires a guaranteed primary target and
//! zero or more ordered fallback targets. The type makes priority and fallback
//! semantics explicit and statically enforced.
//!
//! # Intended Usage
//! ```rust
//! use rustica::datatypes::choice::Choice;
//!
//! let endpoints = Choice::new("primary.api.com", ["backup1.api.com", "backup2.api.com"]);
//!
//! // Try connecting to each endpoint in priority order
//! let result = endpoints.try_each(|ep| {
//!     if *ep == "backup1.api.com" { Ok("connected") } else { Err("unreachable") }
//! });
//! assert_eq!(result, Ok("connected"));
//!
//! // Or find the first matching endpoint
//! let matched = endpoints.first_match(|ep| ep.strip_prefix("backup"));
//! assert_eq!(matched, Some("1.api.com"));
//! ```
//!
//! # Priority Transformation and Combination
//! Transformation via [`Functor`] and combination via [`Semigroup`] strictly preserve
//! priority ordering:
//! - `fmap` transforms `primary` and all `alternatives` preserving order.
//! - `combine` chains another choice's values after the current alternatives.
//!
//! Monadic and applicative operations are deprecated since 0.16.0 in favor of clean
//! priority/alternatives collection semantics.

#[cfg(any(test, feature = "quickcheck"))]
use quickcheck::{Arbitrary, Gen};
use smallvec::SmallVec;
use std::fmt::{Debug, Display, Formatter};
use std::hash::Hash;

use crate::datatypes::error::ChoiceError;
use crate::datatypes::validated::Validated;
use crate::prelude::traits::*;

/// A statically non-empty collection with priority and fallback semantics.
///
/// `primary` is the preferred value; `alternatives` are ordered fallbacks.
/// Prefer using [`try_each`](Self::try_each) or [`first_match`](Self::first_match)
/// to execute fallback logic in priority order rather than extracting raw values.
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

    /// Tries `f` on each value in priority order (primary first, then alternatives).
    ///
    /// Returns the first `Ok` result, short-circuiting on success so subsequent
    /// alternatives are not evaluated. If all values fail, returns the last `Err`.
    pub fn try_each<R, E, F>(&self, mut f: F) -> Result<R, E>
    where
        F: FnMut(&T) -> Result<R, E>,
    {
        let mut last_err = match f(&self.primary) {
            Ok(res) => return Ok(res),
            Err(err) => err,
        };

        for alt in &self.alternatives {
            match f(alt) {
                Ok(res) => return Ok(res),
                Err(err) => last_err = err,
            }
        }

        Err(last_err)
    }

    /// Tries `f` on each value in priority order, collecting all errors into [`Validated`] on total failure.
    ///
    /// Returns [`Validated::Valid`] on the first `Ok` result, short-circuiting on success.
    /// If all values fail, returns [`Validated::Invalid`] containing every encountered error in order.
    pub fn try_each_validated<R, E, F>(&self, mut f: F) -> Validated<E, R>
    where
        F: FnMut(&T) -> Result<R, E>,
    {
        let first_err = match f(&self.primary) {
            Ok(res) => return Validated::Valid(res),
            Err(err) => err,
        };

        let mut errors = SmallVec::<[E; 8]>::new();
        errors.push(first_err);

        for alt in &self.alternatives {
            match f(alt) {
                Ok(res) => return Validated::Valid(res),
                Err(err) => errors.push(err),
            }
        }

        Validated::invalid_many(errors)
    }

    /// Returns the first `Some` result from `f` applied in priority order.
    ///
    /// Short-circuits on the first `Some`, returning immediately without
    /// evaluating remaining alternatives. Returns `None` if no value matches.
    pub fn first_match<R, F>(&self, mut f: F) -> Option<R>
    where
        F: FnMut(&T) -> Option<R>,
    {
        if let Some(res) = f(&self.primary) {
            return Some(res);
        }
        for alt in &self.alternatives {
            if let Some(res) = f(alt) {
                return Some(res);
            }
        }
        None
    }

    /// Monadic bind for `Choice`.
    ///
    /// # Deprecated (since 0.16.0)
    /// `Choice` is redefined as a non-empty priority/alternatives collection.
    /// Monadic operations are deprecated and will be removed in a future release.
    #[deprecated(
        since = "0.16.0",
        note = "Choice is redefined as a non-empty priority/alternatives collection; Monad operations are deprecated."
    )]
    pub fn bind<U, F>(self, f: F) -> Choice<U>
    where
        F: FnMut(T) -> Choice<U>,
    {
        Monad::bind(self, f)
    }

    /// Applicative functor application for `Choice`.
    ///
    /// # Deprecated (since 0.16.0)
    /// `Choice` is redefined as a non-empty priority/alternatives collection.
    /// Applicative operations are deprecated and will be removed in a future release.
    #[deprecated(
        since = "0.16.0",
        note = "Choice is redefined as a non-empty priority/alternatives collection; Applicative operations are deprecated."
    )]
    pub fn apply<A, B>(self, value: Choice<A>) -> Choice<B>
    where
        T: Fn(A) -> B,
        A: Clone,
    {
        Applicative::apply(self, value)
    }
}

impl<T> HKT for Choice<T> {
    type Source = T;
    type Output<U> = Choice<U>;
}

/// # Deprecated (since 0.16.0)
///
/// `Choice` is redefined as a non-empty priority/alternatives collection.
/// Use [`Choice::single`] instead.
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

/// # Deprecated (since 0.16.0)
///
/// `Choice` is redefined as a non-empty priority/alternatives collection.
/// Applicative operations are deprecated and will be removed in a future release.
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
        let primary = f(fa.primary.clone(), fb.primary.clone(), fc.primary.clone());
        let mut alternatives = SmallVec::<[D; 7]>::new();

        for c in &fc.alternatives {
            alternatives.push(f(fa.primary.clone(), fb.primary.clone(), c.clone()));
        }

        for b in &fb.alternatives {
            alternatives.push(f(fa.primary.clone(), b.clone(), fc.primary.clone()));
            for c in &fc.alternatives {
                alternatives.push(f(fa.primary.clone(), b.clone(), c.clone()));
            }
        }

        for a in &fa.alternatives {
            alternatives.push(f(a.clone(), fb.primary.clone(), fc.primary.clone()));
            for c in &fc.alternatives {
                alternatives.push(f(a.clone(), fb.primary.clone(), c.clone()));
            }
            for b in &fb.alternatives {
                alternatives.push(f(a.clone(), b.clone(), fc.primary.clone()));
                for c in &fc.alternatives {
                    alternatives.push(f(a.clone(), b.clone(), c.clone()));
                }
            }
        }

        Choice {
            primary,
            alternatives,
        }
    }
}

/// # Deprecated (since 0.16.0)
///
/// `Choice` is redefined as a non-empty priority/alternatives collection.
/// Monadic operations are deprecated and will be removed in a future release.
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
    #[allow(deprecated)]
    fn monad_laws_hold_for_choice_backward_compatibility() {
        let m = Choice::new(1, vec![2]);
        let f = |x: i32| Choice::new(x + 1, vec![]);
        let g = |x: i32| Choice::new(x * 2, vec![]);

        assert_eq!(Choice::<i32>::pure(10).bind(f), f(10));
        assert_eq!(m.clone().bind(Choice::<i32>::pure), m);
        assert_eq!(m.clone().bind(f).bind(g), m.bind(|x| f(x).bind(g)));
    }

    #[test]
    fn priority_and_transformation_contracts() {
        // C-01: Non-empty single and multiple
        let s = Choice::single(100);
        assert_eq!(*s.primary(), 100);
        assert_eq!(s.len(), 1);
        assert!(!s.is_empty());

        // C-03: Semigroup combine preserves priority order (primary + alts + other.primary + other.alts)
        let c1 = Choice::new(1, vec![2]);
        let c2 = Choice::new(3, vec![4, 5]);
        let combined = c1.combine(c2);
        assert_eq!(*combined.primary(), 1);
        assert_eq!(combined.alternatives(), &[2, 3, 4, 5]);
        assert_eq!(combined.iter().copied().collect::<Vec<_>>(), vec![1, 2, 3, 4, 5]);

        // C-04: Functor fmap preserves priority structure
        let mapped = combined.clone().fmap(|x| x * 10);
        assert_eq!(*mapped.primary(), 10);
        assert_eq!(mapped.alternatives(), &[20, 30, 40, 50]);

        // Foldable preserves priority order
        let folded = combined.fold_left(0, |acc, &x| acc * 10 + x);
        assert_eq!(folded, 12345);
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

    #[test]
    fn try_each_returns_first_success() {
        let choices = Choice::new(1, [2, 3]);
        let mut calls = Vec::new();
        let res = choices.try_each(|&x| {
            calls.push(x);
            Ok::<_, &str>(x * 10)
        });
        assert_eq!(res, Ok(10));
        assert_eq!(calls, vec![1]);
    }

    #[test]
    fn try_each_falls_back_on_failure() {
        let choices = Choice::new(1, [2, 3]);
        let mut calls = Vec::new();
        let res = choices.try_each(|&x| {
            calls.push(x);
            if x == 2 {
                Ok::<_, &str>(x * 10)
            } else {
                Err("failed")
            }
        });
        assert_eq!(res, Ok(20));
        assert_eq!(calls, vec![1, 2]);
    }

    #[test]
    fn try_each_returns_last_error() {
        let choices = Choice::new(1, [2, 3]);
        let mut calls = Vec::new();
        let res = choices.try_each(|&x| {
            calls.push(x);
            Err::<i32, _>(format!("err_{}", x))
        });
        assert_eq!(res, Err("err_3".to_string()));
        assert_eq!(calls, vec![1, 2, 3]);
    }

    #[test]
    fn try_each_validated_collects_errors() {
        let choices = Choice::new(1, [2, 3]);
        let res: Validated<String, i32> = choices.try_each_validated(|&x| {
            Err(format!("err_{}", x))
        });
        assert!(res.is_invalid());
        if let Validated::Invalid(errs) = res {
            let err_list: Vec<_> = errs.into_iter().collect();
            assert_eq!(err_list, vec!["err_1", "err_2", "err_3"]);
        } else {
            panic!("expected invalid");
        }

        // Success on alternative
        let ok_res: Validated<&str, i32> = choices.try_each_validated(|&x| {
            if x == 2 {
                Ok(200)
            } else {
                Err("fail")
            }
        });
        assert_eq!(ok_res, Validated::Valid(200));
    }

    #[test]
    fn first_match_returns_primary() {
        let choices = Choice::new(10, [20, 30]);
        let mut calls = Vec::new();
        let res = choices.first_match(|&x| {
            calls.push(x);
            if x >= 10 { Some(x * 2) } else { None }
        });
        assert_eq!(res, Some(20));
        assert_eq!(calls, vec![10]); // Short-circuits on primary
    }

    #[test]
    fn first_match_falls_back_and_returns_none() {
        let choices = Choice::new(1, [2, 3]);
        // Fallback to alternative
        let res = choices.first_match(|&x| if x == 3 { Some(x * 100) } else { None });
        assert_eq!(res, Some(300));

        // Total failure returns None
        let none_res = choices.first_match(|&x| if x > 100 { Some(x) } else { None });
        assert_eq!(none_res, None);
    }
}
