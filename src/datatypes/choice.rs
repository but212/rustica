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
//! let matched = endpoints.iter().find_map(|ep| ep.strip_prefix("backup"));
//! assert_eq!(matched, Some("1.api.com"));
//! ```
//!
//! # Priority Transformation and Combination
//! Transformation via [`map`](Choice::map) and combination via [`Semigroup`] strictly preserve
//! priority ordering:
//! - `map` transforms `primary` and all `alternatives` preserving order.
//! - `combine` chains another choice's values after the current alternatives.

#[cfg(any(test, feature = "quickcheck"))]
use quickcheck::{Arbitrary, Gen};
use std::fmt::{Debug, Display, Formatter};
use std::hash::Hash;

use crate::datatypes::validated::Validated;
use crate::prelude::traits::*;

/// Errors that can occur during `Choice<T>` operations.
///
/// This enum represents error conditions for [`Choice`]
/// operations that would otherwise panic.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum ChoiceError {
    /// Every inner iterable was empty during a flatten operation.
    ///
    /// This error occurs when calling `try_flatten` on a `Choice` where neither the
    /// primary value nor any alternative produces an item.
    EmptyFlatten,

    /// Input contained no values when constructing a `Choice`.
    EmptyInput,
}

impl ChoiceError {
    /// Returns `true` if this is an `EmptyFlatten` error.
    #[inline]
    pub const fn is_empty_flatten(&self) -> bool {
        matches!(self, ChoiceError::EmptyFlatten)
    }

    /// Returns `true` if this is an `EmptyInput` error.
    #[inline]
    pub const fn is_empty_input(&self) -> bool {
        matches!(self, ChoiceError::EmptyInput)
    }
}

impl Display for ChoiceError {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            ChoiceError::EmptyFlatten => {
                write!(
                    f,
                    "Choice::try_flatten(): no inner iterable produced an item"
                )
            },
            ChoiceError::EmptyInput => write!(f, "Choice construction requires at least one value"),
        }
    }
}

impl std::error::Error for ChoiceError {}

/// A statically non-empty collection with priority and fallback semantics.
///
/// `primary` is the preferred value; `alternatives` are ordered fallbacks.
/// Prefer using [`try_each`](Self::try_each) or `iter().find_map()`
/// to execute fallback logic in priority order rather than extracting raw values.
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Choice<T> {
    pub(crate) primary: T,
    pub(crate) alternatives: Vec<T>,
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
    pub const fn single(primary: T) -> Self {
        Self {
            primary,
            alternatives: Vec::new(),
        }
    }

    /// Returns a reference to the primary value.
    #[inline]
    pub const fn primary(&self) -> &T {
        &self.primary
    }

    /// Returns a slice containing all alternative values.
    #[inline]
    pub fn alternatives(&self) -> &[T] {
        &self.alternatives
    }

    /// Returns the total number of values (1 primary + alternatives count).
    #[inline]
    pub const fn len(&self) -> usize {
        1 + self.alternatives.len()
    }

    /// Returns whether the `Choice` is empty. Always `false`.
    #[inline]
    pub const fn is_empty(&self) -> bool {
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

    /// Filters values in the `Choice` by consuming it. Returns `None` if all values are filtered out.
    ///
    /// Consumes `self` and does not require `T: Clone`.
    pub fn filter<F>(mut self, mut predicate: F) -> Option<Self>
    where
        F: FnMut(&T) -> bool,
    {
        if predicate(&self.primary) {
            self.alternatives.retain(predicate);
            Some(self)
        } else {
            let idx = self.alternatives.iter().position(&mut predicate)?;
            let primary = self.alternatives.remove(idx);
            self.alternatives.drain(..idx);
            self.alternatives.retain(predicate);
            Some(Self {
                primary,
                alternatives: self.alternatives,
            })
        }
    }

    /// Returns an iterator over all values (primary first, followed by alternatives).
    #[inline]
    pub fn iter(&self) -> impl Iterator<Item = &T> {
        std::iter::once(&self.primary).chain(self.alternatives.iter())
    }

    /// Safely flattens a `Choice` of iterable items by consuming it.
    ///
    /// Unlike [`Self::try_flatten_cloned`], this consuming version does not require `T: Clone`.
    ///
    /// Items are concatenated in priority order: the first yielded item becomes the new
    /// primary, followed by the primary iterable's remaining items and then the items of
    /// each alternative's iterable. Returns [`ChoiceError::EmptyFlatten`] when every
    /// iterable is empty.
    pub fn try_flatten<I>(self) -> Result<Choice<I>, ChoiceError>
    where
        T: IntoIterator<Item = I>,
    {
        let mut flattened = self.primary.into_iter().chain(
            self.alternatives
                .into_iter()
                .flat_map(IntoIterator::into_iter),
        );

        match flattened.next() {
            Some(primary) => Ok(Choice {
                primary,
                alternatives: flattened.collect(),
            }),
            None => Err(ChoiceError::EmptyFlatten),
        }
    }

    /// Safely flattens a borrowed `Choice` of iterable items by cloning elements.
    pub fn try_flatten_cloned<I>(&self) -> Result<Choice<I>, ChoiceError>
    where
        T: IntoIterator<Item = I> + Clone,
    {
        self.clone().try_flatten()
    }

    /// Flattens a `Choice` of iterable items by consuming it, returning `None` if all inner iterables are empty.
    ///
    /// Unlike [`Self::flatten_cloned`], this consuming version does not require `T: Clone`.
    pub fn flatten<I>(self) -> Option<Choice<I>>
    where
        T: IntoIterator<Item = I>,
    {
        self.try_flatten().ok()
    }

    /// Flattens a borrowed `Choice` of iterable items by cloning elements, returning `None` if all inner iterables are empty.
    pub fn flatten_cloned<I>(&self) -> Option<Choice<I>>
    where
        T: IntoIterator<Item = I> + Clone,
    {
        self.try_flatten_cloned().ok()
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
    pub fn try_each_validated<R, E, F>(&self, mut f: F) -> Validated<R, E>
    where
        F: FnMut(&T) -> Result<R, E>,
    {
        let first_err = match f(&self.primary) {
            Ok(res) => return Validated::Valid(res),
            Err(err) => err,
        };

        let mut errors = Vec::new();
        errors.push(first_err);

        for alt in &self.alternatives {
            match f(alt) {
                Ok(res) => return Validated::Valid(res),
                Err(err) => errors.push(err),
            }
        }

        Validated::invalid_many(errors)
    }

    /// Maps a function over all options in this `Choice`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::choice::Choice;
    ///
    /// let choice = Choice::new(1, [2, 3]);
    /// let doubled = choice.map(|x| x * 2);
    /// assert_eq!(*doubled.primary(), 2);
    /// assert_eq!(doubled.alternatives(), &[4, 6]);
    /// ```
    #[inline]
    pub fn map<B, F>(self, mut f: F) -> Choice<B>
    where
        F: FnMut(T) -> B,
    {
        Choice {
            primary: f(self.primary),
            alternatives: self.alternatives.into_iter().map(f).collect(),
        }
    }

    /// Functional alias for [`map`](Self::map).
    ///
    /// Transforms the primary value and all alternatives preserving priority order.
    #[inline]
    pub fn fmap<B, F>(self, f: F) -> Choice<B>
    where
        F: FnMut(T) -> B,
    {
        self.map(f)
    }
}

impl<T> Semigroup for Choice<T> {
    fn combine(mut self, other: Self) -> Self {
        self.alternatives.push(other.primary);
        self.alternatives.extend(other.alternatives);
        self
    }
}

impl<T> Choice<Option<T>> {
    /// Sequences a `Choice` of `Option`s into an `Option` of a `Choice`.
    pub fn sequence(self) -> Option<Choice<T>> {
        Some(Choice {
            primary: self.primary?,
            alternatives: self.alternatives.into_iter().collect::<Option<Vec<T>>>()?,
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
    type IntoIter = std::iter::Chain<std::iter::Once<T>, std::vec::IntoIter<T>>;

    fn into_iter(self) -> Self::IntoIter {
        std::iter::once(self.primary).chain(self.alternatives)
    }
}

impl<T: Display> Display for Choice<T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.primary)?;
        let mut alternatives = self.alternatives.iter();
        if let Some(first) = alternatives.next() {
            write!(f, " | {first}")?;
            for alternative in alternatives {
                write!(f, ", {alternative}")?;
            }
        }
        Ok(())
    }
}

impl<T> TryFrom<Vec<T>> for Choice<T> {
    type Error = ChoiceError;

    fn try_from(mut values: Vec<T>) -> Result<Self, Self::Error> {
        if values.is_empty() {
            Err(ChoiceError::EmptyInput)
        } else {
            let primary = values.remove(0);
            Ok(Self {
                primary,
                alternatives: values,
            })
        }
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
            alternatives: Vec::new(),
        }
    }
}

#[cfg(any(test, feature = "quickcheck"))]
impl<T: Arbitrary> Arbitrary for Choice<T> {
    fn arbitrary(g: &mut Gen) -> Self {
        let primary: T = Arbitrary::arbitrary(g);
        let alternatives: Vec<T> = Arbitrary::arbitrary(g);
        Choice::new(primary, alternatives)
    }

    fn shrink(&self) -> Box<dyn Iterator<Item = Self>> {
        let primary_shrinks = self.primary.shrink().map({
            let alternatives = self.alternatives.clone();
            move |primary| Choice {
                primary,
                alternatives: alternatives.clone(),
            }
        });
        let alt_shrinks = self.alternatives.shrink().map({
            let primary = self.primary.clone();
            move |alternatives| Choice {
                primary: primary.clone(),
                alternatives,
            }
        });
        Box::new(primary_shrinks.chain(alt_shrinks))
    }
}

#[cfg(test)]
mod unit_tests {
    use super::Choice;
    use crate::prelude::*;

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
        assert_eq!(
            combined.iter().copied().collect::<Vec<_>>(),
            vec![1, 2, 3, 4, 5]
        );

        // Inherent map and fmap preserve priority structure
        let mapped = combined.clone().map(|x| x * 10);
        assert_eq!(*mapped.primary(), 10);
        assert_eq!(mapped.alternatives(), &[20, 30, 40, 50]);

        let fmapped = combined.clone().fmap(|x| x * 10);
        assert_eq!(mapped, fmapped);

        // Iterator fold preserves priority order
        let folded = combined.iter().fold(0, |acc, &x| acc * 10 + x);
        assert_eq!(folded, 12345);
    }

    #[test]
    fn choice_construction_and_filtering_preserve_values() {
        let c = Choice::new(1, vec![2, 3, 4]);
        assert_eq!(*c.primary(), 1);
        assert_eq!(c.alternatives(), &[2, 3, 4]);
        assert_eq!(c.len(), 4);
        assert!(!c.is_empty());

        let empty: Result<Choice<i32>, _> = Vec::new().try_into();
        assert_eq!(empty, Err(ChoiceError::EmptyInput));
        let choice: Choice<i32> = vec![10, 20, 30].try_into().unwrap();
        assert_eq!(choice.iter().copied().collect::<Vec<_>>(), vec![10, 20, 30]);

        assert_eq!(Choice::of_many(Vec::<i32>::new()), None);
        let evens = c
            .clone()
            .filter(|&x| x % 2 == 0)
            .expect("should have evens");
        assert_eq!(evens.alternatives(), &[4]);
        assert_eq!(c.filter(|&x| x > 100), None);
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
        let res: Validated<i32, String> =
            choices.try_each_validated(|&x| Err(format!("err_{}", x)));
        assert!(res.is_invalid());
        if let Validated::Invalid(errs) = res {
            let err_list: Vec<_> = errs.into_iter().collect();
            assert_eq!(err_list, vec!["err_1", "err_2", "err_3"]);
        } else {
            panic!("expected invalid");
        }

        // Success on alternative
        let ok_res: Validated<i32, &str> =
            choices.try_each_validated(|&x| if x == 2 { Ok(200) } else { Err("fail") });
        assert_eq!(ok_res, Validated::Valid(200));
    }

    #[test]
    fn filter_and_flatten_consume_without_clone() {
        #[derive(Debug, PartialEq, Eq)]
        struct NoClone(i32);

        let choice = Choice::new(NoClone(1), vec![NoClone(2), NoClone(3)]);
        let filtered = choice.filter(|x| x.0 % 2 != 0).expect("keeps 1 and 3");
        assert_eq!(filtered.primary(), &NoClone(1));
        assert_eq!(filtered.alternatives(), &[NoClone(3)]);

        let nested = Choice::new(vec![NoClone(10)], vec![vec![NoClone(20), NoClone(30)]]);
        let flattened = nested.flatten().expect("flatten succeeds");
        assert_eq!(flattened.primary(), &NoClone(10));
        assert_eq!(flattened.alternatives(), &[NoClone(20), NoClone(30)]);

        let empty_primary: Choice<Vec<NoClone>> = Choice::single(vec![]);
        assert_eq!(empty_primary.try_flatten(), Err(ChoiceError::EmptyFlatten));
    }

    #[test]
    fn try_flatten_uses_alternatives_when_primary_is_empty() {
        let nested = Choice::new(Vec::<i32>::new(), vec![vec![1, 2], vec![3]]);
        let flattened = nested.try_flatten().expect("alternatives supply items");
        assert_eq!(flattened.primary(), &1);
        assert_eq!(flattened.alternatives(), &[2, 3]);
    }

    #[test]
    fn flatten_cloned_and_try_flatten_cloned() {
        let nested = Choice::new(vec![1, 2], vec![vec![3, 4]]);
        let flattened = nested.flatten_cloned().unwrap();
        assert_eq!(flattened.primary(), &1);
        assert_eq!(flattened.alternatives(), &[2, 3, 4]);

        let res = nested.try_flatten_cloned().unwrap();
        assert_eq!(res.primary(), &1);
        assert_eq!(res.alternatives(), &[2, 3, 4]);
    }

    #[test]
    fn sequence_is_all_or_nothing() {
        let all_some = Choice::new(Some(1), vec![Some(2), Some(3)]);
        assert_eq!(all_some.sequence(), Some(Choice::new(1, vec![2, 3])));

        let primary_none = Choice::new(None, vec![Some(2)]);
        assert_eq!(primary_none.sequence(), None);

        let alternative_none = Choice::new(Some(1), vec![Some(2), None]);
        assert_eq!(alternative_none.sequence(), None);
    }

    #[test]
    fn display_renders_priority_then_alternatives() {
        assert_eq!(Choice::single(1).to_string(), "1");
        assert_eq!(Choice::new(1, [2, 3]).to_string(), "1 | 2, 3");
    }

    #[test]
    fn test_choice_stack_size_compactness() {
        use std::mem::size_of;
        type Large = [u8; 1024];
        assert!(size_of::<Choice<Large>>() < 1100);
    }

    #[test]
    fn test_choice_error_display() {
        assert_eq!(
            ChoiceError::EmptyFlatten.to_string(),
            "Choice::try_flatten(): no inner iterable produced an item"
        );
        assert_eq!(
            ChoiceError::EmptyInput.to_string(),
            "Choice construction requires at least one value"
        );
    }

    #[test]
    fn test_choice_error_predicates() {
        assert!(ChoiceError::EmptyFlatten.is_empty_flatten());
        assert!(!ChoiceError::EmptyFlatten.is_empty_input());
        assert!(ChoiceError::EmptyInput.is_empty_input());
        assert!(!ChoiceError::EmptyInput.is_empty_flatten());
    }

    #[test]
    fn arbitrary_shrinks_primary_value() {
        use quickcheck::Arbitrary;
        let c = Choice::single(100i32);
        let shrunk: Vec<Choice<i32>> = c.shrink().collect();
        assert!(
            !shrunk.is_empty(),
            "Arbitrary::shrink must yield candidates for primary value"
        );
        assert!(shrunk.iter().any(|s| *s.primary() < 100));
    }

    #[test]
    fn filter_in_place_evaluates_predicate_once() {
        let c = Choice::new(1, vec![3, 4, 5, 6]);
        let mut evaluated = Vec::new();
        let filtered = c.filter(|&x| {
            evaluated.push(x);
            x % 2 == 0
        });
        assert_eq!(evaluated, vec![1, 3, 4, 5, 6]);
        let res = filtered.expect("filtered result");
        assert_eq!(*res.primary(), 4);
        assert_eq!(res.alternatives(), &[6]);

        // When primary matches, alts are filtered without re-evaluating primary
        let c2 = Choice::new(2, vec![3, 4]);
        let mut eval2 = Vec::new();
        let filtered2 = c2.filter(|&x| {
            eval2.push(x);
            x % 2 == 0
        });
        assert_eq!(eval2, vec![2, 3, 4]);
        let res2 = filtered2.expect("filtered result");
        assert_eq!(*res2.primary(), 2);
        assert_eq!(res2.alternatives(), &[4]);

        // When nothing matches, returns None
        let c3 = Choice::new(1, vec![3, 5]);
        assert_eq!(c3.filter(|&x| x % 2 == 0), None);
    }

    #[test]
    fn try_from_vec_reuses_allocation() {
        let mut v = Vec::with_capacity(64);
        v.extend([10, 20, 30, 40]);
        let choice = Choice::try_from(v).expect("conversion succeeds");
        assert_eq!(*choice.primary(), 10);
        assert_eq!(choice.alternatives(), &[20, 30, 40]);
        assert_eq!(choice.alternatives.capacity(), 64);
    }
}
