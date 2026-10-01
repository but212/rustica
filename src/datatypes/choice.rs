#![doc = include_str!("../../docs/datatypes/choice.md")]

#[cfg(any(test, feature = "quickcheck"))]
use alloc::boxed::Box;
use alloc::vec::Vec;
use core::fmt::{Debug, Display, Formatter};
use core::hash::Hash;
#[cfg(any(test, feature = "quickcheck"))]
use quickcheck::{Arbitrary, Gen};

use crate::datatypes::validated::Validated;
use crate::prelude::traits::*;

/// Errors produced by [`Choice`] operations.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum ChoiceError {
    /// Inner iterables produced no items during [`Choice::try_flatten`].
    EmptyFlatten,

    /// Input was empty during construction.
    EmptyInput,
}

impl ChoiceError {
    /// Returns `true` if this is [`EmptyFlatten`](Self::EmptyFlatten).
    #[inline]
    pub const fn is_empty_flatten(&self) -> bool {
        matches!(self, ChoiceError::EmptyFlatten)
    }

    /// Returns `true` if this is [`EmptyInput`](Self::EmptyInput).
    #[inline]
    pub const fn is_empty_input(&self) -> bool {
        matches!(self, ChoiceError::EmptyInput)
    }
}

impl Display for ChoiceError {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
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

impl core::error::Error for ChoiceError {}

/// A statically non-empty collection with priority and fallback semantics.
///
/// `primary` is tried first; `alternatives` are ordered fallbacks.
/// Prefer [`try_each`](Self::try_each) or `iter().find_map()` over extracting raw values.
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Choice<T> {
    pub(crate) primary: T,
    pub(crate) alternatives: Vec<T>,
}

impl<T> Choice<T> {
    /// Creates a `Choice` with a primary value and alternatives.
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

    /// Returns a slice of alternative values.
    #[inline]
    pub const fn alternatives(&self) -> &[T] {
        self.alternatives.as_slice()
    }

    /// Returns the total number of values (primary plus alternatives).
    #[inline]
    pub const fn len(&self) -> usize {
        1 + self.alternatives.len()
    }

    /// Returns `false`; a `Choice` is statically non-empty.
    #[inline]
    pub const fn is_empty(&self) -> bool {
        false
    }

    /// Creates a `Choice` from an iterator yielding at least one element.
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

    /// Retains values matching `predicate`, consuming `self`.
    ///
    /// Returns `None` if all values are filtered out. Does not require `T: Clone`.
    pub fn filter<F>(mut self, mut predicate: F) -> Option<Self>
    where
        F: FnMut(&T) -> bool,
    {
        if predicate(&self.primary) {
            self.alternatives.retain(predicate);
            Some(self)
        } else {
            // Drain the visited prefix through `idx` so `retain` only inspects unvisited
            // values; `predicate` runs exactly once per element. Reordering double-evaluates.
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

    /// Returns an iterator over all values in priority order.
    #[inline]
    pub fn iter(&self) -> impl Iterator<Item = &T> {
        core::iter::once(&self.primary).chain(self.alternatives.iter())
    }

    /// Flattens nested iterables in priority order, consuming `self`.
    ///
    /// The first yielded item becomes the new primary. Returns [`ChoiceError::EmptyFlatten`]
    /// if every iterable is empty. Does not require `T: Clone`.
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

    /// Flattens nested iterables in priority order, returning `None` if all are empty.
    ///
    /// Consumes `self` without requiring `T: Clone`.
    pub fn flatten<I>(self) -> Option<Choice<I>>
    where
        T: IntoIterator<Item = I>,
    {
        self.try_flatten().ok()
    }

    /// Evaluates `f` in priority order, short-circuiting on the first `Ok`.
    ///
    /// Returns the first `Ok`, or the last `Err` if all values fail.
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

    /// Evaluates `f` in priority order, short-circuiting on the first `Ok`.
    ///
    /// Returns [`Validated::Valid`] on success, or [`Validated::Invalid`] collecting
    /// all errors in order if all values fail.
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

    /// Maps `f` over all values in priority order.
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
}

impl<T> Semigroup for Choice<T> {
    fn combine(mut self, other: Self) -> Self {
        self.alternatives.extend(other);
        self
    }
}

impl<T> Choice<Option<T>> {
    /// Transposes a `Choice<Option<T>>` into `Option<Choice<T>>`.
    pub fn sequence(self) -> Option<Choice<T>> {
        Some(Choice {
            primary: self.primary?,
            alternatives: self.alternatives.into_iter().collect::<Option<Vec<T>>>()?,
        })
    }
}

impl<'a, T> IntoIterator for &'a Choice<T> {
    type Item = &'a T;
    type IntoIter = core::iter::Chain<core::iter::Once<&'a T>, core::slice::Iter<'a, T>>;

    fn into_iter(self) -> Self::IntoIter {
        core::iter::once(&self.primary).chain(self.alternatives.iter())
    }
}

impl<T> IntoIterator for Choice<T> {
    type Item = T;
    type IntoIter = core::iter::Chain<core::iter::Once<T>, alloc::vec::IntoIter<T>>;

    fn into_iter(self) -> Self::IntoIter {
        core::iter::once(self.primary).chain(self.alternatives)
    }
}

impl<T: Display> Display for Choice<T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
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

/// Indexes elements in priority order (`0` is primary, `1..` are alternatives).
///
/// # Panics
///
/// Panics if `index >= self.len()`.
impl<T> core::ops::Index<usize> for Choice<T> {
    type Output = T;

    #[inline]
    fn index(&self, index: usize) -> &Self::Output {
        if index == 0 {
            &self.primary
        } else if let Some(alt) = self.alternatives.get(index - 1) {
            alt
        } else {
            panic!(
                "index out of bounds: the len is {} but the index is {}",
                self.len(),
                index
            );
        }
    }
}

/// Appends items to alternatives, preserving the primary value and order.
impl<T> Extend<T> for Choice<T> {
    #[inline]
    fn extend<I: IntoIterator<Item = T>>(&mut self, iter: I) {
        self.alternatives.extend(iter);
    }
}

/// Appends cloned items to alternatives, preserving the primary value and order.
impl<'a, T: Clone> Extend<&'a T> for Choice<T> {
    #[inline]
    fn extend<I: IntoIterator<Item = &'a T>>(&mut self, iter: I) {
        self.alternatives.extend(iter.into_iter().cloned());
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
    use alloc::string::ToString;
    use alloc::vec;
    use alloc::{format, string::String, vec::Vec};
    use quickcheck_macros::quickcheck;

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

        // Inherent map preserves priority structure
        let mapped = combined.clone().map(|x| x * 10);
        assert_eq!(*mapped.primary(), 10);
        assert_eq!(mapped.alternatives(), &[20, 30, 40, 50]);

        // Iterator fold preserves priority order
        let folded = combined.iter().fold(0, |acc, &x| acc * 10 + x);
        assert_eq!(folded, 12345);
    }

    // `Choice` has no identity element (always non-empty), so only associativity holds.
    // Compiled in `cfg(test)` to run in all CI legs without `--features quickcheck`.
    #[quickcheck]
    fn choice_semigroup_associativity(a: Choice<i32>, b: Choice<i32>, c: Choice<i32>) -> bool {
        a.clone().combine(b.clone()).combine(c.clone()) == a.combine(b.combine(c))
    }

    #[test]
    fn choice_combine_handles_empty_alternatives() {
        let single = Choice::single(0);

        // Primary-only operand must not be dropped and must follow existing alternatives.
        assert_eq!(
            single.clone().combine(Choice::single(1)),
            Choice::new(0, vec![1])
        );
        assert_eq!(
            Choice::new(0, vec![2]).combine(single),
            Choice::new(0, vec![2, 0])
        );
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
        use core::mem::size_of;
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

        // When primary matches, alternatives are filtered without re-evaluating primary
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

    #[test]
    fn test_const_fn_capability() {
        const fn inspect_choice<T>(c: &Choice<T>) -> (&T, &[T], usize, bool) {
            (c.primary(), c.alternatives(), c.len(), c.is_empty())
        }

        let c = Choice::single(42);
        let (p, alts, len, is_empty) = inspect_choice(&c);
        assert_eq!(*p, 42);
        assert_eq!(alts, &[] as &[i32]);
        assert_eq!(len, 1);
        assert!(!is_empty);
    }

    #[test]
    fn test_choice_index() {
        let choice = Choice::new(10, [20, 30, 40]);
        assert_eq!(choice[0], 10);
        assert_eq!(choice[1], 20);
        assert_eq!(choice[2], 30);
        assert_eq!(choice[3], 40);
    }

    #[test]
    #[should_panic(expected = "index out of bounds: the len is 3 but the index is 3")]
    fn test_choice_index_out_of_bounds() {
        let choice = Choice::new(1, [2, 3]);
        let _ = choice[3];
    }

    #[test]
    fn test_choice_extend() {
        let mut choice = Choice::single(1);
        choice.extend([2, 3]);
        assert_eq!(choice.len(), 3);
        assert_eq!(choice[0], 1);
        assert_eq!(choice[1], 2);
        assert_eq!(choice[2], 3);

        let more = [4, 5];
        choice.extend(&more);
        assert_eq!(choice.len(), 5);
        assert_eq!(choice[3], 4);
        assert_eq!(choice[4], 5);
    }
}
