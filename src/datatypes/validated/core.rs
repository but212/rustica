//! Core implementation of the `Validated` data type.
//!
//! This module provides the fundamental `Validated<E, A>` type for accumulating
//! validation errors, along with its associated methods and helper types.

use smallvec::{SmallVec, smallvec};

/// A non-empty collection of validation errors.
///
/// The private buffer prevents callers from constructing or clearing an empty
/// error collection while retaining the compact `SmallVec` representation.
#[derive(Clone, PartialEq, PartialOrd, Eq, Ord, Debug, Hash)]
pub struct NonEmptyErrors<E>(ErrorVec<E>);

impl<E> NonEmptyErrors<E> {
    #[inline]
    pub fn new(first: E) -> Self {
        Self(smallvec![first])
    }

    #[inline]
    pub(crate) fn try_from_vec(errors: ErrorVec<E>) -> Option<Self> {
        (!errors.is_empty()).then_some(Self(errors))
    }

    /// Creates a non-empty error collection from an iterator.
    ///
    /// Returns `None` when the iterator yields no errors.
    #[inline]
    pub fn try_from_iter<I>(iter: I) -> Option<Self>
    where
        I: IntoIterator<Item = E>,
    {
        let mut iter = iter.into_iter();
        let first = iter.next()?;
        Some(Self::from_first_and_iter(first, iter))
    }

    #[inline]
    pub(crate) fn from_first_and_iter<I>(first: E, rest: I) -> Self
    where
        I: IntoIterator<Item = E>,
    {
        let mut errors = ErrorVec::new();
        errors.push(first);
        errors.extend(rest);
        Self(errors)
    }

    #[inline]
    pub(crate) fn into_vec(self) -> ErrorVec<E> {
        self.0
    }

    #[inline]
    pub fn as_slice(&self) -> &[E] {
        &self.0
    }

    #[inline]
    pub fn iter(&self) -> std::slice::Iter<'_, E> {
        self.0.iter()
    }

    #[inline]
    pub fn iter_mut(&mut self) -> std::slice::IterMut<'_, E> {
        self.0.iter_mut()
    }

    #[inline]
    pub fn len(&self) -> usize {
        self.0.len()
    }

    /// Returns whether the error collection is empty.
    ///
    /// This is always `false`: constructing `NonEmptyErrors` requires at
    /// least one error, and its mutating methods preserve that invariant.
    #[inline]
    pub fn is_empty(&self) -> bool {
        false
    }

    #[inline]
    pub fn push(&mut self, error: E) {
        self.0.push(error);
    }

    #[inline]
    pub fn extend<I: IntoIterator<Item = E>>(&mut self, errors: I) {
        self.0.extend(errors);
    }
}

impl<E> std::ops::Deref for NonEmptyErrors<E> {
    type Target = [E];

    fn deref(&self) -> &Self::Target {
        self.as_slice()
    }
}

impl<E: PartialEq> PartialEq<ErrorVec<E>> for NonEmptyErrors<E> {
    fn eq(&self, other: &ErrorVec<E>) -> bool {
        self.as_slice() == other.as_slice()
    }
}

impl<E> IntoIterator for NonEmptyErrors<E> {
    type Item = E;
    type IntoIter = std::vec::IntoIter<E>;

    fn into_iter(self) -> Self::IntoIter {
        self.0.into_vec().into_iter()
    }
}

#[cfg(feature = "serde")]
impl<E: serde::Serialize> serde::Serialize for NonEmptyErrors<E> {
    fn serialize<S: serde::Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        self.0.serialize(serializer)
    }
}

#[cfg(feature = "serde")]
impl<'de, E: serde::Deserialize<'de>> serde::Deserialize<'de> for NonEmptyErrors<E> {
    fn deserialize<D: serde::Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        let errors = ErrorVec::<E>::deserialize(deserializer)?;
        if errors.is_empty() {
            return Err(serde::de::Error::custom("Validated errors cannot be empty"));
        }
        Ok(Self(errors))
    }
}

/// Type alias for the internal error collection.
///
/// Uses `SmallVec` with inline capacity of 4 to optimize for the common case
/// of few errors while still supporting larger error collections efficiently.
pub(crate) type ErrorVec<E> = SmallVec<[E; 4]>;

/// Internal helper for efficiently accumulating validation errors.
///
/// `ErrorAccumulator` provides a unified interface for collecting errors from
/// multiple `Validated` instances, with optimized paths for both owned and
/// borrowed error collections.
///
/// # Performance Characteristics
///
/// - Stack-allocated for up to 4 errors (via `SmallVec`)
/// - Heap allocation only when exceeding inline capacity
/// - Zero-copy error transfer via `extend_owned` when consuming `Validated` instances
/// - Efficient cloning path via `extend_cloned` for borrowed references
///
/// # Type Parameters
///
/// * `E` - The error type being accumulated
pub(crate) struct ErrorAccumulator<E> {
    /// Internal buffer storing accumulated errors.
    buffer: ErrorVec<E>,
}

impl<E> ErrorAccumulator<E> {
    /// Creates a new empty error accumulator.
    ///
    /// The accumulator starts with inline storage for up to 4 errors.
    #[inline]
    pub(crate) fn new() -> Self {
        Self {
            buffer: ErrorVec::new(),
        }
    }

    /// Creates a new error accumulator with pre-allocated capacity.
    ///
    /// Use this when you know approximately how many errors to expect,
    /// to avoid reallocation during accumulation.
    ///
    /// # Arguments
    ///
    /// * `capacity` - The number of errors to pre-allocate space for
    #[inline]
    pub(crate) fn with_capacity(capacity: usize) -> Self {
        Self {
            buffer: ErrorVec::with_capacity(capacity),
        }
    }

    #[inline]
    pub(crate) fn into_non_empty(self) -> Option<NonEmptyErrors<E>> {
        NonEmptyErrors::try_from_vec(self.buffer)
    }

    #[inline]
    pub(crate) fn push(&mut self, error: E) {
        self.buffer.push(error);
    }

    /// Extends the accumulator with owned errors, avoiding clones.
    ///
    /// This method is optimized for consuming `Validated::Invalid` instances
    /// by draining their error collections directly into the accumulator.
    ///
    /// # Arguments
    ///
    /// * `errors` - The error collection to drain and append
    #[inline]
    pub(crate) fn extend_owned<I: IntoIterator<Item = E>>(&mut self, errors: I) {
        self.buffer.extend(errors);
    }
}

/// A validation type that can accumulate multiple errors.
///
/// Validated<E, A> represents either a valid value of type A or a collection of
/// errors of type E. Unlike Result, which fails fast on the first error,
/// Validated can collect multiple errors during validation.
#[derive(Clone, PartialEq, PartialOrd, Eq, Ord, Debug, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum Validated<E, A> {
    /// Represents a valid value of type A.
    Valid(A),
    /// Represents an invalid state with multiple errors of type E.
    /// Uses SmallVec for better performance with small error counts.
    Invalid(NonEmptyErrors<E>),
}

impl<E, A> Validated<E, A> {
    /// Returns whether this `Validated` is valid.
    #[inline]
    pub fn is_valid(&self) -> bool {
        matches!(self, Validated::Valid(_))
    }

    /// Returns whether this `Validated` is invalid.
    #[inline]
    pub fn is_invalid(&self) -> bool {
        !self.is_valid()
    }

    /// Creates a new valid instance.
    #[inline]
    pub fn valid(x: A) -> Self {
        Validated::Valid(x)
    }

    /// Creates a new invalid instance with a single error.
    #[inline]
    pub fn invalid(e: E) -> Self {
        Validated::Invalid(NonEmptyErrors::new(e))
    }

    /// Creates a new invalid instance with multiple errors from a collection.
    #[inline]
    pub fn invalid_many<I>(errors: I) -> Self
    where
        I: IntoIterator<Item = E>,
    {
        let mut iter = errors.into_iter();
        let Some(first) = iter.next() else {
            panic!("Validated::invalid_many requires at least one error")
        };
        Validated::Invalid(NonEmptyErrors::from_first_and_iter(first, iter))
    }

    /// Attempts to create an invalid value, returning `None` for an empty iterator.
    #[inline]
    pub fn try_invalid_many<I>(errors: I) -> Option<Self>
    where
        I: IntoIterator<Item = E>,
    {
        let mut iter = errors.into_iter();
        let first = iter.next()?;
        Some(Validated::Invalid(NonEmptyErrors::from_first_and_iter(
            first, iter,
        )))
    }

    #[inline]
    pub(crate) fn invalid_from_accumulator(accumulator: ErrorAccumulator<E>) -> Self {
        Validated::Invalid(
            accumulator
                .into_non_empty()
                .expect("Validated errors cannot be empty"),
        )
    }
}
