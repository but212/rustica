//! Core implementation of the `Validated` data type.
//!
//! This module provides the fundamental `Validated<E, A>` type for accumulating
//! validation errors, along with its associated methods and helper types.

use crate::datatypes::error::ValidatedError;
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
    pub fn try_from_slice(slice: &[E]) -> Option<Self>
    where
        E: Clone,
    {
        (!slice.is_empty()).then_some(Self(slice.to_vec().into()))
    }

    /// Converts the non-empty error collection into a regular vector.
    #[inline]
    pub fn into_vec(self) -> ErrorVec<E> {
        self.0
    }

    /// Returns a slice over the errors.
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
/// - Zero-copy error transfer via `extend` when consuming `Validated` instances
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

    /// Extends the accumulator with errors, avoiding clones.
    ///
    /// This method is optimized for consuming `Validated::Invalid` instances
    /// by draining their error collections directly into the accumulator.
    ///
    /// # Arguments
    ///
    /// * `errors` - The error collection to drain and append
    #[inline]
    pub(crate) fn extend<I: IntoIterator<Item = E>>(&mut self, errors: I) {
        self.buffer.extend(errors);
    }
}

impl<E> Extend<E> for ErrorAccumulator<E> {
    #[inline]
    fn extend<I: IntoIterator<Item = E>>(&mut self, iter: I) {
        self.buffer.extend(iter);
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

    // --- Value Extraction and Safe Unwrapping ---

    /// Consumes `self` and returns `Ok(A)` if `Valid(A)`, or `Err(NonEmptyErrors<E>)` if `Invalid(errors)`.
    #[inline]
    pub fn into_value(self) -> Result<A, NonEmptyErrors<E>> {
        match self {
            Validated::Valid(a) => Ok(a),
            Validated::Invalid(es) => Err(es),
        }
    }

    /// Consumes `self` and returns `Ok(NonEmptyErrors<E>)` if `Invalid(errors)`, or `Err(A)` if `Valid(A)`.
    #[inline]
    pub fn into_error_payload(self) -> Result<NonEmptyErrors<E>, A> {
        match self {
            Validated::Valid(a) => Err(a),
            Validated::Invalid(es) => Ok(es),
        }
    }

    /// Safely extracts the valid value.
    ///
    /// This is the safe alternative to `unwrap()` that returns
    /// a proper error type instead of panicking.
    #[inline]
    pub fn try_unwrap(self) -> Result<A, ValidatedError> {
        match self {
            Validated::Valid(a) => Ok(a),
            Validated::Invalid(_) => Err(ValidatedError::ExpectedValid),
        }
    }

    /// Safely extracts the error collection.
    ///
    /// This is the safe alternative to `unwrap_invalid()` that returns
    /// a proper error type instead of panicking.
    #[inline]
    pub fn try_unwrap_invalid(self) -> Result<NonEmptyErrors<E>, ValidatedError> {
        match self {
            Validated::Invalid(es) => Ok(es),
            Validated::Valid(_) => Err(ValidatedError::ExpectedInvalid),
        }
    }

    /// Safely gets a reference to the valid value.
    #[inline]
    pub fn try_valid_ref(&self) -> Result<&A, ValidatedError> {
        match self {
            Validated::Valid(a) => Ok(a),
            Validated::Invalid(_) => Err(ValidatedError::ExpectedValid),
        }
    }

    /// Unwraps a valid value or panics.
    ///
    /// # Panics
    ///
    /// Panics if this is invalid.
    #[inline]
    pub fn unwrap(self) -> A
    where
        E: std::fmt::Debug,
    {
        match self {
            Validated::Valid(value) => value,
            Validated::Invalid(e) => {
                panic!("Called Validated::unwrap() on an Invalid value: {e:?}")
            },
        }
    }

    /// Unwraps a valid value or returns a default.
    #[inline]
    pub fn unwrap_or(self, default: A) -> A {
        match self {
            Validated::Valid(x) => x,
            _ => default,
        }
    }

    /// Unwraps an invalid error collection or panics with a message.
    ///
    /// # Panics
    ///
    /// Panics if this is `Valid`.
    #[inline]
    pub fn unwrap_invalid(self) -> NonEmptyErrors<E>
    where
        A: std::fmt::Debug,
    {
        match self {
            Validated::Invalid(es) => es,
            Validated::Valid(a) => {
                panic!("Called Validated::unwrap_invalid() on a Valid value: {a:?}")
            },
        }
    }

    // --- Option Views and Conversions ---

    /// Returns a reference to the valid value as an Option, without cloning.
    #[inline]
    pub fn as_option(&self) -> Option<&A> {
        match self {
            Validated::Valid(x) => Some(x),
            Validated::Invalid(_) => None,
        }
    }

    /// Converts to Option by consuming self, without cloning.
    #[inline]
    pub fn into_option(self) -> Option<A> {
        match self {
            Validated::Valid(x) => Some(x),
            Validated::Invalid(_) => None,
        }
    }

    /// Converts to Option by cloning the inner valid value.
    #[inline]
    pub fn to_option(&self) -> Option<A>
    where
        A: Clone,
    {
        match self {
            Validated::Valid(x) => Some(x.clone()),
            _ => None,
        }
    }

    // --- Standard Conversions ---

    /// Converts to fail-fast `Result`, explicitly keeping only the first error.
    #[inline]
    pub fn into_result_first_error(self) -> Result<A, E> {
        match self {
            Self::Valid(value) => Ok(value),
            Self::Invalid(errors) => Err(errors
                .into_iter()
                .next()
                .expect("Validated errors cannot be empty")),
        }
    }

    /// Constructs a `Validated` from an `Option`, using the provided error when `None`.
    #[inline]
    pub fn from_option(option: Option<A>, error: E) -> Self {
        match option {
            Some(value) => Self::Valid(value),
            None => Self::invalid(error),
        }
    }

    /// Constructs a `Validated` from an `Option`, generating an error via a closure when `None`.
    #[inline]
    pub fn from_option_with<F>(option: Option<A>, error_fn: F) -> Self
    where
        F: FnOnce() -> E,
    {
        match option {
            Some(value) => Self::Valid(value),
            None => Self::invalid(error_fn()),
        }
    }
}

impl<E, A> From<Result<A, E>> for Validated<E, A> {
    #[inline]
    fn from(result: Result<A, E>) -> Self {
        match result {
            Ok(value) => Self::Valid(value),
            Err(error) => Self::invalid(error),
        }
    }
}

impl<E: Clone, A: Clone> From<&Result<A, E>> for Validated<E, A> {
    #[inline]
    fn from(result: &Result<A, E>) -> Self {
        result.clone().into()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn non_empty_errors_fallible_construction() {
        assert_eq!(NonEmptyErrors::<String>::try_from_iter(Vec::new()), None);

        let errors = NonEmptyErrors::try_from_iter(["first".to_string(), "second".to_string()])
            .expect("non-empty input should construct errors");
        assert_eq!(errors.as_slice(), ["first", "second"]);
    }

    #[test]
    fn test_safe_unwrapping() {
        let valid: Validated<&str, i32> = Validated::valid(42);
        assert_eq!(valid.try_valid_ref(), Ok(&42));
        assert_eq!(valid.clone().try_unwrap(), Ok(42));
        assert_eq!(
            valid.try_unwrap_invalid(),
            Err(ValidatedError::ExpectedInvalid)
        );

        let invalid: Validated<&str, i32> = Validated::invalid("err");
        assert_eq!(invalid.try_valid_ref(), Err(ValidatedError::ExpectedValid));
        assert_eq!(
            invalid.clone().try_unwrap(),
            Err(ValidatedError::ExpectedValid)
        );
        assert!(invalid.try_unwrap_invalid().is_ok());
    }

    #[test]
    #[should_panic(expected = "Called Validated::unwrap() on an Invalid value:")]
    fn unwrap_rejects_invalid_values() {
        Validated::<&str, i32>::invalid("error").unwrap();
    }

    #[test]
    #[should_panic(expected = "Called Validated::unwrap_invalid() on a Valid value:")]
    fn unwrap_invalid_rejects_valid_values() {
        Validated::<&str, i32>::valid(42).unwrap_invalid();
    }

    #[test]
    fn test_option_and_result_conversions() {
        let valid: Validated<&str, i32> = Ok(42).into();
        assert_eq!(valid.as_option(), Some(&42));
        assert_eq!(valid.clone().into_option(), Some(42));
        assert_eq!(valid.to_option(), Some(42));
        assert_eq!(valid.into_result_first_error(), Ok(42));

        let res: Result<i32, &str> = Err("err");
        let invalid = Validated::from(&res);
        assert_eq!(invalid.as_option(), None);
        assert_eq!(invalid.into_result_first_error(), Err("err"));

        let from_some = Validated::from_option(Some(10), "err");
        assert_eq!(from_some, Validated::valid(10));
        let from_none: Validated<&str, i32> = Validated::from_option_with(None, || "dynamic_err");
        assert_eq!(from_none, Validated::invalid("dynamic_err"));
    }
}
