//! Core implementation of the `Validated` data type.
//!
//! This module provides the fundamental `Validated<E, A>` type for accumulating
//! validation errors, along with its associated methods and helper types.

use smallvec::{SmallVec, smallvec};

/// Type alias for the internal error collection.
///
/// Uses `SmallVec` with inline capacity of 4 to optimize for the common case
/// of few errors while still supporting larger error collections efficiently.
pub type ErrorVec<E> = SmallVec<[E; 4]>;

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
    pub(crate) buffer: ErrorVec<E>,
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

    /// Consumes the accumulator and returns the collected errors.
    ///
    /// This transfers ownership of the error collection without cloning.
    #[inline]
    pub(crate) fn into_inner(self) -> ErrorVec<E> {
        self.buffer
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
    pub(crate) fn extend_owned(&mut self, mut errors: ErrorVec<E>) {
        self.buffer.extend(errors.drain(..));
    }
}

impl<E: Clone> ErrorAccumulator<E> {
    /// Extends the accumulator by cloning errors from a borrowed collection.
    ///
    /// This method is used when working with `&Validated` references where
    /// the original error collection cannot be consumed. It pre-reserves
    /// capacity to minimize reallocations.
    ///
    /// # Arguments
    ///
    /// * `errors` - The error collection to clone from
    #[inline]
    pub(crate) fn extend_cloned(&mut self, errors: &ErrorVec<E>) {
        if errors.is_empty() {
            return;
        }
        self.buffer.reserve(errors.len());
        self.buffer.extend(errors.iter().cloned());
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
    Invalid(ErrorVec<E>),
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
        Validated::Invalid(smallvec![e])
    }

    /// Creates a new invalid instance with multiple errors from a collection.
    #[inline]
    pub fn invalid_many<I>(errors: I) -> Self
    where
        I: IntoIterator<Item = E>,
    {
        let iter = errors.into_iter();
        let (lower, upper) = iter.size_hint();
        match upper {
            Some(exact) if exact == lower => {
                if exact <= 4 {
                    Validated::Invalid(iter.collect())
                } else {
                    let mut vec = SmallVec::with_capacity(exact);
                    vec.extend(iter);
                    Validated::Invalid(vec)
                }
            },
            Some(upper_bound) => {
                if upper_bound <= 4 {
                    Validated::Invalid(iter.collect())
                } else {
                    let mut vec = SmallVec::with_capacity(upper_bound);
                    vec.extend(iter);
                    Validated::Invalid(vec)
                }
            },
            None => {
                if lower <= 4 {
                    Validated::Invalid(iter.collect())
                } else {
                    let mut vec = SmallVec::with_capacity(lower);
                    vec.extend(iter);
                    Validated::Invalid(vec)
                }
            },
        }
    }

    /// Creates a new invalid instance with multiple errors from a collection.
    /// Panics if empty.
    #[inline]
    pub fn invalid_vec<I>(errors: I) -> Self
    where
        I: IntoIterator<Item = E>,
    {
        let mut iter = errors.into_iter();
        if let Some(first) = iter.next() {
            let (lower, _upper) = iter.size_hint();
            let mut vec: ErrorVec<E> = SmallVec::with_capacity(lower.saturating_add(1));
            vec.push(first);
            vec.extend(iter);
            Validated::Invalid(vec)
        } else {
            panic!("Validated::invalid_vec requires at least one error")
        }
    }
}
