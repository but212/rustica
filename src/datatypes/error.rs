//! Unified error types for Rustica datatypes.
//!
//! This module provides standardized error types for datatype operations,
//! enabling safe alternatives to panicking methods and consistent error handling
//! across the library.
//!
//! # Error Types
//!
//! - [`ChoiceError`] - Errors for `Choice<T>` operations
//! - [`ValidatedError`] - Errors for `Validated<E, A>` operations
//!
//! # Examples
//!
//! ```rust
//! use rustica::datatypes::error::ChoiceError;
//! use rustica::datatypes::choice::Choice;
//!
//! let choice: Choice<Vec<i32>> = Choice::single(vec![]);
//! assert_eq!(choice.try_flatten(), Err(ChoiceError::EmptyPrimaryIterator));
//! ```

use std::fmt::{self, Display};

/// Errors that can occur during `Choice<T>` operations.
///
/// This enum represents error conditions for [`Choice`](super::choice::Choice)
/// operations that would otherwise panic.
///
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum ChoiceError {
    /// Primary value iterator was empty during flatten operation.
    ///
    /// This error occurs when calling `flatten` on a Choice where
    /// the primary value produces an empty iterator.
    EmptyPrimaryIterator,

    /// Input contained no values when constructing a `Choice`.
    EmptyInput,
}

impl ChoiceError {
    /// Returns `true` if this is an `EmptyPrimaryIterator` error.
    #[inline]
    pub const fn is_empty_primary_iterator(&self) -> bool {
        matches!(self, ChoiceError::EmptyPrimaryIterator)
    }

    /// Returns `true` if this is an `EmptyInput` error.
    #[inline]
    pub const fn is_empty_input(&self) -> bool {
        matches!(self, ChoiceError::EmptyInput)
    }
}

impl Display for ChoiceError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ChoiceError::EmptyPrimaryIterator => write!(
                f,
                "Choice::flatten(): primary value produced empty iterator"
            ),
            ChoiceError::EmptyInput => write!(f, "Choice construction requires at least one value"),
        }
    }
}

impl std::error::Error for ChoiceError {}

/// Errors that can occur during `Validated<E, A>` operations.
///
/// This enum represents error conditions for [`Validated`](super::validated::Validated)
/// operations that would otherwise panic.
///
/// # Examples
///
/// ```rust
/// use rustica::datatypes::error::ValidatedError;
///
/// let err = ValidatedError::ExpectedValid;
/// assert_eq!(
///     err.to_string(),
///     "Validated::unwrap(): called on Invalid variant"
/// );
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum ValidatedError {
    /// Expected Valid variant but got Invalid.
    ///
    /// This error occurs when calling `unwrap()` or `unwrap_owned()`
    /// on a `Validated::Invalid` value.
    ExpectedValid,

    /// Expected Invalid variant but got Valid.
    ///
    /// This error occurs when calling `unwrap_invalid_owned()`
    /// on a `Validated::Valid` value.
    ExpectedInvalid,
}

impl ValidatedError {
    /// Returns `true` if this is an `ExpectedValid` error.
    #[inline]
    pub const fn is_expected_valid(&self) -> bool {
        matches!(self, ValidatedError::ExpectedValid)
    }

    /// Returns `true` if this is an `ExpectedInvalid` error.
    #[inline]
    pub const fn is_expected_invalid(&self) -> bool {
        matches!(self, ValidatedError::ExpectedInvalid)
    }
}

impl Display for ValidatedError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ValidatedError::ExpectedValid => {
                write!(f, "Validated::unwrap(): called on Invalid variant")
            },
            ValidatedError::ExpectedInvalid => {
                write!(f, "Validated::unwrap_invalid(): called on Valid variant")
            },
        }
    }
}

impl std::error::Error for ValidatedError {}

#[cfg(test)]
mod tests {
    use super::{ChoiceError, ValidatedError};

    #[test]
    fn test_choice_error_display() {
        assert_eq!(
            ChoiceError::EmptyPrimaryIterator.to_string(),
            "Choice::flatten(): primary value produced empty iterator"
        );
        assert_eq!(
            ChoiceError::EmptyInput.to_string(),
            "Choice construction requires at least one value"
        );
    }

    #[test]
    fn test_validated_error_display() {
        assert_eq!(
            ValidatedError::ExpectedValid.to_string(),
            "Validated::unwrap(): called on Invalid variant"
        );
        assert_eq!(
            ValidatedError::ExpectedInvalid.to_string(),
            "Validated::unwrap_invalid(): called on Valid variant"
        );
    }

    #[test]
    fn test_choice_error_predicates() {
        assert!(ChoiceError::EmptyPrimaryIterator.is_empty_primary_iterator());
    }

    #[test]
    fn test_validated_error_predicates() {
        assert!(ValidatedError::ExpectedValid.is_expected_valid());
        assert!(!ValidatedError::ExpectedValid.is_expected_invalid());
        assert!(ValidatedError::ExpectedInvalid.is_expected_invalid());
        assert!(!ValidatedError::ExpectedInvalid.is_expected_valid());
    }
}
