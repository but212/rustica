//! Unified error types for Rustica datatypes.
//!
//! This module provides standardized error types for datatype operations,
//! enabling safe alternatives to panicking methods and consistent error handling
//! across the library.
//!
//! # Error Types
//!
//! - [`ChoiceError`] - Errors for `Choice<T>` operations
//! - [`EitherError`] - Errors for `Either<L, R>` operations  
//! - [`ValidatedError`] - Errors for `Validated<E, A>` operations
//!
//! # Examples
//!
//! ```rust
//! use rustica::datatypes::error::{ChoiceError, EitherError};
//! use rustica::datatypes::choice::Choice;
//! use rustica::datatypes::either::Either;
//!
//! // Safe alternative access with ChoiceError
//! let choice: Choice<i32> = Choice::new(1, vec![2, 3]);
//! match choice.try_remove_alternative(0) {
//!     Ok(new_choice) => println!("Removed: {:?}", new_choice),
//!     Err(ChoiceError::IndexOutOfBounds { index, len }) => {
//!         println!("Index {} out of bounds (len={})", index, len);
//!     },
//!     Err(ChoiceError::NoAlternatives) => println!("No alternatives"),
//!     _ => {},
//! }
//!
//! let either: Either<&str, i32> = Either::Right(42);
//! match either.try_unwrap_left() {
//!     Ok(left) => println!("Left: {}", left),
//!     Err(_) => println!("Was Right variant"),
//! }
//! ```

use std::fmt::{self, Display};

/// Errors that can occur during `Choice<T>` operations.
///
/// This enum represents error conditions for [`Choice`](super::choice::Choice)
/// operations that would otherwise panic.
///
/// # Examples
///
/// ```rust
/// use rustica::datatypes::error::ChoiceError;
///
/// let err = ChoiceError::NoAlternatives;
/// assert_eq!(
///     err.to_string(),
///     "Choice operation failed: no alternatives available"
/// );
/// ```
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum ChoiceError {
    /// The Choice has no alternatives to operate on.
    ///
    /// This error occurs when attempting operations like `remove_alternative`
    /// or `swap_primary` on a Choice that only has a primary value.
    NoAlternatives,

    /// Index is out of bounds for the alternatives.
    ///
    /// # Fields
    ///
    /// - `index` - The invalid index that was accessed
    /// - `len` - The actual number of alternatives
    IndexOutOfBounds {
        /// The invalid index that was accessed.
        index: usize,
        /// The actual number of alternatives.
        len: usize,
    },

    /// Primary value iterator was empty during flatten operation.
    ///
    /// This error occurs when calling `flatten` on a Choice where
    /// the primary value produces an empty iterator.
    EmptyPrimaryIterator,

    /// The Choice is empty (has no values at all).
    ///
    /// This error occurs when attempting to access values from
    /// an empty Choice created with `Choice::new_empty()`.
    EmptyChoice,
}

impl ChoiceError {
    /// Creates a new `IndexOutOfBounds` error.
    ///
    /// # Arguments
    ///
    /// * `index` - The invalid index that was accessed
    /// * `len` - The actual number of alternatives
    #[inline]
    pub const fn index_out_of_bounds(index: usize, len: usize) -> Self {
        ChoiceError::IndexOutOfBounds { index, len }
    }

    /// Returns `true` if this is a `NoAlternatives` error.
    #[inline]
    pub const fn is_no_alternatives(&self) -> bool {
        matches!(self, ChoiceError::NoAlternatives)
    }

    /// Returns `true` if this is an `IndexOutOfBounds` error.
    #[inline]
    pub const fn is_index_out_of_bounds(&self) -> bool {
        matches!(self, ChoiceError::IndexOutOfBounds { .. })
    }

    /// Returns `true` if this is an `EmptyPrimaryIterator` error.
    #[inline]
    pub const fn is_empty_primary_iterator(&self) -> bool {
        matches!(self, ChoiceError::EmptyPrimaryIterator)
    }

    /// Returns `true` if this is an `EmptyChoice` error.
    #[inline]
    pub const fn is_empty_choice(&self) -> bool {
        matches!(self, ChoiceError::EmptyChoice)
    }
}

impl Display for ChoiceError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ChoiceError::NoAlternatives => {
                write!(f, "Choice operation failed: no alternatives available")
            },
            ChoiceError::IndexOutOfBounds { index, len } => {
                write!(
                    f,
                    "Choice::remove_alternative(): index {} out of bounds for {} alternatives",
                    index, len
                )
            },
            ChoiceError::EmptyPrimaryIterator => {
                write!(
                    f,
                    "Choice::flatten(): primary value produced empty iterator"
                )
            },
            ChoiceError::EmptyChoice => {
                write!(f, "Choice operation failed: choice is empty")
            },
        }
    }
}

impl std::error::Error for ChoiceError {}

/// Errors that can occur during `Either<L, R>` operations.
///
/// This enum represents error conditions for [`Either`](super::either::Either)
/// operations that would otherwise panic.
///
/// # Examples
///
/// ```rust
/// use rustica::datatypes::error::EitherError;
///
/// let err = EitherError::ExpectedLeft;
/// assert_eq!(
///     err.to_string(),
///     "Either::unwrap_left(): called on Right variant"
/// );
/// ```
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub enum EitherError {
    /// Expected Left variant but got Right.
    ///
    /// This error occurs when calling `unwrap_left()`, `left_value()`,
    /// or `left_ref()` on an `Either::Right` value.
    ExpectedLeft,

    /// Expected Right variant but got Left.
    ///
    /// This error occurs when calling `unwrap_right()`, `right_value()`,
    /// `right_ref()`, or `unwrap()` on an `Either::Left` value.
    ExpectedRight,
}

impl EitherError {
    /// Returns `true` if this is an `ExpectedLeft` error.
    #[inline]
    pub const fn is_expected_left(&self) -> bool {
        matches!(self, EitherError::ExpectedLeft)
    }

    /// Returns `true` if this is an `ExpectedRight` error.
    #[inline]
    pub const fn is_expected_right(&self) -> bool {
        matches!(self, EitherError::ExpectedRight)
    }
}

impl Display for EitherError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            EitherError::ExpectedLeft => {
                write!(f, "Either::unwrap_left(): called on Right variant")
            },
            EitherError::ExpectedRight => {
                write!(f, "Either::unwrap_right(): called on Left variant")
            },
        }
    }
}

impl std::error::Error for EitherError {}

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
    use super::{ChoiceError, EitherError, ValidatedError};

    #[test]
    fn test_choice_error_display() {
        assert_eq!(
            ChoiceError::NoAlternatives.to_string(),
            "Choice operation failed: no alternatives available"
        );
        assert_eq!(
            ChoiceError::index_out_of_bounds(5, 3).to_string(),
            "Choice::remove_alternative(): index 5 out of bounds for 3 alternatives"
        );
        assert_eq!(
            ChoiceError::EmptyPrimaryIterator.to_string(),
            "Choice::flatten(): primary value produced empty iterator"
        );
        assert_eq!(
            ChoiceError::EmptyChoice.to_string(),
            "Choice operation failed: choice is empty"
        );
    }

    #[test]
    fn test_either_error_display() {
        assert_eq!(
            EitherError::ExpectedLeft.to_string(),
            "Either::unwrap_left(): called on Right variant"
        );
        assert_eq!(
            EitherError::ExpectedRight.to_string(),
            "Either::unwrap_right(): called on Left variant"
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
        assert!(ChoiceError::NoAlternatives.is_no_alternatives());
        assert!(!ChoiceError::NoAlternatives.is_index_out_of_bounds());
        let idx_err = ChoiceError::index_out_of_bounds(1, 2);
        assert!(idx_err.is_index_out_of_bounds());
        assert!(!idx_err.is_no_alternatives());
        assert!(ChoiceError::EmptyPrimaryIterator.is_empty_primary_iterator());
        assert!(ChoiceError::EmptyChoice.is_empty_choice());
    }

    #[test]
    fn test_either_error_predicates() {
        assert!(EitherError::ExpectedLeft.is_expected_left());
        assert!(!EitherError::ExpectedLeft.is_expected_right());
        assert!(EitherError::ExpectedRight.is_expected_right());
        assert!(!EitherError::ExpectedRight.is_expected_left());
    }

    #[test]
    fn test_validated_error_predicates() {
        assert!(ValidatedError::ExpectedValid.is_expected_valid());
        assert!(!ValidatedError::ExpectedValid.is_expected_invalid());
        assert!(ValidatedError::ExpectedInvalid.is_expected_invalid());
        assert!(!ValidatedError::ExpectedInvalid.is_expected_valid());
    }
}
