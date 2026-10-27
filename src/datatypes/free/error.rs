use core::fmt::{self, Display};

/// Errors during [`Free`](super::Free) evaluation.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum FreeError<E> {
    /// Error returned by the effect interpreter.
    Interpreter(E),
    /// Type mismatch when downcasting an effect result.
    TypeMismatch {
        /// Expected return type name.
        expected: &'static str,
    },
}

impl<E> FreeError<E> {
    /// Returns `true` if this error is from the interpreter.
    #[inline]
    pub const fn is_interpreter(&self) -> bool {
        matches!(self, FreeError::Interpreter(_))
    }

    /// Returns `true` if this error is a type mismatch.
    #[inline]
    pub const fn is_type_mismatch(&self) -> bool {
        matches!(self, FreeError::TypeMismatch { .. })
    }
}

impl<E: Display> Display for FreeError<E> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            FreeError::Interpreter(e) => write!(f, "Free interpreter error: {e}"),
            FreeError::TypeMismatch { expected } => {
                write!(
                    f,
                    "Free interpretation type mismatch: expected return type {expected}"
                )
            },
        }
    }
}

impl<E: core::error::Error + 'static> core::error::Error for FreeError<E> {
    fn source(&self) -> Option<&(dyn core::error::Error + 'static)> {
        match self {
            FreeError::Interpreter(e) => Some(e),
            FreeError::TypeMismatch { .. } => None,
        }
    }
}
