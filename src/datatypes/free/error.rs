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
    pub const fn is_interpreter(&self) -> bool {
        matches!(self, Self::Interpreter(_))
    }

    /// Returns `true` if this error is a type mismatch.
    pub const fn is_type_mismatch(&self) -> bool {
        matches!(self, Self::TypeMismatch { .. })
    }
}

impl<E: Display> Display for FreeError<E> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Interpreter(e) => write!(f, "Free interpreter error: {e}"),
            Self::TypeMismatch { expected } => {
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
            Self::Interpreter(e) => Some(e),
            Self::TypeMismatch { .. } => None,
        }
    }
}

#[cfg(test)]
mod tests {
    use alloc::string::ToString;

    use super::*;

    #[test]
    fn test_free_error() {
        let err: FreeError<&str> = FreeError::Interpreter("boom");
        assert!(err.is_interpreter());
        assert!(!err.is_type_mismatch());
        assert_eq!(err.to_string(), "Free interpreter error: boom");

        let mismatch: FreeError<&str> = FreeError::TypeMismatch { expected: "i32" };
        assert!(mismatch.is_type_mismatch());
        assert!(!mismatch.is_interpreter());
        assert_eq!(
            mismatch.to_string(),
            "Free interpretation type mismatch: expected return type i32"
        );
    }
}
