//! # MonadPlus
//!
//! Deprecated in 0.15.0: Use `Alternative` (`empty_alt` and `alt`) instead.

use std::fmt::Debug;

use crate::traits::monad::Monad;

/// A trait for monads that support choice operations, extending the basic Monad trait.
///
/// Deprecated in 0.15.0 in favor of `Alternative` (`empty_alt` and `alt`).
#[deprecated(
    since = "0.15.0",
    note = "use `Alternative` (`empty_alt` and `alt`) instead"
)]
pub trait MonadPlus: Monad {
    /// Creates a monad that represents an empty or failed computation.
    fn mzero<T: Clone>() -> Self::Output<T>;

    /// Combines two monads, representing a choice between them.
    fn mplus(&self, other: &Self) -> Self;

    /// Combines two monads, consuming both.
    fn mplus_owned(self, other: Self) -> Self
    where
        Self: Sized;
}

#[allow(deprecated)]
impl<T: Clone> MonadPlus for Option<T> {
    fn mzero<U: Clone>() -> Self::Output<U> {
        None
    }

    fn mplus(&self, other: &Self) -> Self {
        match self {
            Some(_) => self.clone(),
            None => other.clone(),
        }
    }

    fn mplus_owned(self, other: Self) -> Self {
        match self {
            Some(_) => self,
            None => other,
        }
    }
}

#[allow(deprecated)]
impl<T: Clone, E: Clone + Debug + Default> MonadPlus for Result<T, E> {
    fn mzero<U: Clone>() -> Self::Output<U> {
        Err(E::default())
    }

    fn mplus(&self, other: &Self) -> Self {
        match self {
            Ok(_) => self.clone(),
            Err(_) => other.clone(),
        }
    }

    fn mplus_owned(self, other: Self) -> Self {
        match self {
            Ok(_) => self,
            Err(_) => other,
        }
    }
}

#[cfg(test)]
mod tests {
    #[allow(deprecated)]
    use super::MonadPlus;

    #[test]
    fn monad_plus_option_works() {
        #[allow(deprecated)]
        let zero: Option<i32> = Option::<i32>::mzero();
        assert_eq!(zero, None);

        #[allow(deprecated)]
        let a = Some(1);
        #[allow(deprecated)]
        let b = Some(2);
        assert_eq!(a.mplus(&b), Some(1));
        assert_eq!(None::<i32>.mplus(&b), Some(2));
        assert_eq!(a.mplus_owned(b), Some(1));
    }

    #[test]
    fn monad_plus_result_works() {
        #[allow(deprecated)]
        let zero: Result<i32, String> = Result::<i32, String>::mzero();
        assert_eq!(zero, Err(String::new()));

        #[allow(deprecated)]
        let ok: Result<i32, String> = Ok(1);
        #[allow(deprecated)]
        let err: Result<i32, String> = Err("e".to_string());
        assert_eq!(err.clone().mplus(&ok), Ok(1));
        assert_eq!(ok.clone().mplus_owned(err), Ok(1));
    }
}
