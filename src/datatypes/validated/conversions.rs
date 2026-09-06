use crate::datatypes::validated::Validated;

impl<E, A> From<Result<A, E>> for Validated<E, A> {
    fn from(result: Result<A, E>) -> Self {
        match result {
            Ok(value) => Self::Valid(value),
            Err(error) => Self::invalid(error),
        }
    }
}

impl<E: Clone, A: Clone> From<&Result<A, E>> for Validated<E, A> {
    fn from(result: &Result<A, E>) -> Self {
        result.clone().into()
    }
}

impl<E, A> Validated<E, A> {
    /// Converts to fail-fast `Result`, explicitly keeping only the first error.
    pub fn into_result_first_error(self) -> Result<A, E> {
        match self {
            Self::Valid(value) => Ok(value),
            Self::Invalid(errors) => Err(errors
                .into_iter()
                .next()
                .expect("Validated errors cannot be empty")),
        }
    }

    pub fn from_option(option: Option<A>, error: E) -> Self {
        match option {
            Some(value) => Self::Valid(value),
            None => Self::invalid(error),
        }
    }

    /// Creates a Validated from an Option, consuming both.
    #[inline]
    #[deprecated(since = "0.15.0", note = "use `Validated::from_option` instead")]
    pub fn from_option_owned(option: Option<A>, error: E) -> Self {
        Self::from_option(option, error)
    }

    pub fn from_option_with<F>(option: Option<A>, error_fn: F) -> Self
    where
        F: FnOnce() -> E,
    {
        match option {
            Some(value) => Self::Valid(value),
            None => Self::invalid(error_fn()),
        }
    }

    /// Creates a Validated from an Option using a function to generate the error, consuming both.
    #[inline]
    #[deprecated(since = "0.15.0", note = "use `Validated::from_option_with` instead")]
    pub fn from_option_with_owned<F>(option: Option<A>, error_fn: F) -> Self
    where
        F: FnOnce() -> E,
    {
        Self::from_option_with(option, error_fn)
    }
}

#[cfg(test)]
mod unit_tests {
    use super::Validated;

    #[test]
    fn conversions_accept_non_clone_values() {
        struct NoClone(&'static str);
        let converted: Result<NoClone, NoClone> =
            Validated::valid(NoClone("valid")).into_result_first_error();
        assert!(matches!(converted, Ok(NoClone("valid"))));
        assert!(matches!(
            Validated::<NoClone, NoClone>::from(Ok(NoClone("result"))),
            Validated::Valid(NoClone("result"))
        ));
    }
}

#[cfg(test)]
mod tests {
    use super::Validated;

    #[test]
    fn result_conversion_uses_from_and_names_the_lossy_boundary() {
        let valid: Validated<&str, i32> = Ok(42).into();
        assert_eq!(valid.into_result_first_error(), Ok(42));

        let result: Result<i32, &str> = Err("first");
        let invalid = Validated::from(&result);
        assert_eq!(invalid.into_result_first_error(), Err("first"));

        let accumulated: Validated<&str, ()> = Validated::invalid_many(["first", "second"]);
        assert_eq!(accumulated.into_result_first_error(), Err("first"));

        #[allow(deprecated)]
        let from_opt: Validated<&str, i32> = Validated::from_option_owned(Some(10), "err");
        assert_eq!(from_opt, Validated::valid(10));

        #[allow(deprecated)]
        let from_opt_with: Validated<&str, i32> =
            Validated::from_option_with_owned(None, || "err_with");
        assert_eq!(from_opt_with, Validated::invalid("err_with"));
    }
}
