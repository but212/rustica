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

    pub fn from_option(option: &Option<A>, error: &E) -> Self
    where
        A: Clone,
        E: Clone,
    {
        match option {
            Some(value) => Self::Valid(value.clone()),
            None => Self::invalid(error.clone()),
        }
    }

    pub fn from_option_owned(option: Option<A>, error: E) -> Self {
        match option {
            Some(value) => Self::Valid(value),
            None => Self::invalid(error),
        }
    }

    pub fn from_option_with<F>(option: &Option<A>, error_fn: &F) -> Self
    where
        F: Fn() -> E,
        A: Clone,
    {
        match option {
            Some(value) => Self::Valid(value.clone()),
            None => Self::invalid(error_fn()),
        }
    }

    pub fn from_option_with_owned<F>(option: Option<A>, error_fn: F) -> Self
    where
        F: FnOnce() -> E,
    {
        match option {
            Some(value) => Self::Valid(value),
            None => Self::invalid(error_fn()),
        }
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
    }
}
