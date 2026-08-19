use crate::datatypes::validated::Validated;

impl<E, A> Validated<E, A> {
    /// Attempts recovery for accumulated errors, in order.
    ///
    /// This is a `Validated`-specific variant of recovery for the case where there may be
    /// multiple accumulated errors.
    ///
    /// Unlike `ErrorOps::recover` (which recovers from a single error in fail-fast types like
    /// `Result`), this method feeds each accumulated error to the recovery function.
    ///
    /// **Important**: errors are processed left-to-right, and if any recovery returns
    /// `Validated::Valid(v)`, evaluation stops early and that `Valid(v)` is returned.
    /// If no recovery returns `Valid`, all errors produced by recoveries are accumulated.
    ///
    /// # Type Parameters
    ///
    /// * `F`: Recovery function type
    ///
    /// # Arguments
    ///
    /// * `recovery`: Function applied to each error
    ///
    /// # Returns
    ///
    /// - If any recovery yields `Valid(v)`, returns the first such `Valid(v)` (early exit)
    /// - Otherwise, returns `Invalid` with all errors produced by the recovery function
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::validated::Validated;
    ///
    /// let errors = Validated::<String, i32>::invalid_many(vec![
    ///     "error1".to_string(),
    ///     "error2".to_string(),
    ///     "error3".to_string(),
    /// ]);
    ///
    /// let mut seen = Vec::new();
    /// let result = errors.recover_all(|e| {
    ///     seen.push(e.clone());
    ///     Validated::invalid(format!("recovered: {}", e))
    /// });
    ///
    /// // All three errors were processed
    /// assert_eq!(seen.len(), 3);
    /// assert!(result.is_invalid());
    /// ```
    pub fn recover_all<F>(self, mut recovery: F) -> Self
    where
        F: FnMut(E) -> Self,
    {
        match self {
            Validated::Valid(v) => Validated::Valid(v),
            Validated::Invalid(errors) => {
                let mut accumulated = Vec::new();

                for error in errors {
                    match recovery(error) {
                        Validated::Valid(v) => {
                            // First successful recovery wins
                            return Validated::Valid(v);
                        },
                        Validated::Invalid(more_errors) => {
                            accumulated.extend(more_errors.into_vec());
                        },
                    }
                }

                Validated::invalid_many(accumulated)
            },
        }
    }

    /// Recovers with a function that receives ALL errors at once.
    ///
    /// This variant is useful when you need to analyze all errors together
    /// to make a recovery decision, rather than processing them individually.
    ///
    /// # Type Parameters
    ///
    /// * `F`: Recovery function type
    ///
    /// # Arguments
    ///
    /// * `recovery`: Function that receives all errors as a Vec
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::validated::Validated;
    ///
    /// let errors = Validated::<String, i32>::invalid_many(vec![
    ///     "Missing name".to_string(),
    ///     "Invalid email".to_string(),
    /// ]);
    ///
    /// let result = errors.recover_all_at_once(|all_errors| {
    ///     if all_errors.len() > 5 {
    ///         // Too many errors, give up
    ///         Validated::invalid("Too many validation errors".to_string())
    ///     } else {
    ///         // Provide default value
    ///         Validated::valid(Default::default())
    ///     }
    /// });
    /// ```
    pub fn recover_all_at_once<F>(self, recovery: F) -> Self
    where
        F: FnOnce(Vec<E>) -> Self,
    {
        match self {
            Validated::Valid(v) => Validated::Valid(v),
            Validated::Invalid(errors) => recovery(errors.into_vec().into_vec()),
        }
    }

    /// Attempts to recover from errors with a fallback value.
    ///
    /// This is a convenience method for the common case of providing
    /// a default value when validation fails.
    ///
    /// # Arguments
    ///
    /// * `default`: The fallback value to use
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::validated::Validated;
    ///
    /// let error: Validated<String, i32> = Validated::invalid("failed".to_string());
    /// let recovered = error.recover_with(42);
    /// assert_eq!(recovered, Validated::valid(42));
    /// ```
    #[inline]
    pub fn recover_with(self, default: A) -> Self {
        match self {
            Validated::Valid(v) => Validated::Valid(v),
            Validated::Invalid(_) => Validated::Valid(default),
        }
    }
}
