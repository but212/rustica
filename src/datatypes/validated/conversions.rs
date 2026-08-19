use crate::datatypes::validated::Validated;

impl<E, A> Validated<E, A> {
    /// Converts from `Result<A, E>` to `Validated<E, A>` using a reference to the Result.
    ///
    /// This method takes a reference to a `Result` and returns a new `Validated` instance.
    /// The original `Result` is not consumed, making this method suitable when you need
    /// to keep the original `Result` intact. This requires `A: Clone` and `E: Clone`
    /// to create a new `Validated` from the referenced data.
    ///
    /// For a version that takes ownership of the `Result`, see `from_result_owned`.
    ///
    /// # Type Parameters
    ///
    /// * `A`: The value type (must implement `Clone`)
    /// * `E`: The error type (must implement `Clone`)
    ///
    /// # Arguments
    ///
    /// * `result` - The Result to convert (by reference)
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::validated::Validated;
    ///
    /// let result: Result<i32, &str> = Ok(42);
    /// let validated = Validated::from_result(&result);
    /// assert_eq!(validated, Validated::valid(42));
    /// // The original result is still available
    /// assert_eq!(result, Ok(42));
    ///
    /// let error_result: Result<i32, &str> = Err("error");
    /// let validated = Validated::from_result(&error_result);
    /// assert_eq!(validated, Validated::invalid("error"));
    /// ```
    #[inline]
    pub fn from_result(result: &Result<A, E>) -> Validated<E, A>
    where
        A: Clone,
        E: Clone,
    {
        use crate::error::result_to_validated;
        result_to_validated(result.clone())
    }

    /// Converts from `Result<A, E>` to `Validated<E, A>`, taking ownership of the Result.
    ///
    /// This method consumes the `Result` and returns a new `Validated` instance. By taking
    /// ownership of the `Result`, this method avoids any cloning of the inner values, making
    /// it more efficient than `from_result` when you don't need the original `Result` anymore.
    /// This is particularly useful when working with expensive-to-clone types.
    ///
    /// For a version that takes a reference to the `Result`, see `from_result`.
    ///
    /// # Type Parameters
    ///
    /// * `A`: The value type
    /// * `E`: The error type
    ///
    /// # Arguments
    ///
    /// * `result` - The Result to convert and consume
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::validated::Validated;
    ///
    /// let result: Result<i32, String> = Ok(42);
    /// let validated = Validated::from_result_owned(result);
    /// assert_eq!(validated, Validated::valid(42));
    /// // Note that result is consumed and can't be used again
    ///
    /// let error_result: Result<i32, String> = Err("error".to_string());
    /// let validated = Validated::from_result_owned(error_result);
    /// assert!(validated.is_invalid());
    /// assert_eq!(validated.errors(), vec!["error".to_string()]);
    /// ```
    pub fn from_result_owned(result: Result<A, E>) -> Validated<E, A>
    where
        A: Clone,
        E: Clone,
    {
        use crate::error::result_to_validated;
        result_to_validated(result)
    }

    /// Converts this `Validated` into a `Result`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::validated::Validated;
    ///
    /// let valid: Validated<&str, i32> = Validated::valid(42);
    /// let result = valid.to_result();
    /// assert_eq!(result, Ok(42));
    ///
    /// let invalid: Validated<&str, i32> = Validated::invalid("error");
    /// assert!(invalid.to_result().is_err());
    /// ```
    #[inline]
    pub fn to_result(&self) -> Result<A, E>
    where
        A: Clone,
        E: Clone,
    {
        match self {
            Validated::Valid(a) => Ok(a.clone()),
            Validated::Invalid(errors) => Err(errors[0].clone()),
        }
    }

    /// Converts this `Validated` into a `Result`, taking ownership of the Validated.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::validated::Validated;
    ///
    /// let valid: Validated<String, i32> = Validated::valid(42);
    /// let result = valid.to_result_owned();
    /// assert_eq!(result, Ok(42));
    ///
    /// let invalid: Validated<String, i32> = Validated::invalid("error".to_string());
    /// assert!(invalid.to_result_owned().is_err());
    /// ```
    #[inline]
    pub fn to_result_owned(self) -> Result<A, E> {
        match self {
            Validated::Valid(a) => Ok(a),
            Validated::Invalid(errors) => Err(errors
                .into_iter()
                .next()
                .expect("Validated errors cannot be empty")),
        }
    }

    /// Converts from `Option<A>` to `Validated<E, A>` with a provided error.
    ///
    /// If the Option is Some, returns a Valid value.
    /// If the Option is None, returns an Invalid with the provided error.
    ///
    /// # Arguments
    ///
    /// * `option` - The Option to convert
    /// * `error` - The error to use if the Option is None
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::validated::Validated;
    ///
    /// let some_value: Option<i32> = Some(42);
    /// let validated: Validated<&str, i32> = Validated::from_option(&some_value, &"missing value");
    /// assert_eq!(validated, Validated::valid(42));
    ///
    /// let none_value: Option<i32> = None;
    /// let validated: Validated<&str, i32> = Validated::from_option(&none_value, &"missing value");
    /// assert_eq!(validated, Validated::invalid("missing value"));
    /// ```
    #[inline]
    pub fn from_option(option: &Option<A>, error: &E) -> Self
    where
        A: Clone,
        E: Clone,
    {
        match option {
            Some(value) => Validated::Valid(value.clone()),
            None => Validated::invalid(error.clone()),
        }
    }

    /// Converts from `Option<A>` to `Validated<E, A>` with a provided error, taking ownership.
    ///
    /// If the Option is Some, returns a Valid value.
    /// If the Option is None, returns an Invalid with the provided error.
    ///
    /// # Arguments
    ///
    /// * `option` - The Option to convert and consume
    /// * `error` - The error to use if the Option is None
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::validated::Validated;
    ///
    /// let some_value: Option<i32> = Some(42);
    /// let validated: Validated<String, i32> = Validated::from_option_owned(some_value, "missing value".to_string());
    /// assert_eq!(validated, Validated::valid(42));
    ///
    /// let none_value: Option<i32> = None;
    /// let validated: Validated<String, i32> = Validated::from_option_owned(none_value, "missing value".to_string());
    /// assert!(validated.is_invalid());
    /// ```
    #[inline]
    pub fn from_option_owned(option: Option<A>, error: E) -> Self {
        match option {
            Some(value) => Validated::Valid(value),
            None => Validated::invalid(error),
        }
    }

    /// Converts from `Option<A>` to `Validated<E, A>` with a function to generate the error.
    ///
    /// If the Option is Some, returns a Valid value.
    /// If the Option is None, returns an Invalid with the error from the provided function.
    ///
    /// # Arguments
    ///
    /// * `option` - The Option to convert
    /// * `error_fn` - Function to generate the error if the Option is None
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::validated::Validated;
    ///
    /// let some_value: Option<i32> = Some(42);
    /// let validated: Validated<&str, i32> = Validated::from_option_with(&some_value, &|| "missing value");
    /// assert_eq!(validated, Validated::valid(42));
    ///
    /// let none_value: Option<i32> = None;
    /// let validated: Validated<&str, i32> = Validated::from_option_with(&none_value, &|| "missing value");
    /// assert_eq!(validated, Validated::invalid("missing value"));
    /// ```
    #[inline]
    pub fn from_option_with<F>(option: &Option<A>, error_fn: &F) -> Self
    where
        F: Fn() -> E,
        A: Clone,
    {
        match option {
            Some(value) => Validated::Valid(value.clone()),
            None => Validated::invalid(error_fn()),
        }
    }

    /// Converts from `Option<A>` to `Validated<E, A>` with a function to generate the error, taking ownership.
    ///
    /// If the Option is Some, returns a Valid value.
    /// If the Option is None, returns an Invalid with the error from the provided function.
    ///
    /// # Arguments
    ///
    /// * `option` - The Option to convert and consume
    /// * `error_fn` - Function to generate the error if the Option is None
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::validated::Validated;
    ///
    /// let some_value: Option<i32> = Some(42);
    /// let validated: Validated<String, i32> = Validated::from_option_with_owned(some_value, || "missing value".to_string());
    /// assert_eq!(validated, Validated::valid(42));
    ///
    /// let none_value: Option<i32> = None;
    /// let validated: Validated<String, i32> = Validated::from_option_with_owned(none_value, || "missing value".to_string());
    /// assert!(validated.is_invalid());
    /// ```
    #[inline]
    pub fn from_option_with_owned<F>(option: Option<A>, error_fn: F) -> Self
    where
        F: FnOnce() -> E,
    {
        match option {
            Some(value) => Validated::Valid(value),
            None => Validated::invalid(error_fn()),
        }
    }
}
