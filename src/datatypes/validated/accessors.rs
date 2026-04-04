use crate::datatypes::validated::{Validated, ErrorVec};
use crate::datatypes::error::ValidatedError;

impl<E, A> Validated<E, A> {
    /// Returns all errors if this is invalid, or an empty collection if valid.
    ///
    /// This method clones the underlying errors into an owned `Vec`. For zero-copy
    /// views, prefer [`error_slice`](#method.error_slice) or [`error_payload`](#method.error_payload).
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::validated::Validated;
    ///
    /// let valid: Validated<&str, i32> = Validated::valid(42);
    /// let errors = valid.errors();
    /// assert!(errors.is_empty());
    ///
    /// let invalid: Validated<&str, i32> = Validated::invalid("error");
    /// let errors = invalid.errors();
    /// assert_eq!(errors.len(), 1);
    /// assert_eq!(errors[0], "error");
    /// ```
    #[inline]
    pub fn errors(&self) -> Vec<E>
    where
        E: Clone,
    {
        self.iter_errors().cloned().collect()
    }

    /// Returns a slice view over the accumulated errors without cloning.
    ///
    /// When this `Validated` is `Valid`, an empty slice is returned.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::validated::Validated;
    ///
    /// let invalid: Validated<&str, i32> = Validated::invalid("error");
    /// assert_eq!(invalid.error_slice(), &["error"]);
    ///
    /// let valid: Validated<&str, i32> = Validated::valid(1);
    /// assert!(valid.error_slice().is_empty());
    /// ```
    #[inline]
    pub fn error_slice(&self) -> &[E] {
        match self {
            Validated::Valid(_) => &[],
            Validated::Invalid(es) => es.as_slice(),
        }
    }

    /// Returns a mutable reference to the internal error buffer when invalid.
    ///
    /// This enables in-place modifications without reallocating. Mutating the
    /// returned buffer is only safe when you can preserve the semantic meaning
    /// of accumulated errors.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::validated::Validated;
    ///
    /// let mut invalid: Validated<String, ()> = Validated::invalid("oops".to_string());
    /// if let Some(errors) = invalid.error_buffer_mut() {
    ///     errors.push("more".to_string());
    /// }
    /// assert_eq!(invalid.error_slice(), &["oops", "more"]);
    /// ```
    #[inline]
    pub fn error_buffer_mut(&mut self) -> Option<&mut ErrorVec<E>> {
        match self {
            Validated::Valid(_) => None,
            Validated::Invalid(es) => Some(es),
        }
    }

    /// Returns an iterator over all errors if this is invalid, or an empty iterator if valid.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::validated::Validated;
    ///
    /// let valid: Validated<&str, i32> = Validated::valid(42);
    /// let mut errors = valid.iter_errors();
    /// assert!(errors.next().is_none());
    ///
    /// let invalid: Validated<&str, i32> = Validated::invalid("error");
    /// let mut errors = invalid.iter_errors();
    /// assert_eq!(errors.next().unwrap(), &"error");
    /// assert!(errors.next().is_none());
    /// ```
    #[inline]
    pub fn iter_errors(&self) -> crate::datatypes::validated::iter::ErrorsIter<'_, E> {
        use crate::datatypes::validated::iter::ErrorsIter;
        match self {
            Validated::Invalid(es) => ErrorsIter::Multi(es.iter()),
            _ => ErrorsIter::Empty,
        }
    }

    /// Returns a reference to the internal `SmallVec` of errors if this is `Invalid`, otherwise `None`.
    ///
    /// This provides direct, non-cloning access to the error collection.
    /// If you need an owned `Vec<E>` (which clones), see the `errors()` method.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::validated::Validated;
    ///
    /// let valid: Validated<&str, i32> = Validated::valid(42);
    /// assert_eq!(valid.error_payload(), None);
    ///
    /// let invalid: Validated<&str, i32> = Validated::invalid("error");
    /// if let Some(errors) = invalid.error_payload() {
    ///     assert_eq!(errors.len(), 1);
    ///     assert_eq!(errors[0], "error");
    /// }
    ///
    /// let invalid_many: Validated<String, i32> = Validated::invalid_many(vec!["err1".to_string(), "err2".to_string()]);
    /// if let Some(errors) = invalid_many.error_payload() {
    ///     assert_eq!(errors.len(), 2);
    ///     assert_eq!(errors[0], "err1");
    ///     assert_eq!(errors[1], "err2");
    /// }
    /// ```
    #[inline]
    pub fn error_payload(&self) -> Option<&ErrorVec<E>> {
        match self {
            Validated::Valid(_) => None,
            Validated::Invalid(es) => Some(es),
        }
    }

    /// Returns the contained `Valid` value, consuming the `self` value.
    ///
    /// Because this function consumes `self`, it does not require `A` to be `Clone`.
    /// This is more efficient than `unwrap()` if `A` is `Clone` but cloning is expensive,
    /// or if `A` is not `Clone`.
    ///
    /// # Panics
    ///
    /// Panics if `self` is `Invalid`, with a panic message including the errors.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::validated::Validated;
    ///
    /// let valid: Validated<&str, i32> = Validated::valid(42);
    /// assert_eq!(valid.unwrap_owned(), 42);
    /// ```
    ///
    /// ```rust,should_panic
    /// use rustica::datatypes::validated::Validated;
    ///
    /// let invalid: Validated<&str, i32> = Validated::invalid("error message");
    /// // This will panic with: "Called Validated::unwrap_owned() on an Invalid value: [\"error message\"]"
    /// invalid.unwrap_owned();
    /// ```
    #[inline]
    pub fn unwrap_owned(self) -> A
    where
        E: std::fmt::Debug,
    {
        match self {
            Validated::Valid(a) => a,
            Validated::Invalid(e) => {
                panic!("Called Validated::unwrap_owned() on an Invalid value: {e:?}")
            },
        }
    }

    /// Returns the contained `Invalid` error collection, consuming the `self` value.
    ///
    /// This method moves the `SmallVec` out of the `Validated` instance.
    ///
    /// # Panics
    ///
    /// Panics if `self` is `Valid`, with a panic message including the valid value.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::validated::Validated;
    /// use smallvec::SmallVec;
    ///
    /// let invalid: Validated<&str, i32> = Validated::invalid("error");
    /// let expected: SmallVec<[&str; 4]> = SmallVec::from_slice(&["error"]);
    /// assert_eq!(invalid.unwrap_invalid_owned(), expected);
    /// ```
    ///
    /// ```rust,should_panic
    /// use rustica::datatypes::validated::Validated;
    ///
    /// let valid: Validated<&str, i32> = Validated::valid(42);
    /// // This will panic with: "Called Validated::unwrap_invalid_owned() on a Valid value: 42"
    /// valid.unwrap_invalid_owned();
    /// ```
    #[inline]
    pub fn unwrap_invalid_owned(self) -> ErrorVec<E>
    where
        A: std::fmt::Debug,
    {
        match self {
            Validated::Valid(a) => {
                panic!("Called Validated::unwrap_invalid_owned() on a Valid value: {a:?}")
            },
            Validated::Invalid(e) => e,
        }
    }

    /// Consumes `self` and returns `Ok(A)` if `Valid(A)`, or `Err(ErrorVec<E>)` if `Invalid(errors)`.
    ///
    /// This method is useful for safely extracting the valid value or the complete collection of errors,
    /// transferring ownership without cloning the contained value or errors.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::validated::Validated;
    /// use smallvec::smallvec;
    ///
    /// let valid: Validated<&str, i32> = Validated::valid(42);
    /// assert_eq!(valid.into_value(), Ok(42));
    ///
    /// let invalid: Validated<&str, i32> = Validated::invalid_many(vec!["err1", "err2"]);
    /// assert_eq!(invalid.into_value(), Err(smallvec!["err1", "err2"]));
    ///
    /// // Example with move semantics (no cloning required)
    /// use std::rc::Rc;
    ///
    /// #[derive(Debug, PartialEq)]
    /// struct ExpensiveValue(Rc<Vec<u8>>);
    /// #[derive(Debug, PartialEq)]
    /// struct CustomError(String);
    ///
    /// let data = Rc::new(vec![1, 2, 3]);
    /// let valid_ex: Validated<CustomError, ExpensiveValue> = Validated::Valid(ExpensiveValue(data.clone()));
    /// assert_eq!(Rc::strong_count(&data), 2);
    ///
    /// // into_value consumes the Validated without cloning the inner value
    /// let result = valid_ex.into_value();
    /// assert!(result.is_ok());
    /// assert_eq!(Rc::strong_count(&data), 2); // No additional clones created
    /// ```
    #[inline]
    pub fn into_value(self) -> Result<A, ErrorVec<E>> {
        match self {
            Validated::Valid(a) => Ok(a),
            Validated::Invalid(es) => Err(es),
        }
    }

    /// Consumes `self` and returns `Ok(ErrorVec<E>)` if `Invalid(errors)`, or `Err(A)` if `Valid(A)`.
    ///
    /// This method is useful for safely extracting the complete error collection or the valid value,
    /// transferring ownership without cloning the contained value or errors.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::validated::Validated;
    /// use std::rc::Rc;
    /// use smallvec::smallvec;
    ///
    /// let valid: Validated<String, i32> = Validated::valid(42);
    /// let result = valid.into_error_payload();
    /// assert_eq!(result, Err(42));
    ///
    /// let invalid: Validated<String, i32> = Validated::invalid("error".to_string());
    /// let result = invalid.into_error_payload();
    /// assert_eq!(result, Ok(smallvec!["error".to_string()]));
    ///
    /// // Example with truly non-Clone types
    /// struct TrulyNonClone {
    ///     data: Rc<()>,
    /// }
    ///
    /// impl PartialEq for TrulyNonClone {
    ///     fn eq(&self, _other: &Self) -> bool { true }
    /// }
    ///
    /// impl std::fmt::Debug for TrulyNonClone {
    ///     fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
    ///         f.write_str("TrulyNonClone")
    ///     }
    /// }
    ///
    /// let value = TrulyNonClone { data: Rc::new(()) };
    /// let error = TrulyNonClone { data: Rc::new(()) };
    ///
    /// let valid_nc: Validated<TrulyNonClone, TrulyNonClone> = Validated::Valid(value);
    /// let result = valid_nc.into_error_payload();
    /// assert!(matches!(result, Err(_)));
    ///
    /// let invalid_nc: Validated<TrulyNonClone, TrulyNonClone> = Validated::Invalid(smallvec![error]);
    /// let result = invalid_nc.into_error_payload();
    /// assert!(matches!(result, Ok(_)));
    /// ```
    #[inline]
    pub fn into_error_payload(self) -> Result<ErrorVec<E>, A> {
        match self {
            Validated::Valid(a) => Err(a),
            Validated::Invalid(es) => Ok(es),
        }
    }

    /// Returns a reference to the valid value as an Option, without cloning.
    ///
    /// This is a zero-copy alternative to `to_option()` when you only need a reference.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::validated::Validated;
    ///
    /// let valid: Validated<&str, i32> = Validated::Valid(42);
    /// assert_eq!(valid.as_option(), Some(&42));
    ///
    /// let invalid: Validated<&str, i32> = Validated::Invalid(vec!["error"].into());
    /// assert_eq!(invalid.as_option(), None);
    /// ```
    #[inline]
    pub fn as_option(&self) -> Option<&A> {
        match self {
            Validated::Valid(x) => Some(x),
            Validated::Invalid(_) => None,
        }
    }

    /// Converts to Option by consuming self, without cloning.
    ///
    /// This is more efficient than `to_option()` when you can consume the Validated.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::validated::Validated;
    ///
    /// let valid: Validated<&str, i32> = Validated::Valid(42);
    /// assert_eq!(valid.into_option(), Some(42));
    ///
    /// let invalid: Validated<&str, i32> = Validated::Invalid(vec!["error"].into());
    /// assert_eq!(invalid.into_option(), None);
    /// ```
    #[inline]
    pub fn into_option(self) -> Option<A> {
        match self {
            Validated::Valid(x) => Some(x),
            Validated::Invalid(_) => None,
        }
    }

    /// Safely extracts the valid value.
    ///
    /// This is the safe alternative to `unwrap_owned()` that returns
    /// a proper error type instead of panicking.
    ///
    /// # Returns
    ///
    /// * `Ok(A)` - The valid value if this is `Validated::Valid`
    /// * `Err(ValidatedError::ExpectedValid)` - If this is `Validated::Invalid`
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::validated::Validated;
    /// use rustica::datatypes::error::ValidatedError;
    ///
    /// let valid: Validated<&str, i32> = Validated::Valid(42);
    /// assert_eq!(valid.try_unwrap(), Ok(42));
    ///
    /// let invalid: Validated<&str, i32> = Validated::invalid("error");
    /// assert_eq!(invalid.try_unwrap(), Err(ValidatedError::ExpectedValid));
    /// ```
    #[inline]
    pub fn try_unwrap(self) -> Result<A, ValidatedError> {
        match self {
            Validated::Valid(a) => Ok(a),
            Validated::Invalid(_) => Err(ValidatedError::ExpectedValid),
        }
    }

    /// Safely extracts the error collection.
    ///
    /// This is the safe alternative to `unwrap_invalid_owned()` that returns
    /// a proper error type instead of panicking.
    ///
    /// # Returns
    ///
    /// * `Ok(ErrorVec<E>)` - The errors if this is `Validated::Invalid`
    /// * `Err(ValidatedError::ExpectedInvalid)` - If this is `Validated::Valid`
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::validated::Validated;
    /// use rustica::datatypes::error::ValidatedError;
    ///
    /// let invalid: Validated<&str, i32> = Validated::invalid("error");
    /// let result = invalid.try_unwrap_invalid();
    /// assert!(result.is_ok());
    /// assert_eq!(result.unwrap().len(), 1);
    ///
    /// let valid: Validated<&str, i32> = Validated::Valid(42);
    /// assert_eq!(valid.try_unwrap_invalid(), Err(ValidatedError::ExpectedInvalid));
    /// ```
    #[inline]
    pub fn try_unwrap_invalid(self) -> Result<ErrorVec<E>, ValidatedError> {
        match self {
            Validated::Invalid(es) => Ok(es),
            Validated::Valid(_) => Err(ValidatedError::ExpectedInvalid),
        }
    }

    /// Safely gets a reference to the valid value.
    ///
    /// This is the safe alternative that returns a proper error type
    /// instead of returning Option.
    ///
    /// # Returns
    ///
    /// * `Ok(&A)` - A reference to the valid value
    /// * `Err(ValidatedError::ExpectedValid)` - If this is `Validated::Invalid`
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::validated::Validated;
    /// use rustica::datatypes::error::ValidatedError;
    ///
    /// let valid: Validated<&str, i32> = Validated::Valid(42);
    /// assert_eq!(valid.try_valid_ref(), Ok(&42));
    ///
    /// let invalid: Validated<&str, i32> = Validated::invalid("error");
    /// assert_eq!(invalid.try_valid_ref(), Err(ValidatedError::ExpectedValid));
    /// ```
    #[inline]
    pub fn try_valid_ref(&self) -> Result<&A, ValidatedError> {
        match self {
            Validated::Valid(a) => Ok(a),
            Validated::Invalid(_) => Err(ValidatedError::ExpectedValid),
        }
    }

    /// Unwraps a valid value or panics.
    ///
    /// If this is valid, returns the valid value.
    /// If this is invalid, panics.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::validated::Validated;
    ///
    /// let valid: Validated<&str, i32> = Validated::valid(42);
    /// assert_eq!(valid.unwrap(), 42);
    /// ```
    ///
    /// ```rust,should_panic
    /// use rustica::datatypes::validated::Validated;
    ///
    /// let invalid: Validated<&str, i32> = Validated::invalid("error");
    /// invalid.unwrap(); // Panics
    /// ```
    ///
    /// # Panics
    ///
    /// Panics if this is invalid.
    #[inline]
    pub fn unwrap(&self) -> A
    where
        A: Clone,
    {
        match self {
            Validated::Valid(value) => value.clone(),
            _ => panic!("Cannot unwrap invalid value"),
        }
    }

    /// Unwraps a valid value or returns a default.
    ///
    /// If this is valid, returns the valid value.
    /// If this is invalid, returns the provided default.
    ///
    /// # Arguments
    ///
    /// * `default` - The default value to return if invalid
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::validated::Validated;
    ///
    /// let valid: Validated<&str, i32> = Validated::valid(42);
    /// assert_eq!(valid.unwrap_or(&0), 42);
    ///
    /// let invalid: Validated<&str, i32> = Validated::invalid("error");
    /// assert_eq!(invalid.unwrap_or(&0), 0);
    /// ```
    #[inline]
    pub fn unwrap_or(&self, default: &A) -> A
    where
        A: Clone,
    {
        match self {
            Validated::Valid(x) => x.clone(),
            _ => default.clone(),
        }
    }

    /// Returns a reference to the valid value.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::validated::Validated;
    ///
    /// let valid: Validated<&str, i32> = Validated::valid(42);
    /// assert_eq!(valid.as_ref(), Some(&42));
    ///
    /// let invalid: Validated<&str, i32> = Validated::invalid("error");
    /// assert_eq!(invalid.as_ref(), None);
    /// ```
    #[inline]
    pub fn as_ref(&self) -> Option<&A> {
        match self {
            Validated::Valid(x) => Some(x),
            _ => None,
        }
    }

    /// Unwraps a valid value or panics with a message.
    ///
    /// If this is valid, returns the valid value.
    /// If this is invalid, panics with a message.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::validated::Validated;
    ///
    /// let invalid: Validated<&str, i32> = Validated::invalid_many(["e1", "e2"]);
    /// assert_eq!(invalid.unwrap_invalid(), vec!["e1", "e2"]);
    /// ```
    ///
    /// ```rust,should_panic
    /// use rustica::datatypes::validated::Validated;
    ///
    /// let valid: Validated<&str, i32> = Validated::valid(42);
    /// valid.unwrap_invalid(); // Panics
    /// ```
    ///
    /// # Panics
    ///
    /// Panics if this is `Valid`.
    #[inline]
    pub fn unwrap_invalid(&self) -> Vec<E>
    where
        E: Clone,
    {
        match self {
            Validated::Invalid(_) => self.iter_errors().cloned().collect(),
            _ => panic!("Cannot unwrap valid value"),
        }
    }

    #[inline]
    pub fn to_option(&self) -> Option<A>
    where
        A: Clone,
    {
        match self {
            Validated::Valid(x) => Some(x.clone()),
            _ => None,
        }
    }
}
