//! Core implementation of the `Validated` data type.
//!
//! This module provides the fundamental `Validated<E, A>` type for accumulating
//! validation errors, along with its associated methods and helper types.

use smallvec::{SmallVec, smallvec};

/// Type alias for the internal error collection.
///
/// Uses `SmallVec` with inline capacity of 8 to optimize for the common case
/// of few errors while still supporting larger error collections efficiently.
type ErrorVec<E> = SmallVec<[E; 8]>;

/// Internal helper for efficiently accumulating validation errors.
///
/// `ErrorAccumulator` provides a unified interface for collecting errors from
/// multiple `Validated` instances, with optimized paths for both owned and
/// borrowed error collections.
///
/// # Performance Characteristics
///
/// - Stack-allocated for up to 8 errors (via `SmallVec`)
/// - Heap allocation only when exceeding inline capacity
/// - Zero-copy error transfer via `extend_owned` when consuming `Validated` instances
/// - Efficient cloning path via `extend_cloned` for borrowed references
///
/// # Type Parameters
///
/// * `E` - The error type being accumulated
struct ErrorAccumulator<E> {
    /// Internal buffer storing accumulated errors.
    buffer: ErrorVec<E>,
}

impl<E> ErrorAccumulator<E> {
    /// Creates a new empty error accumulator.
    ///
    /// The accumulator starts with inline storage for up to 8 errors.
    #[inline]
    fn new() -> Self {
        Self {
            buffer: ErrorVec::new(),
        }
    }

    /// Creates a new error accumulator with pre-allocated capacity.
    ///
    /// Use this when you know approximately how many errors to expect,
    /// to avoid reallocation during accumulation.
    ///
    /// # Arguments
    ///
    /// * `capacity` - The number of errors to pre-allocate space for
    #[inline]
    fn with_capacity(capacity: usize) -> Self {
        Self {
            buffer: ErrorVec::with_capacity(capacity),
        }
    }

    /// Consumes the accumulator and returns the collected errors.
    ///
    /// This transfers ownership of the error collection without cloning.
    #[inline]
    fn into_inner(self) -> ErrorVec<E> {
        self.buffer
    }

    /// Extends the accumulator with owned errors, avoiding clones.
    ///
    /// This method is optimized for consuming `Validated::Invalid` instances
    /// by draining their error collections directly into the accumulator.
    ///
    /// # Arguments
    ///
    /// * `errors` - The error collection to drain and append
    #[inline]
    fn extend_owned(&mut self, mut errors: ErrorVec<E>) {
        self.buffer.extend(errors.drain(..));
    }
}

impl<E: Clone> ErrorAccumulator<E> {
    /// Extends the accumulator by cloning errors from a borrowed collection.
    ///
    /// This method is used when working with `&Validated` references where
    /// the original error collection cannot be consumed. It pre-reserves
    /// capacity to minimize reallocations.
    ///
    /// # Arguments
    ///
    /// * `errors` - The error collection to clone from
    #[inline]
    fn extend_cloned(&mut self, errors: &ErrorVec<E>) {
        if errors.is_empty() {
            return;
        }
        self.buffer.reserve(errors.len());
        self.buffer.extend(errors.iter().cloned());
    }
}

/// A validation type that can accumulate multiple errors.
///
/// Validated<E, A> represents either a valid value of type A or a collection of
/// errors of type E. Unlike Result, which fails fast on the first error,
/// Validated can collect multiple errors during validation.
///
/// # Performance: Owned vs Borrowed API
///
/// This type provides both borrowed and owned variants of key methods to enable
/// zero-copy optimizations when ownership is available:
///
/// ## Borrowed Methods (Reference-based)
/// - `combine_errors(&self, other: &Self)` - Takes references, clones errors
/// - `sequence(&[&Validated<E, A>], fn)` - Works with references, clones errors
/// - `collect<I>(iter: I)` - Takes an iterator of `Validated` values; in practice often used with cloned values (e.g. `values.iter().cloned()`), and may clone depending on context
///
/// ## Owned Methods (Ownership-taking)
/// - `combine_errors_owned(self, other: Self)` - Takes ownership, moves errors
/// - `sequence_owned(Vec<Self>, fn)` - Takes owned values, moves errors
/// - `collect_owned<I>(iter: I)` - Takes owned iterator, moves errors
///
/// **Use owned methods when:** You can consume the `Validated` instances and want
/// maximum performance by avoiding error cloning.
///
/// **Use borrowed methods when:** You need to preserve the original instances
/// or are working with references.
///
/// # Zero-Copy Error Access
///
/// For read-only access to errors without cloning:
/// - `error_slice()` - Returns `&[E]` slice view
/// - `iter_errors()` - Returns iterator over error references
///
/// For mutable access to the internal error buffer:
/// - `error_buffer_mut()` - Returns `Option<&mut SmallVec<[E; 8]>>`
///
/// # Type Parameter Constraints
///
/// - **`E: Clone`**: The error type `E` often requires a `Clone` bound. This is because:
///   - Operations that accumulate errors from multiple `Validated` instances (e.g., in `Applicative::apply` when both are `Invalid`) may need to combine and thus clone error collections.
///   - Methods providing access to errors (e.g., `errors()`, which returns `Vec<E>`) typically clone the internal errors to avoid lifetime issues or to provide owned data.
///   - If your error type `E` is expensive to clone, consider wrapping it in an `Arc<E>` or ensure that operations that trigger cloning are used judiciously.
///
/// - **`A: Clone`**: The value type `A` also often requires a `Clone` bound for similar reasons, especially for methods that operate on `&self` but need to return an owned `Validated` or extract the value (e.g., `unwrap()`, `fmap_invalid` when `self` is `Valid`). Ownership-taking variants of methods (e.g., `fmap_owned`, `unwrap_owned`) can sometimes alleviate this requirement for `A`.
///
/// # Notes on Trait Implementations
///
/// - **`Alternative` Implementation**: The `Alternative` trait implementation for `Validated<E, A>` requires `E: Clone + Default`:
///   - `empty_alt()` returns `Validated::Invalid` containing a default error (`E::default()`).
///   - `guard(false)` also uses `E::default()` to create an `Invalid` state.
///   - `many()` for an `Invalid` state discards original errors and uses `E::default()`.
///   - These methods use `Default` to ensure a consistent representation for the empty/failure case.
///
/// # Error Accumulation Behavior
///
/// When combining multiple `Validated` instances with methods like `lift2` or `apply`, errors are accumulated
/// in a specific order:
///
/// - In `lift2(self, rb, f)`, errors from `self` are collected first, followed by errors from `rb`.
/// - Similarly, in `apply(self, rf)`, errors from `self` are collected first, then errors from `rf`.
///
/// This ordering is important to maintain consistency and predictable behavior when chaining operations.
///
/// # Iterator Support
///
/// `Validated<E, A>` provides several iterator methods to work with its contents:
///
/// - `iter()`: Returns an iterator over a reference to the valid value (0 or 1 items)
/// - `iter_mut()`: Returns an iterator over a mutable reference to the valid value (0 or 1 items)
/// - `iter_errors()`: Returns an iterator over references to all error values
/// - `iter_errors_mut()`: Returns an iterator over mutable references to all error values
///
/// ```rust
/// use rustica::datatypes::validated::Validated;
///
/// let valid: Validated<&str, i32> = Validated::valid(42);
/// let mut sum = 0;
/// // Iterate over the valid value
/// for &value in valid.iter() {
///     sum += value; // sum = 42
/// }
/// assert_eq!(sum, 42);
///
/// let invalid: Validated<&str, i32> = Validated::invalid("error");
/// let mut error_messages: Vec<&str> = Vec::new();
/// // Iterate over the error values
/// for &error in invalid.iter_errors() {
///     error_messages.push(error);
/// }
/// assert_eq!(error_messages, vec!["error"]);
/// ```
#[derive(Clone, PartialEq, PartialOrd, Eq, Ord, Debug, Hash)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
pub enum Validated<E, A> {
    /// Represents a valid value of type A.
    Valid(A),
    /// Represents an invalid state with multiple errors of type E.
    /// Uses SmallVec for better performance with small error counts.
    Invalid(SmallVec<[E; 8]>),
}

impl<E, A> Validated<E, A> {
    /// Returns whether this `Validated` is valid.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::validated::Validated;
    ///
    /// let valid: Validated<&str, i32> = Validated::valid(42);
    /// assert!(valid.is_valid());
    ///
    /// let invalid: Validated<&str, i32> = Validated::invalid("error");
    /// assert!(!invalid.is_valid());
    /// ```
    #[inline]
    pub fn is_valid(&self) -> bool {
        matches!(self, Validated::Valid(_))
    }

    /// Returns whether this `Validated` is invalid.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::validated::Validated;
    ///
    /// let valid: Validated<&str, i32> = Validated::valid(42);
    /// assert!(!valid.is_invalid());
    ///
    /// let invalid: Validated<&str, i32> = Validated::invalid("error");
    /// assert!(invalid.is_invalid());
    /// ```
    #[inline]
    pub fn is_invalid(&self) -> bool {
        !self.is_valid()
    }

    /// Recovers from each error individually, preserving error accumulation.
    ///
    /// Unlike `ErrorOps::recover` which only uses the first error, this method
    /// applies the recovery function to **every accumulated error**, maintaining
    /// Validated's core semantics of error collection.
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
    /// - If all recoveries succeed with Valid, returns the first Valid
    /// - If any recovery fails, accumulates all new errors
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

                Validated::Invalid(smallvec::SmallVec::from_vec(accumulated))
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
            Validated::Invalid(errors) => recovery(errors.into_vec()),
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
    pub fn error_buffer_mut(&mut self) -> Option<&mut SmallVec<[E; 8]>> {
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
    pub fn iter_errors(&self) -> std::slice::Iter<'_, E> {
        self.error_slice().iter()
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
    pub fn error_payload(&self) -> Option<&SmallVec<[E; 8]>> {
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
    /// let expected: SmallVec<[&str; 8]> = SmallVec::from_slice(&["error"]);
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
    pub fn unwrap_invalid_owned(self) -> SmallVec<[E; 8]>
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

    /// Consumes `self` and returns `Ok(A)` if `Valid(A)`, or `Err(SmallVec<[E; 8]>)` if `Invalid(errors)`.
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
    pub fn into_value(self) -> Result<A, SmallVec<[E; 8]>> {
        match self {
            Validated::Valid(a) => Ok(a),
            Validated::Invalid(es) => Err(es),
        }
    }

    /// Consumes `self` and returns `Ok(SmallVec<[E; 8]>)` if `Invalid(errors)`, or `Err(A)` if `Valid(A)`.
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
    pub fn into_error_payload(self) -> Result<SmallVec<[E; 8]>, A> {
        match self {
            Validated::Valid(a) => Err(a),
            Validated::Invalid(es) => Ok(es),
        }
    }
}

impl<E: Clone, A: Clone> Validated<E, A> {
    /// Creates a new valid instance.
    ///
    /// # Arguments
    ///
    /// * `x` - The valid value
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::validated::Validated;
    ///
    /// let valid: Validated<(), i32> = Validated::valid(42);
    /// ```
    #[inline]
    pub fn valid(x: A) -> Self {
        Validated::Valid(x)
    }

    /// Creates a new invalid instance with a single error.
    ///
    /// # Arguments
    ///
    /// * `e` - The error value
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::validated::Validated;
    ///
    /// let invalid: Validated<&str, ()> = Validated::invalid("validation error");
    /// ```
    #[inline]
    pub fn invalid(e: E) -> Self {
        Validated::Invalid(smallvec![e])
    }

    /// Creates a new invalid instance with multiple errors from a collection.
    ///
    /// Unlike `invalid_vec`, this method **does not panic** if the input `errors` collection is empty.
    /// If `errors` is empty, this function will produce `Validated::Invalid` containing an empty list of errors
    /// (e.g., `Validated::Invalid([])`).
    /// This makes `invalid_many` suitable for scenarios where an invalid state might legitimately have no specific
    /// error items, or where the input collection's emptiness is not considered a panic-worthy condition.
    ///
    /// If you specifically require that an `Invalid` instance must contain at least one error and wish for a panic
    /// if the input is empty, see `invalid_vec`.
    ///
    /// # Arguments
    ///
    /// * `errors` - A collection of error values that can be converted into a SmallVec
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::validated::Validated;
    ///
    /// let errors_list = vec!["error1", "error2"];
    /// let invalid: Validated<&str, ()> = Validated::invalid_many(errors_list.clone());
    /// assert!(invalid.is_invalid());
    /// assert_eq!(invalid.errors(), errors_list);
    /// ```
    ///
    /// ```rust
    /// use rustica::datatypes::validated::Validated;
    ///
    /// // Creating an invalid Validated from an empty Vec using invalid_many
    /// // results in Invalid with an empty list of errors.
    /// let invalid_empty: Validated<&str, ()> = Validated::invalid_many(Vec::<&str>::new());
    /// assert!(invalid_empty.is_invalid());
    /// assert!(invalid_empty.errors().is_empty());
    /// ```
    #[inline]
    pub fn invalid_many<I>(errors: I) -> Self
    where
        I: IntoIterator<Item = E>,
    {
        let iter = errors.into_iter();

        // Get size hint once
        let (lower, upper) = iter.size_hint();

        match upper {
            Some(exact) if exact == lower => {
                // ExactSizeIterator case - most efficient
                if exact <= 4 {
                    Validated::Invalid(iter.collect())
                } else {
                    let mut vec = SmallVec::with_capacity(exact);
                    vec.extend(iter);
                    Validated::Invalid(vec)
                }
            },
            Some(upper_bound) => {
                // Upper bound available
                if upper_bound <= 4 {
                    Validated::Invalid(iter.collect())
                } else {
                    let mut vec = SmallVec::with_capacity(upper_bound);
                    vec.extend(iter);
                    Validated::Invalid(vec)
                }
            },
            None => {
                // No upper bound - use lower bound or default
                if lower <= 4 {
                    Validated::Invalid(iter.collect())
                } else {
                    let mut vec = SmallVec::with_capacity(lower);
                    vec.extend(iter);
                    Validated::Invalid(vec)
                }
            },
        }
    }

    /// Creates a new invalid instance with multiple errors from a collection.
    ///
    /// **Important:** This function requires the input collection to contain at least one error.
    /// If the provided `errors` collection is empty, this function will **panic**.
    /// If you need to create an `Invalid` instance that can represent an empty set of errors
    /// (e.g., `Validated::Invalid([])`), use `invalid_many` instead. `invalid_many` will produce
    /// `Validated::Invalid` with an empty error list if given an empty input collection, without panicking.
    ///
    /// The rationale for this panicking behavior is to ensure that an `Invalid` state constructed via
    /// `invalid_vec` is guaranteed to be non-empty, which might be a specific requirement in certain contexts.
    /// However, for general use, `invalid_many` is often more flexible.
    ///
    /// # Arguments
    ///
    /// * `errors` - A collection of error values that can be converted into a SmallVec
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::validated::Validated;
    ///
    /// let errors_list = vec!["error1", "error2"];
    /// let invalid: Validated<&str, ()> = Validated::invalid_vec(errors_list.clone());
    /// assert!(invalid.is_invalid());
    /// assert_eq!(invalid.errors(), errors_list);
    /// ```
    ///
    /// ```rust,should_panic
    /// use rustica::datatypes::validated::Validated;
    ///
    /// // Attempting to create an invalid Validated from an empty Vec using invalid_vec should panic.
    /// let _invalid_empty: Validated<&str, ()> = Validated::invalid_vec(Vec::<&str>::new());
    /// ```
    #[inline]
    pub fn invalid_vec<I>(errors: I) -> Self
    where
        I: IntoIterator<Item = E>,
    {
        let mut iter = errors.into_iter();
        if let Some(first) = iter.next() {
            // Preallocate: at least 1 element for `first`, plus the iterator's lower bound
            let (lower, _upper) = iter.size_hint();
            let mut vec: SmallVec<[E; 8]> = SmallVec::with_capacity(lower.saturating_add(1));
            vec.push(first);
            vec.extend(iter);
            Validated::Invalid(vec)
        } else {
            panic!("Validated::invalid_vec requires at least one error")
        }
    }

    /// Maps a function over the error values if `Invalid`, or returns the `Valid` value (cloned).
    ///
    /// If this `Validated` is `Invalid`, applies the function `f` to transform each error.
    /// If `Valid`, the original valid value `A` is cloned and returned in a new `Validated::Valid`.
    /// This method is suitable when you only have a reference (`&self`) to the `Validated` value.
    ///
    /// # Type Parameters
    ///
    /// * `G`: The result type of the mapping function
    /// * `F`: The type of the mapping function
    ///
    /// # Arguments
    ///
    /// * `f` - Function to apply to each error
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::validated::Validated;
    ///
    /// let invalid: Validated<&str, i32> = Validated::invalid("error");
    /// let mapped = invalid.fmap_invalid(|e| format!("Error: {}", e));
    /// assert_eq!(mapped, Validated::invalid("Error: error".to_string()));
    /// ```
    pub fn fmap_invalid<G, F>(&self, f: F) -> Validated<G, A>
    where
        F: Fn(&E) -> G,
        G: Clone,
    {
        match self {
            Validated::Valid(x) => Validated::Valid(x.clone()),
            Validated::Invalid(_) => {
                let transformed = self.iter_errors().map(f).collect();
                Validated::Invalid(transformed)
            },
        }
    }

    /// Maps a function over the error values if `Invalid` (taking ownership), or returns the `Valid` value (moved).
    ///
    /// If this `Validated` is `Invalid`, applies the function `f` to transform each error (errors `E` are moved into `f`).
    /// If `Valid`, the original valid value `A` is moved and returned in a new `Validated::Valid`.
    /// This method takes `self` by ownership, which can be more efficient as it avoids cloning the value `A` if it's `Valid`.
    ///
    /// # Type Parameters
    ///
    /// * `G`: The result type of the mapping function
    /// * `F`: The type of the mapping function
    ///
    /// # Arguments
    ///
    /// * `f` - Function to apply to each error
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::validated::Validated;
    ///
    /// let invalid: Validated<&str, i32> = Validated::invalid("error");
    /// let mapped = invalid.fmap_invalid_owned(|e| format!("Error: {}", e));
    /// assert_eq!(mapped, Validated::invalid("Error: error".to_string()));
    /// ```
    pub fn fmap_invalid_owned<G, F>(self, f: F) -> Validated<G, A>
    where
        F: Fn(E) -> G,
        G: Clone,
    {
        match self {
            Validated::Valid(x) => Validated::Valid(x),
            Validated::Invalid(es) => {
                let transformed: SmallVec<[G; 8]> = es.into_iter().map(f).collect();
                Validated::Invalid(transformed)
            },
        }
    }

    /// Combines errors from two Validated values.
    ///
    /// This is used internally to combine errors when both values are invalid.
    /// The function assumes at least one of the values is invalid.
    ///
    /// # Arguments
    ///
    /// * `other` - Another Validated instance to combine errors with
    ///
    /// # Panics
    ///
    /// Panics if both values are valid, as this function should only be called when
    /// at least one value is invalid.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::validated::Validated;
    ///
    /// let invalid1: Validated<&str, i32> = Validated::invalid("error1");
    /// let invalid2: Validated<&str, i32> = Validated::invalid_many(["error2", "error3"]);
    ///
    /// // Case 1: self is Invalid, other is Invalid
    /// let combined1 = invalid1.clone().combine_errors(&invalid2);
    /// assert!(combined1.is_invalid());
    /// if let Validated::Invalid(errors) = combined1 {
    ///     assert_eq!(errors.as_slice(), &["error1", "error2", "error3"]);
    /// }
    ///
    /// // Case 2: self is Valid, other is Invalid
    /// let valid1: Validated<&str, i32> = Validated::valid(1);
    /// let combined2 = valid1.clone().combine_errors(&invalid2);
    /// assert!(combined2.is_invalid());
    /// if let Validated::Invalid(errors) = combined2 {
    ///     assert_eq!(errors.as_slice(), &["error2", "error3"]);
    /// }
    ///
    /// // Case 3: self is Invalid, other is Valid
    /// let combined3 = invalid1.clone().combine_errors(&valid1);
    /// assert!(combined3.is_invalid());
    /// if let Validated::Invalid(errors) = combined3 {
    ///     assert_eq!(errors.as_slice(), &["error1"]);
    /// }
    /// ```
    ///
    /// ```rust,should_panic
    /// use rustica::datatypes::validated::Validated;
    ///
    /// // Panics if both are Valid
    /// let valid1: Validated<&str, i32> = Validated::valid(1);
    /// let valid2: Validated<&str, i32> = Validated::valid(2);
    /// let _combined_panic = valid1.combine_errors(&valid2);
    /// ```
    pub fn combine_errors(&self, other: &Self) -> Self {
        match (self, other) {
            (Validated::Valid(_), Validated::Valid(_)) => unreachable!(),
            (Validated::Valid(_), invalid) => invalid.clone(),
            (invalid, Validated::Valid(_)) => invalid.clone(),
            (Validated::Invalid(e1), Validated::Invalid(e2)) => {
                let mut acc = ErrorAccumulator::with_capacity(e1.len() + e2.len());
                acc.extend_cloned(e1);
                acc.extend_cloned(e2);
                Validated::Invalid(acc.into_inner())
            },
        }
    }

    /// Combines errors from two `Validated` instances, taking ownership of both.
    ///
    /// This method is more efficient than `combine_errors` when you can consume
    /// both `Validated` instances, as it avoids cloning the error collections.
    ///
    /// # Panics
    ///
    /// Panics if both `Validated` instances are `Valid`. This is a programmer error
    /// as there are no errors to combine.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::validated::Validated;
    ///
    /// let invalid1: Validated<&str, i32> = Validated::invalid("error1");
    /// let invalid2: Validated<&str, i32> = Validated::invalid("error2");
    /// let combined = invalid1.combine_errors_owned(invalid2);
    /// assert_eq!(combined.error_slice(), &["error1", "error2"]);
    /// ```
    #[inline]
    pub fn combine_errors_owned(self, other: Self) -> Self {
        match (self, other) {
            (Validated::Valid(_), Validated::Valid(_)) => unreachable!(),
            (Validated::Valid(_), invalid) => invalid,
            (invalid, Validated::Valid(_)) => invalid,
            (Validated::Invalid(mut e1), Validated::Invalid(e2)) => {
                e1.extend(e2);
                Validated::Invalid(e1)
            },
        }
    }

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
    #[inline]
    pub fn from_result_owned(result: Result<A, E>) -> Validated<E, A> {
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
        use crate::utils::error_utils::WithError;
        self.clone().to_result()
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
        use crate::utils::error_utils::WithError;
        self.to_result()
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
    pub fn from_option(option: &Option<A>, error: &E) -> Self {
        match option {
            Some(value) => Validated::Valid(value.clone()),
            None => Validated::Invalid(smallvec![error.clone()]),
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
            None => Validated::Invalid(smallvec![error]),
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
    {
        match option {
            Some(value) => Validated::Valid(value.clone()),
            None => Validated::Invalid(smallvec![error_fn()]),
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
            None => Validated::Invalid(smallvec![error_fn()]),
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
    pub fn unwrap(&self) -> A {
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
    pub fn unwrap_or(&self, default: &A) -> A {
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
    ///
    /// Note: This is a method on `Validated` that returns `Option<&A>`, and is distinct
    /// from the `std::convert::AsRef` trait implementation provided in
    /// `validated::traits`. To use the trait-based `AsRef<A>` implementation,
    /// reference it through the trait (e.g. `<Validated<E, A> as AsRef<A>>::as_ref(&v)`).
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

    /// Combines multiple Validated values using a function.
    ///
    /// This is similar to `lift2` but works with a slice of Validated values.
    /// If all values are valid, applies the function to combine them.
    /// If any values are invalid, collects all errors.
    ///
    /// # Type Parameters
    ///
    /// * `B`: The result type of the combining function
    /// * `F`: The type of the combining function
    ///
    /// # Arguments
    ///
    /// * `values` - Slice of Validated values
    /// * `f` - Function to combine valid values
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::validated::Validated;
    ///
    /// let a: Validated<&str, i32> = Validated::valid(1);
    /// let b: Validated<&str, i32> = Validated::valid(2);
    /// let c: Validated<&str, i32> = Validated::valid(3);
    ///
    /// let values = [&a, &b, &c];
    /// let sum = Validated::sequence(&values, &|vs: &[i32]| {
    ///     vs.iter().sum()
    /// });
    /// assert_eq!(sum, Validated::valid(6));
    ///
    /// // Example with invalid inputs
    /// let d: Validated<&str, i32> = Validated::invalid("error1");
    /// let e: Validated<&str, i32> = Validated::valid(5);
    /// let f: Validated<&str, i32> = Validated::invalid("error2");
    /// let mixed_values = [&d, &e, &f];
    /// let mixed_result = Validated::sequence(&mixed_values, &|vs: &[i32]| vs.iter().sum::<i32>());
    /// assert!(mixed_result.is_invalid());
    /// if let Validated::Invalid(errors) = mixed_result {
    ///     assert_eq!(errors.as_slice(), &["error1", "error2"]);
    /// }
    ///
    /// // Example with empty input
    /// let empty_values: &[&Validated<&str, i32>; 0] = &[];
    /// let empty_result = Validated::sequence(empty_values, &|vs: &[i32]| vs.iter().sum::<i32>());
    /// assert_eq!(empty_result, Validated::valid(0));
    /// ```
    pub fn sequence<B, F>(values: &[&Validated<E, A>], f: &F) -> Validated<E, B>
    where
        F: Fn(&[A]) -> B,
        B: Clone,
    {
        // Early check for empty slice
        if values.is_empty() {
            return Validated::Valid(f(&[]));
        }

        // First pass to check if all are valid (fast path)
        if values.iter().all(|v| matches!(v, Validated::Valid(_))) {
            let valid_values: Vec<A> = values
                .iter()
                .filter_map(|v| match v {
                    Validated::Valid(x) => Some(x.clone()),
                    _ => None,
                })
                .collect();
            return Validated::Valid(f(&valid_values));
        }

        // Collect all errors using iterator methods
        let mut acc = ErrorAccumulator::new();
        for value in values {
            if let Validated::Invalid(es) = value {
                acc.extend_cloned(es);
            }
        }

        Validated::Invalid(acc.into_inner())
    }

    /// Sequences owned Validated values into a single Validated value.
    ///
    /// This method is more efficient than `sequence` when you can consume the
    /// Validated instances, as it avoids cloning error collections.
    ///
    /// # Type Parameters
    ///
    /// * `B`: The output value type (must implement `Clone`)
    /// * `F`: The function type to transform collected valid values
    ///
    /// # Arguments
    ///
    /// * `values`: A vector of owned `Validated` values to sequence
    /// * `f`: A function to transform the collected valid values
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::validated::Validated;
    ///
    /// let values = vec![
    ///     Validated::<&str, i32>::valid(1),
    ///     Validated::<&str, i32>::valid(2),
    /// ];
    /// let result = Validated::sequence_owned(values, |vals| vals.len());
    /// assert_eq!(result, Validated::valid(2));
    /// ```
    #[inline]
    pub fn sequence_owned<B, F>(values: Vec<Self>, f: F) -> Validated<E, B>
    where
        F: Fn(Vec<A>) -> B,
        B: Clone,
    {
        // Early check for empty vec
        if values.is_empty() {
            return Validated::Valid(f(Vec::new()));
        }

        // First pass to check if all are valid (fast path)
        if values.iter().all(|v| matches!(v, Validated::Valid(_))) {
            let valid_values: Vec<A> = values
                .into_iter()
                .filter_map(|v| match v {
                    Validated::Valid(x) => Some(x),
                    _ => None,
                })
                .collect();
            return Validated::Valid(f(valid_values));
        }

        // Collect all errors using extend_owned for efficiency
        let mut acc = ErrorAccumulator::new();
        for value in values {
            if let Validated::Invalid(es) = value {
                acc.extend_owned(es);
            }
        }

        Validated::Invalid(acc.into_inner())
    }

    /// Collects an iterator of Validated values into a single Validated value.
    ///
    /// If all values in the iterator are valid, returns a Valid value containing a collection of all values.
    /// If any values are invalid, returns an Invalid value containing all errors.
    ///
    /// # Type Parameters
    ///
    /// * `I`: The iterator type yielding `Validated<E, A>` items
    /// * `C`: The collection type to collect valid values into (must implement `FromIterator<A>`)
    ///
    /// # Trait Bounds
    ///
    /// * `I: Iterator<Item = Validated<E, A>>` - The iterator must yield `Validated<E, A>` items
    /// * `C: FromIterator<A> + Clone` - The collection must be constructible from an iterator of `A` values
    /// * `A: Clone` - The value type must be cloneable
    /// * `E: Clone` - The error type must be cloneable
    ///
    /// # Arguments
    ///
    /// * `iter` - Iterator of Validated values
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::validated::Validated;
    ///
    /// let values = vec![
    ///     Validated::<&str, i32>::valid(1),
    ///     Validated::<&str, i32>::valid(2),
    ///     Validated::<&str, i32>::valid(3),
    /// ];
    ///
    /// let collected: Validated<&str, Vec<i32>> = Validated::collect(values.iter().cloned());
    /// assert_eq!(collected, Validated::valid(vec![1, 2, 3]));
    ///
    /// let mixed = vec![
    ///     Validated::<&str, i32>::valid(1),
    ///     Validated::<&str, i32>::invalid("error"),
    ///     Validated::<&str, i32>::valid(3),
    /// ];
    ///
    /// let collected: Validated<&str, Vec<i32>> = Validated::collect(mixed.iter().cloned());
    /// assert!(collected.is_invalid());
    /// if let Validated::Invalid(errors) = collected {
    ///     assert_eq!(errors.as_slice(), &["error"]);
    /// }
    ///
    /// // Example with all invalid inputs
    /// let all_invalid = vec![
    ///     Validated::<&str, i32>::invalid("err1"),
    ///     Validated::<&str, i32>::invalid("err2"),
    /// ];
    /// let collected_all_invalid: Validated<&str, Vec<i32>> = Validated::collect(all_invalid.iter().cloned());
    /// assert!(collected_all_invalid.is_invalid());
    /// if let Validated::Invalid(errors) = collected_all_invalid {
    ///     assert_eq!(errors.as_slice(), &["err1", "err2"]);
    /// }
    ///
    /// // Example with an empty iterator
    /// let empty_iter: std::vec::IntoIter<Validated<&str, i32>> = vec![].into_iter();
    /// let collected_empty: Validated<&str, Vec<i32>> = Validated::collect(empty_iter);
    /// assert_eq!(collected_empty, Validated::valid(Vec::<i32>::new()));
    /// ```
    pub fn collect<I, C>(iter: I) -> Validated<E, C>
    where
        I: Iterator<Item = Validated<E, A>>,
        C: FromIterator<A> + Clone,
        A: Clone,
        E: Clone,
    {
        let (values, errors): (Vec<_>, SmallVec<[E; 8]>) = iter.fold(
            (Vec::new(), SmallVec::<[E; 8]>::new()),
            |(mut values, mut errors), item| {
                match item {
                    Validated::Valid(a) => values.push(a),
                    Validated::Invalid(es) => errors.extend(es),
                }
                (values, errors)
            },
        );

        if errors.is_empty() {
            Validated::Valid(C::from_iter(values))
        } else {
            Validated::Invalid(errors)
        }
    }

    /// Collects owned Validated values from an iterator into a single Validated value.
    ///
    /// This method is more efficient than `collect` when working with owned Validated
    /// instances, as it can move errors instead of cloning them.
    ///
    /// # Type Parameters
    ///
    /// * `I`: The iterator type yielding `Validated<E, A>` items
    /// * `C`: The collection type to collect valid values into (must implement `FromIterator<A>`)
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::validated::Validated;
    ///
    /// let values = vec![
    ///     Validated::<&str, i32>::valid(1),
    ///     Validated::<&str, i32>::valid(2),
    /// ];
    /// let result: Validated<&str, Vec<i32>> = Validated::collect_owned(values.into_iter());
    /// assert_eq!(result, Validated::valid(vec![1, 2]));
    /// ```
    #[inline]
    pub fn collect_owned<I, C>(iter: I) -> Validated<E, C>
    where
        I: Iterator<Item = Validated<E, A>>,
        C: FromIterator<A> + Clone,
    {
        let mut acc = ErrorAccumulator::new();
        let mut values = Vec::new();

        for item in iter {
            match item {
                Validated::Valid(a) => values.push(a),
                Validated::Invalid(es) => acc.extend_owned(es),
            }
        }

        if acc.buffer.is_empty() {
            Validated::Valid(C::from_iter(values))
        } else {
            Validated::Invalid(acc.into_inner())
        }
    }

    #[inline]
    pub fn to_option(&self) -> Option<A> {
        match self {
            Validated::Valid(x) => Some(x.clone()),
            _ => None,
        }
    }

    #[cfg(feature = "async")]
    /// Maps an async function over the valid value.
    ///
    /// If this is valid, applies the async function to transform the value.
    /// If this is invalid, returns the errors unchanged.
    ///
    /// # Type Parameters
    ///
    /// * `B`: The result type of the mapping function
    /// * `F`: The type of the mapping function
    /// * `Fut`: The future type returned by the mapping function
    ///
    /// # Arguments
    ///
    /// * `f` - Async function to apply to the valid value
    ///
    /// # Examples
    ///
    /// ```rust
    /// # #[cfg(feature = "async")]
    /// # async fn example() {
    /// use rustica::datatypes::validated::Validated;
    ///
    /// let valid: Validated<&str, i32> = Validated::valid(42);
    /// let mapped = valid.fmap_valid_async(|x| async move { x * 2 }).await;
    /// assert_eq!(mapped, Validated::valid(84));
    /// # }
    /// ```
    pub async fn fmap_valid_async<B, F, Fut>(&self, f: F) -> Validated<E, B>
    where
        F: Fn(A) -> Fut + Send + 'static,
        Fut: std::future::Future<Output = B> + Send,
        B: Clone + Send + 'static,
    {
        match self {
            Validated::Valid(x) => {
                let result = f(x.clone()).await;
                Validated::Valid(result)
            },
            Validated::Invalid(e) => Validated::Invalid(e.clone()),
        }
    }

    #[cfg(feature = "async")]
    /// Maps an async function over the error values.
    ///
    /// If this is invalid, applies the async function to transform each error.
    /// If this is valid, returns the value unchanged.
    ///
    /// # Type Parameters
    ///
    /// * `G`: The result type of the mapping function
    /// * `F`: The type of the mapping function
    /// * `Fut`: The future type returned by the mapping function
    ///
    /// # Arguments
    ///
    /// * `f` - Async function to apply to each error
    ///
    /// # Examples
    ///
    /// ```rust
    /// # #[cfg(feature = "async")]
    /// # async fn example() {
    /// use rustica::datatypes::validated::Validated;
    ///
    /// let invalid: Validated<&str, i32> = Validated::invalid("error");
    /// let mapped = invalid.fmap_invalid_async(|e| async move { format!("Error: {}", e) }).await;
    /// assert_eq!(mapped, Validated::invalid("Error: error".to_string()));
    /// # }
    /// ```
    pub async fn fmap_invalid_async<G, F, Fut>(&self, f: F) -> Validated<G, A>
    where
        F: Fn(E) -> Fut + Send + 'static + Clone,
        Fut: std::future::Future<Output = G> + Send,
        G: Clone + Send + 'static,
    {
        match self {
            Validated::Valid(x) => Validated::Valid(x.clone()),
            Validated::Invalid(es) => {
                // Using futures::future::join_all to run all futures concurrently
                let futures = es.iter().map(|e| f(e.clone()));
                let results = futures::future::join_all(futures).await;
                let transformed: SmallVec<[G; 8]> = results.into_iter().collect();

                Validated::Invalid(transformed)
            },
        }
    }

    #[cfg(feature = "async")]
    /// Chains an async validation operation to this Validated.
    ///
    /// If this is valid, applies the async function to the value to get another Validated.
    /// If this is invalid, returns the errors unchanged.
    ///
    /// # Type Parameters
    ///
    /// * `B`: The result type of the mapping function
    /// * `F`: The type of the mapping function
    /// * `Fut`: The future type returned by the mapping function
    ///
    /// # Arguments
    ///
    /// * `f` - Async function that returns another Validated
    ///
    /// # Examples
    ///
    /// ```rust
    /// # #[cfg(feature = "async")]
    /// # async fn example() {
    /// use rustica::datatypes::validated::Validated;
    ///
    /// let valid: Validated<&str, i32> = Validated::valid(42);
    /// let chained = valid.and_then_async(|x| async move {
    ///     if x > 50 {
    ///         Validated::<&str, String>::valid(x.to_string())
    ///     } else {
    ///         Validated::<&str, String>::invalid("Value too small")
    ///     }
    /// }).await;
    ///
    /// assert_eq!(chained, Validated::<&str, String>::invalid("Value too small"));
    /// # }
    /// ```
    pub async fn and_then_async<B, F, Fut>(&self, f: F) -> Validated<E, B>
    where
        F: Fn(A) -> Fut + Send + 'static,
        Fut: std::future::Future<Output = Validated<E, B>> + Send,
        B: Clone + Send + 'static,
    {
        match self {
            Validated::Valid(x) => f(x.clone()).await,
            Validated::Invalid(e) => Validated::Invalid(e.clone()),
        }
    }
}
