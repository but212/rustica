use crate::category::hkt::ReturnTypeConstraints;

/// A trait for types that can be evaluated to produce a value.
///
/// # Type Parameters
/// * `A` - The type of the value produced by the evaluation
///
/// # Laws
/// - Left Identity: `evaluate(duplicate(w)) = w`
/// - Right Identity: `duplicate(evaluate(w)) = w`
/// - Associativity: `evaluate(evaluate(w)) = map(duplicate)(evaluate(w))`
///
/// # Examples
///
/// ```
/// use rustica::category::hkt::ReturnTypeConstraints;
/// use rustica::category::evaluate::Evaluate;
///
/// #[derive(Debug, Clone, PartialEq)]
/// struct MyOption<A> {
///     value: Option<A>,
/// }
///
/// impl<A> MyOption<A>
/// where
///     A: ReturnTypeConstraints,
/// {
///     fn new(value: Option<A>) -> Self {
///         MyOption { value }
///     }
/// }
///
/// #[derive(Debug, Clone, PartialEq)]
/// struct MyResult<A, E> {
///     value: Result<A, E>,
/// }
///
/// impl<A, E> MyResult<A, E>
/// where
///     A: ReturnTypeConstraints,
///     E: std::fmt::Debug,
/// {
///     fn new(value: Result<A, E>) -> Self {
///         MyResult { value }
///     }
/// }
///
/// impl<A> Evaluate<A> for MyOption<A>
/// where
///     A: ReturnTypeConstraints,
/// {
///     fn evaluate(self) -> A {
///         self.value.unwrap_or_else(|| panic!("Option is None"))
///     }
/// }
///
/// impl<A, E> Evaluate<A> for MyResult<A, E>
/// where
///     A: ReturnTypeConstraints,
///     E: std::fmt::Debug,
/// {
///     fn evaluate(self) -> A {
///         self.value.unwrap_or_else(|err| panic!("Result is Err: {:?}", err))
///     }
/// }
///
/// let option_value: MyOption<i32> = MyOption::new(Some(42));
/// assert_eq!(option_value.evaluate(), 42);
///
/// let result_value: MyResult<i32, &str> = MyResult::new(Ok(42));
/// assert_eq!(result_value.evaluate(), 42);
///
/// let none_value: MyOption<i32> = MyOption::new(None);
/// let panic_value: MyResult<i32, &str> = MyResult::new(Err("error"));
///
/// // Uncommenting the following lines will cause the program to panic
/// // assert_eq!(none_value.evaluate(), 42);
/// // assert_eq!(panic_value.evaluate(), 42);
/// ```
pub trait Evaluate<A>
where
    A: ReturnTypeConstraints,
{
    /// Evaluates the computation and returns the result.
    ///
    /// # Arguments
    /// * `self` - The value to evaluate.
    ///
    /// # Returns
    /// * `A` - The result of the evaluation.
    fn evaluate(self) -> A;
}

impl<A> Evaluate<A> for Option<A>
where
    A: ReturnTypeConstraints,
{
    /// Evaluates the computation and returns the result.
    ///
    /// # Arguments
    /// * `self` - The value to evaluate.
    ///
    /// # Returns
    /// * `A` - The result of the evaluation.
    #[inline]
    fn evaluate(self) -> A {
        self.unwrap_or_else(|| panic!("Option is None"))
    }
}

impl<A, E> Evaluate<A> for Result<A, E>
where
    A: ReturnTypeConstraints,
    E: std::fmt::Debug,
{
    #[inline]
    fn evaluate(self) -> A {
        self.unwrap_or_else(|err| panic!("Result is Err: {:?}", err))
    }
}