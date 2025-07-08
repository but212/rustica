//! Evaluation traits for functional data types in Rust.
//!
//! This module provides traits for types that can be evaluated to produce concrete values.
//! These traits are particularly useful for working with lazy computations, thunks, or
//! deferred evaluations in functional programming.
//!
//! # TODO: Future Improvements
//!
//! - **Implement More Standard Library Types**: Add implementations for more common types like `Vec<T>` and tuples
//! - **Lazy Evaluation Utilities**: Add specialized types for lazy evaluation with memoization
//! - **Performance Benchmarks**: Add documentation on performance characteristics of different evaluation approaches
//! - **Laws Documentation**: Add formal proofs and examples of evaluation laws
//! - **Integration Examples**: Show how Evaluate works with other traits like Functor and Applicative
//! - **Error Handling**: Improve error messages and recovery options for evaluation failures
//! - **Thread Safety**: Add thread-safe evaluation contexts for concurrent evaluations
//!
//! # Functional Programming Context
//!
//! In functional programming, evaluation strategies control when expressions are evaluated.
//! The `Evaluate` trait provides mechanisms to work with both eager and lazy evaluation
//! paradigms in Rust, with a focus on referential transparency and consistent results.
//!
//! # Design Philosophy
//!
//! The traits in this module are designed to be:
//!
//! - **Minimal**: Focusing on core evaluation operations
//! - **Ownership-Aware**: Providing both reference and ownership-based methods
//! - **Composable**: Working well with other functional traits
//! - **Performance-Conscious**: Using inline attributes and optimized implementations
//!
//! # Key Traits
//!
//! - `Evaluate`: Core trait for types that can be evaluated to produce values
//! - `EvaluateExt`: Extension trait with utility methods for evaluated values
//!
//! # Laws
//!
//! For a valid `Evaluate` implementation:
//!
//! 1. **Idempotence**: Evaluating an already evaluated value should yield the same result
//! 2. **Referential Transparency**: Evaluation should be consistent for the same input
//! 3. **Consistency**: Evaluating a pure value should return that value unchanged
//!
//! # Examples
//!
//! ```rust
//! use rustica::traits::hkt::HKT;
//! use rustica::traits::evaluate::{Evaluate, EvaluateExt};
//!
//! // A simple lazy computation wrapper
//! struct Lazy<T>(Box<dyn Fn() -> T>);
//!
//! impl<T> HKT for Lazy<T> {
//!     type Source = T;
//!     type Output<U> = Lazy<U>;
//! }
//!
//! impl<T: Clone> Evaluate for Lazy<T> {
//!     fn evaluate(&self) -> Self::Source {
//!         (self.0)()
//!     }
//! }
//!
//! // Usage
//! let computation: Lazy<i32> = Lazy(Box::new(|| 42));
//! assert_eq!(computation.evaluate(), 42);
//!
//! // Using extension methods
//! let mapped = computation.map_evaluate(|x| x.to_string());
//! assert_eq!(mapped, "42");
//! ```

use crate::traits::hkt::HKT;

/// A trait for types that can be evaluated to produce a value.
///
/// The Evaluate trait represents computations or expressions that can be
/// reduced to a concrete value. This is particularly useful for working with
/// lazy computations, thunks, or deferred evaluations.
///
/// # Type Parameters
/// The trait is implemented on types that implement `HKT`, where:
/// * `Source` is the type of the computation
/// * `Output<T>` represents the result type after evaluation
///
/// # Ownership-Aware API
/// This trait provides both ownership-based and reference-based methods:
/// * `evaluate` - Uses a reference to the computation (non-consuming)
/// * `evaluate_owned` - Takes ownership of the computation (consuming)
///
/// # Performance Considerations
/// - `evaluate` is preferred when you need to keep the original computation
/// - `evaluate_owned` may be more efficient for types where taking ownership avoids cloning
/// - All methods are marked with `#[inline]` to encourage compiler optimization
pub trait Evaluate: HKT
where
    Self: Sized,
{
    /// Evaluates the computation to produce a concrete value without consuming the computation.
    ///
    /// This method reduces a computation or expression to its final value by reference.
    /// The evaluation process should be consistent and produce the same
    /// result for the same input.
    ///
    /// # Returns
    /// The concrete value resulting from the evaluation
    fn evaluate(&self) -> Self::Source;

    /// Evaluates the computation to produce a concrete value by consuming the computation.
    ///
    /// This method takes ownership of the computation and reduces it to its final value.
    /// It may be more efficient than `evaluate` for types where taking ownership
    /// allows avoiding cloning or other overhead.
    ///
    /// # Returns
    /// The concrete value resulting from the evaluation
    ///
    /// # Default Implementation
    /// By default, this calls `evaluate` and clones the result.
    /// For types where taking ownership enables optimization, consider overriding this.
    fn evaluate_owned(self) -> Self::Source
    where
        Self::Source: Clone,
    {
        self.evaluate()
    }
}

/// Extension trait providing additional utility methods for `Evaluate` implementers.
///
/// This trait adds convenience methods for working with evaluatable computations,
/// such as mapping over the result of evaluation or combining multiple evaluations.
pub trait EvaluateExt: Evaluate {
    /// Maps a function over the result of evaluating this computation by reference.
    ///
    /// # Type Parameters
    /// * `F` - The mapping function type
    /// * `U` - The output type after mapping
    ///
    /// # Parameters
    /// * `f` - A function that transforms the evaluation result
    ///
    /// # Returns
    /// The transformed result after evaluation and mapping
    #[inline]
    fn fmap_evaluate<F, U>(&self, f: F) -> U
    where
        F: Fn(Self::Source) -> U,
    {
        f(self.evaluate())
    }

    /// Maps a function over the result of evaluating this computation by reference.
    ///
    /// This method evaluates the computation first, then applies the function to the result.
    ///
    /// # Type Parameters
    /// * `F` - The mapping function type
    /// * `U` - The output type after mapping
    ///
    /// # Parameters
    /// * `f` - A function that transforms the evaluation result
    ///
    /// # Returns
    /// The transformed result after evaluation and mapping
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::traits::evaluate::{Evaluate, EvaluateExt};
    /// use rustica::datatypes::wrapper::thunk::Thunk;
    ///
    /// let computation: Thunk<_, i32> = Thunk::new(|| 42);
    /// let stringified: String = computation.fmap_evaluate(|x| x.to_string());
    /// assert_eq!(stringified, "42");
    /// ```
    #[inline]
    fn map_evaluate<F, U>(&self, f: F) -> U
    where
        F: Fn(Self::Source) -> U,
    {
        f(self.evaluate())
    }

    /// Maps a function over the result of evaluating this computation by consuming it.
    ///
    /// # Type Parameters
    /// * `F` - The mapping function type
    /// * `U` - The output type after mapping
    ///
    /// # Parameters
    /// * `f` - A function that transforms the evaluation result
    ///
    /// # Returns
    /// The transformed result after evaluation and mapping
    #[inline]
    fn fmap_evaluate_owned<F, U>(self, f: F) -> U
    where
        F: Fn(Self::Source) -> U,
        Self::Source: Clone,
    {
        f(self.evaluate())
    }

    /// Maps a function over the result of evaluating this computation by consuming it.
    ///
    /// This method consumes the computation, evaluates it, and applies the function to the result.
    /// It may be more efficient than `map_evaluate` for types where taking ownership
    /// allows avoiding unnecessary cloning.
    ///
    /// # Type Parameters
    /// * `F` - The mapping function type
    /// * `U` - The output type after mapping
    ///
    /// # Parameters
    /// * `f` - A function that transforms the evaluation result
    ///
    /// # Returns
    /// The transformed result after evaluation and mapping
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::traits::evaluate::{Evaluate, EvaluateExt};
    /// use rustica::datatypes::wrapper::thunk::Thunk;
    ///
    /// let computation: Thunk<_, i32> = Thunk::new(|| 42);
    /// let stringified: String = computation.fmap_evaluate_owned(|x| x.to_string());
    /// assert_eq!(stringified, "42");
    /// ```
    #[inline]
    fn map_evaluate_owned<F, U>(self, f: F) -> U
    where
        F: Fn(Self::Source) -> U,
        Self::Source: Clone,
    {
        f(self.evaluate_owned())
    }

    /// Evaluates this computation and then another computation based on the result.
    ///
    /// This method is useful for chaining dependent computations.
    ///
    /// # Type Parameters
    /// * `F` - The function type
    /// * `C` - The second computation type
    ///
    /// # Parameters
    /// * `f` - A function that produces a new computation based on this one's result
    ///
    /// # Returns
    /// The result of evaluating the second computation
    #[inline]
    fn bind_evaluate<F, C>(&self, f: F) -> C::Source
    where
        F: Fn(Self::Source) -> C,
        C: Evaluate,
        Self::Source: Clone,
    {
        f(self.evaluate()).evaluate()
    }

    /// Evaluates this computation and then another computation based on the result.
    ///
    /// This method is similar to `bind_evaluate` but with a more monadic naming convention.
    ///
    /// # Type Parameters
    /// * `F` - The function type
    /// * `C` - The second computation type
    ///
    /// # Parameters
    /// * `f` - A function that produces a new computation based on this one's result
    ///
    /// # Returns
    /// The result of evaluating the second computation
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::traits::evaluate::{Evaluate, EvaluateExt};
    /// use rustica::datatypes::wrapper::thunk::Thunk;
    ///
    /// let computation: Thunk<_, i32> = Thunk::new(|| 42);
    /// let chained = computation.bind_evaluate(|x| Thunk::new(move || x + 1));
    /// assert_eq!(chained, 43);
    /// ```
    #[inline]
    fn and_then_evaluate<F, C>(&self, f: F) -> C::Source
    where
        F: Fn(Self::Source) -> C,
        C: Evaluate,
        Self::Source: Clone,
    {
        f(self.evaluate()).evaluate()
    }

    /// Evaluates this computation, consumes it, and then another computation based on the result.
    ///
    /// This ownership-based variant of `and_then_evaluate` is useful when the original
    /// computation is no longer needed after evaluation.
    ///
    /// # Type Parameters
    /// * `F` - The function type
    /// * `C` - The second computation type
    ///
    /// # Parameters
    /// * `f` - A function that produces a new computation based on this one's result
    ///
    /// # Returns
    /// The result of evaluating the second computation
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::traits::evaluate::{Evaluate, EvaluateExt};
    /// use rustica::datatypes::wrapper::thunk::Thunk;
    ///
    /// let computation: Thunk<_, i32> = Thunk::new(|| 42);
    /// let chained = computation.bind_evaluate_owned(|x| Thunk::new(move || x + 1));
    /// assert_eq!(chained, 43);
    /// ```
    #[inline]
    fn bind_evaluate_owned<F, C>(self, f: F) -> C::Source
    where
        F: Fn(Self::Source) -> C,
        C: Evaluate,
        Self::Source: Clone,
    {
        f(self.evaluate()).evaluate()
    }

    /// Evaluates this computation by consuming it, then feeds the result into another computation.
    ///
    /// This method is similar to `and_then_evaluate` but takes ownership of the original
    /// computation, which can be more efficient when the computation is no longer needed.
    ///
    /// # Type Parameters
    /// * `F` - The function type
    /// * `C` - The second computation type
    ///
    /// # Parameters
    /// * `f` - A function that produces a new computation based on this one's result
    ///
    /// # Returns
    /// The result of evaluating the second computation
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::traits::evaluate::{Evaluate, EvaluateExt};
    /// use rustica::datatypes::wrapper::thunk::Thunk;
    ///
    /// let computation: Thunk<_, i32> = Thunk::new(|| 42);
    /// let chained = computation.and_then_evaluate_owned(|x| Thunk::new(move || x + 1));
    /// assert_eq!(chained, 43);
    /// ```
    #[inline]
    fn and_then_evaluate_owned<F, C>(self, f: F) -> C::Source
    where
        F: Fn(Self::Source) -> C,
        C: Evaluate,
        Self::Source: Clone,
    {
        f(self.evaluate_owned()).evaluate()
    }

    /// Combines the evaluation of this computation with another.
    ///
    /// # Type Parameters
    /// * `C` - The other computation type
    /// * `F` - The combining function type
    /// * `O` - The output type of the combining function
    ///
    /// # Parameters
    /// * `other` - Another evaluatable computation
    /// * `f` - A function that combines the results of both computations
    ///
    /// # Returns
    /// The combined result after evaluating both computations
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::traits::evaluate::{Evaluate, EvaluateExt};
    /// use rustica::datatypes::wrapper::thunk::Thunk;
    ///
    /// let computation1 = Thunk::new(|| 42);
    /// let computation2 = Thunk::new(|| "answer");
    /// let combined = computation1.combine_evaluate(&computation2, |num, text| {
    ///     format!("The {} is {}", text, num)
    /// });
    /// assert_eq!(combined, "The answer is 42");
    /// ```
    #[inline]
    fn combine_evaluate<C, F, O>(&self, other: &C, f: F) -> O
    where
        C: Evaluate,
        F: Fn(Self::Source, C::Source) -> O,
        Self::Source: Clone,
        C::Source: Clone,
    {
        f(self.evaluate(), other.evaluate())
    }

    /// Combines the evaluation of this computation with another, consuming both.
    ///
    /// This ownership-based variant of `combine_evaluate` takes ownership of both
    /// computations, which can be more efficient when they're no longer needed.
    ///
    /// # Type Parameters
    /// * `C` - The other computation type
    /// * `F` - The combining function type
    /// * `O` - The output type of the combining function
    ///
    /// # Parameters
    /// * `other` - Another evaluatable computation
    /// * `f` - A function that combines the results of both computations
    ///
    /// # Returns
    /// The combined result after evaluating both computations
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::traits::evaluate::{Evaluate, EvaluateExt};
    /// use rustica::datatypes::wrapper::thunk::Thunk;
    ///
    /// let computation1 = Thunk::new(|| 42);
    /// let computation2 = Thunk::new(|| "answer");
    /// let combined = computation1.combine_evaluate_owned(computation2, |num, text| {
    ///     format!("The {} is {}", text, num)
    /// });
    /// assert_eq!(combined, "The answer is 42");
    /// ```
    #[inline]
    fn combine_evaluate_owned<C, F, O>(self, other: C, f: F) -> O
    where
        C: Evaluate,
        F: Fn(Self::Source, C::Source) -> O,
        Self::Source: Clone,
        C::Source: Clone,
    {
        f(self.evaluate(), other.evaluate())
    }

    /// Evaluates this computation and returns the result if a predicate is satisfied,
    /// otherwise returns None.
    ///
    /// # Type Parameters
    /// * `F` - The predicate function type
    ///
    /// # Parameters
    /// * `pred` - A predicate that tests the evaluation result
    ///
    /// # Returns
    /// An Option containing the evaluation result if the predicate is satisfied, or None
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::traits::evaluate::{Evaluate, EvaluateExt};
    /// use rustica::datatypes::wrapper::thunk::Thunk;
    ///
    /// let computation: Thunk<_, i32> = Thunk::new(|| 42);
    /// let filtered: Option<i32> = computation.filter_evaluate(|&x| x > 0);
    /// assert_eq!(filtered, Some(42));
    ///
    /// let computation: Thunk<_, i32> = Thunk::new(|| -10);
    /// let filtered: Option<i32> = computation.filter_evaluate(|&x| x > 0);
    /// assert_eq!(filtered, None); // Filtered out because it doesn't match the predicate
    /// ```
    #[inline]
    fn filter_evaluate<F>(&self, pred: F) -> Option<Self::Source>
    where
        F: Fn(&Self::Source) -> bool,
        Self::Source: Clone,
    {
        let result = self.evaluate();
        if pred(&result) { Some(result) } else { None }
    }

    /// Evaluates this computation by consuming it and returns the result if a predicate is satisfied,
    /// otherwise returns None.
    ///
    /// # Type Parameters
    /// * `F` - The predicate function type
    ///
    /// # Parameters
    /// * `pred` - A predicate that tests the evaluation result
    ///
    /// # Returns
    /// An Option containing the evaluation result if the predicate is satisfied, or None
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::traits::evaluate::{Evaluate, EvaluateExt};
    /// use rustica::datatypes::wrapper::thunk::Thunk;
    ///
    /// let computation: Thunk<_, i32> = Thunk::new(|| 42);
    /// let filtered: Option<i32> = computation.filter_evaluate_owned(|&x| x > 0);
    /// assert_eq!(filtered, Some(42));
    ///
    /// let computation: Thunk<_, i32> = Thunk::new(|| -10);
    /// let filtered: Option<i32> = computation.filter_evaluate_owned(|&x| x > 0);
    /// assert_eq!(filtered, None); // Filtered out because it doesn't match the predicate
    /// ```
    #[inline]
    fn filter_evaluate_owned<F>(self, pred: F) -> Option<Self::Source>
    where
        F: Fn(&Self::Source) -> bool,
        Self::Source: Clone,
    {
        let result = self.evaluate_owned();
        if pred(&result) { Some(result) } else { None }
    }
}

// Blanket implementation for all types that implement Evaluate
impl<T: Evaluate> EvaluateExt for T {}

// Implementation for common standard library types

/// Implementation of `Evaluate` for `Option<T>`.
///
/// This implementation treats `Option<T>` as an evaluatable computation,
/// where `None` represents a failed computation and `Some(T)` represents
/// a successful computation with result `T`.
///
/// # Examples
///
/// ```rust
/// use rustica::traits::evaluate::{Evaluate, EvaluateExt};
///
/// // A successful computation
/// let some_value: Option<i32> = Some(42);
/// assert_eq!(some_value.evaluate(), 42);
///
/// // A failed computation
/// let none_value: Option<i32> = None;
/// let result = std::panic::catch_unwind(|| {
///     none_value.evaluate()
/// });
/// assert!(result.is_err()); // Panics as expected for None
///
/// // Using extension methods
/// let doubled: i32 = some_value.map_evaluate(|x| x * 2);
/// assert_eq!(doubled, 84);
/// ```
impl<T: Clone> Evaluate for Option<T> {
    #[inline]
    fn evaluate(&self) -> T {
        match self {
            Some(value) => value.clone(),
            None => panic!("Cannot evaluate None"),
        }
    }

    #[inline]
    fn evaluate_owned(self) -> T {
        self.expect("Cannot evaluate None")
    }
}

/// Implementation of `Evaluate` for `Result<T, E>`.
///
/// This implementation treats `Result<T, E>` as an evaluatable computation,
/// where `Err(E)` represents a failed computation and `Ok(T)` represents
/// a successful computation with result `T`.
///
/// # Examples
///
/// ```rust
/// use rustica::traits::evaluate::{Evaluate, EvaluateExt};
///
/// // A successful computation
/// let ok_result: Result<i32, &str> = Ok(42);
/// assert_eq!(ok_result.evaluate(), 42);
///
/// // A failed computation
/// let err_result: Result<i32, &str> = Err("computation failed");
/// let result = std::panic::catch_unwind(|| {
///     err_result.evaluate()
/// });
/// assert!(result.is_err()); // Panics as expected for Err
///
/// // Using extension methods with explicit type annotation
/// let ok_result: Result<i32, &str> = Ok(42);
/// let doubled: i32 = ok_result.map_evaluate(|x| x * 2);
/// assert_eq!(doubled, 84);
/// ```
impl<T: Clone, E: Clone + std::fmt::Debug> Evaluate for Result<T, E> {
    #[inline]
    fn evaluate(&self) -> T {
        match self {
            Ok(value) => value.clone(),
            Err(e) => panic!("Cannot evaluate Err: {e:?}"),
        }
    }

    #[inline]
    fn evaluate_owned(self) -> T {
        self.expect("Cannot evaluate Err")
    }
}
