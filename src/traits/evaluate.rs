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
/// # Laws
/// For a valid Evaluate implementation:
///
/// 1. Idempotence:
///    evaluate(evaluate(x)) == evaluate(x)
///
/// 2. Referential Transparency:
///    let y = evaluate(x);
///    evaluate(x) == y
///
/// 3. Consistency:
///    evaluate(pure(x)) == x
///
/// # Examples
///
/// Basic implementation for a lazy computation:
/// ```rust
/// use rustica::traits::hkt::HKT;
/// use rustica::traits::evaluate::Evaluate;
///
/// struct Lazy<T>(Box<dyn Fn() -> T>);
///
/// impl<T> HKT for Lazy<T> {
///     type Source = T;
///     type Output<U> = Lazy<U>;
/// }
///
/// impl<T> Evaluate for Lazy<T> {
///     fn evaluate(&self) -> Self::Source {
///         (self.0)()
///     }
/// }
///
/// // Usage
/// let computation = Lazy(Box::new(|| 42));
/// assert_eq!(computation.evaluate(), 42);
/// ```
///
/// # Design Notes
///
/// 1. Evaluation should be consistent and produce the same result for
///    the same input (referential transparency).
///
/// 2. The evaluate operation may have side effects, but these should be
///    documented and consistent.
///
/// 3. Consider caching evaluation results if the computation is expensive
///    and the same value will be needed multiple times.
pub trait Evaluate: HKT {
    /// Evaluates the computation to produce a concrete value.
    ///
    /// This method reduces a computation or expression to its final value.
    /// The evaluation process should be consistent and produce the same
    /// result for the same input.
    ///
    /// # Returns
    /// The concrete value resulting from the evaluation
    fn evaluate(&self) -> Self::Source;
}