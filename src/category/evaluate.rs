use crate::category::hkt::ReturnTypeConstraints;

/// A trait for types that can be evaluated to produce a value.
///
/// # Type Parameters
/// * `A` - The type of the value produced by the evaluation
pub trait Evaluate<A>
where
    A: ReturnTypeConstraints,
{
    /// Evaluates the computation and returns the result.
    ///
    /// # Returns
    /// The result of the evaluation.
    fn evaluate(self) -> A;
}

impl<A> Evaluate<A> for Option<A>
where
    A: ReturnTypeConstraints,
{
    fn evaluate(self) -> A {
        self.unwrap_or_else(|| panic!("Option is None"))
    }
}

impl<A, E> Evaluate<A> for Result<A, E>
where
    A: ReturnTypeConstraints,
    E: std::fmt::Debug,
{
    fn evaluate(self) -> A {
        self.unwrap_or_else(|err| panic!("Result is Err: {:?}", err))
    }
}
