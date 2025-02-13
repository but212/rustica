use crate::category::hkt::ReturnTypeConstraints;

/// A trait for types that can be evaluated to produce a value.
///
/// # Type Parameters
/// * `A` - The type of the value produced by the evaluation
///
/// # Laws
/// 1. Identity: `e.evaluate().pure() = e`
/// 2. Composition: `e.evaluate().fmap(g) = (e.fmap(g)).evaluate()`
/// 3. Naturality: `η(e.evaluate()) = η(e).evaluate()`
/// 4. Purity: `pure(x).evaluate() = x`
/// 5. Strictness: `e.evaluate()` must force evaluation
/// 6. Memoization: Multiple `e.evaluate()` calls should return equivalent results
/// 7. Error Handling: `e.evaluate()` must propagate errors
/// 8. Resource Safety: `e.evaluate()` must manage resources properly
///
/// # Examples
/// ```
/// use rustica::prelude::*;
///
/// let opt: Option<i32> = Some(42);
/// assert_eq!(opt.evaluate(), 42);
///
/// let res: Result<&str, &str> = Ok("success");
/// assert_eq!(res.evaluate(), "success");
/// ```
pub trait Evaluate<A>
where
    A: ReturnTypeConstraints,
{
    fn evaluate(self) -> A;
}

impl<A> Evaluate<A> for Option<A>
where
    A: ReturnTypeConstraints,
{
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