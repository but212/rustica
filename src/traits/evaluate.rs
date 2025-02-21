use crate::traits::hkt::TypeConstraints;

/// A trait for types that can be evaluated to produce a value.
///
/// This trait defines a single method `evaluate` which, when called,
/// produces a value of type `A`.
///
/// # Type Parameters
/// * `A` - The type of the value produced by the evaluation
///
/// # Laws
/// 
/// An Evaluate instance must satisfy these laws:
/// 
/// 1. Identity: For any evaluable `e`,
///    `e.evaluate().pure() = e`
/// 2. Composition: For any evaluable `e` and function `g`,
///    `e.evaluate().fmap(g) = (e.fmap(g)).evaluate()`
/// 3. Naturality: For any natural transformation `η` and evaluable `e`,
///    `η(e.evaluate()) = η(e).evaluate()`
/// 4. Purity: For any value `x`,
///    `pure(x).evaluate() = x`
pub trait Evaluate<A>
where
    A: TypeConstraints,
{
    /// Evaluates the implementor to produce a value of type `A`.
    ///
    /// # Returns
    /// A value of type `A` resulting from the evaluation.
    ///
    /// # Panics
    /// This method may panic if the evaluation cannot produce a valid result.
    ///
    /// # Examples
    /// ```
    /// use rustica::traits::evaluate::Evaluate;
    ///
    /// let opt: Option<i32> = Some(42);
    /// assert_eq!(opt.evaluate(), 42);
    ///
    /// let res: Result<&str, ()> = Ok("success");
    /// assert_eq!(res.evaluate(), "success");
    /// ```
    fn evaluate(self) -> A;
}

impl<A> Evaluate<A> for Option<A>
where
    A: TypeConstraints,
{
    #[inline]
    fn evaluate(self) -> A {
        self.unwrap_or_else(|| panic!("Option is None"))
    }
}

impl<A, E> Evaluate<A> for Result<A, E>
where
    A: TypeConstraints,
    E: std::fmt::Debug,
{
    #[inline]
    fn evaluate(self) -> A {
        self.unwrap_or_else(|err| panic!("Result is Err: {:?}", err))
    }
}