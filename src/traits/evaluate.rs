use crate::traits::hkt::{HKT, TypeOps, AnyBox};
use std::fmt::Debug;

/// A trait for types that can be evaluated to produce a value.
///
/// This trait defines a single method `evaluate` which, when called,
/// produces a value.
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
pub trait Evaluate: HKT {
    /// Evaluates the implementor to produce a value.
    ///
    /// # Returns
    /// A boxed value resulting from the evaluation.
    ///
    /// # Panics
    /// This method may panic if the evaluation cannot produce a valid result.
    ///
    /// # Examples
    /// ```
    /// use rustica::traits::evaluate::Evaluate;
    ///
    /// let opt: Option<i32> = Some(42);
    /// assert_eq!(opt.evaluate().downcast_ref::<i32>().unwrap(), &42);
    ///
    /// let res: Result<&str, ()> = Ok("success");
    /// assert_eq!(res.evaluate().downcast_ref::<&str>().unwrap(), &"success");
    /// ```
    fn evaluate(&self) -> AnyBox;
}

impl<T> Evaluate for Option<T>
where
    T: TypeOps + 'static
{
    fn evaluate(&self) -> AnyBox {
        match self {
            Some(x) => x.clone_box(),
            None => panic!("Option is None")
        }
    }
}

impl<T, E> Evaluate for Result<T, E>
where
    T: TypeOps + 'static,
    E: TypeOps + Debug + 'static
{
    fn evaluate(&self) -> AnyBox {
        match self {
            Ok(x) => x.clone_box(),
            Err(err) => panic!("Result is Err: {:?}", err)
        }
    }
}