//! A wrapper for boxed functions that can be evaluated.
//!
//! This module provides the `BoxedFn` type, which wraps a boxed function
//! in a structure that implements the `Evaluate` trait.

use crate::traits::evaluate::Evaluate;
use crate::traits::hkt::HKT;

/// A wrapper for boxed functions that produce values.
///
/// This type allows treating a boxed function as an evaluatable computation.
/// The function is executed when the computation is evaluated.
///
/// # Type Parameters
///
/// * `T` - The return type of the boxed function
///
/// # Examples
///
/// ```rust
/// use rustica::traits::evaluate::{Evaluate, EvaluateExt};
/// use rustica::traits::hkt::HKT;
/// use rustica::datatypes::wrapper::boxed_fn::BoxedFn;
///
/// // Create a boxed function that computes a value
/// let computation = BoxedFn(Box::new(|| 42));
///
/// // Evaluate the computation
/// assert_eq!(computation.evaluate(), 42);
///
/// // Map the result to another type
/// let string_result: String = computation.map_evaluate(|x| x.to_string());
/// assert_eq!(string_result, "42");
///
/// // Chain computations
/// let first_computation = BoxedFn(Box::new(|| 10));
/// let second_result: i32 = first_computation.and_then_evaluate(|x| {
///     BoxedFn(Box::new(move || x * 2))
/// });
/// assert_eq!(second_result, 20);
/// ```
pub struct BoxedFn<T>(pub Box<dyn Fn() -> T>);

impl<T> HKT for BoxedFn<T> {
    type Source = T;
    type Output<U> = BoxedFn<U>;
}

impl<T> Evaluate for BoxedFn<T> {
    #[inline]
    fn evaluate(&self) -> T {
        (self.0)()
    }

    // For BoxedFn, we can optimize by not using the default implementation
    // since calling the function directly is more efficient than cloning the result
    #[inline]
    fn evaluate_owned(self) -> T
    where
        T: Clone,
    {
        (self.0)()
    }
}
