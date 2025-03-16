//! A lightweight thunk that can be evaluated.
//!
//! This module provides the `Thunk` type, which is a statically-typed
//! function wrapper that implements the `Evaluate` trait.

use crate::traits::evaluate::Evaluate;
use crate::traits::hkt::HKT;
use std::marker::PhantomData;

/// A thunk that lazily produces a value when evaluated.
///
/// This type provides a more lightweight alternative to `BoxedFn` when:
/// - No dynamic dispatch is needed
/// - The function's exact type is known at compile time
/// - Performance is a primary concern
///
/// # Type Parameters
///
/// * `F` - The function type that produces the value
/// * `T` - The type of value produced by the function
///
/// # Examples
///
/// ```rust
/// use rustica::traits::evaluate::{Evaluate, EvaluateExt};
/// use rustica::datatypes::wrapper::thunk::Thunk;
///
/// // Create a thunk that produces a value
/// let computation = Thunk::new(|| 42);
///
/// // Evaluate by reference
/// assert_eq!(computation.evaluate(), 42);
///
/// // Using extension methods
/// let string_result: String = computation.map_evaluate(|x| x.to_string());
/// assert_eq!(string_result, "42");
///
/// // Evaluate by consuming the thunk
/// let result: i32 = computation.evaluate_owned();
/// assert_eq!(result, 42);
/// ```
pub struct Thunk<F, T>
where
    F: Fn() -> T,
{
    function: F,
    phantom: PhantomData<T>,
}

impl<F, T> Thunk<F, T>
where
    F: Fn() -> T,
{
    /// Creates a new thunk from a function.
    ///
    /// # Parameters
    ///
    /// * `f` - The function that will produce the value when evaluated
    ///
    /// # Returns
    ///
    /// A new `Thunk` instance wrapping the given function
    #[inline]
    pub fn new(f: F) -> Self {
        Thunk {
            function: f,
            phantom: PhantomData,
        }
    }
}

impl<F, T> HKT for Thunk<F, T>
where
    F: Fn() -> T,
{
    type Source = T;
    type Output<U> = Thunk<Box<dyn Fn() -> U>, U>;
}

impl<F, T> Evaluate for Thunk<F, T>
where
    F: Fn() -> T,
{
    #[inline]
    fn evaluate(&self) -> T {
        (self.function)()
    }

    // We can provide a specialized implementation since we know
    // exactly how to evaluate the thunk
    #[inline]
    fn evaluate_owned(self) -> T {
        (self.function)()
    }
}
