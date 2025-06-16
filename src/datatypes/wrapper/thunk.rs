//! A lightweight thunk that can be evaluated.
//!
//! This module provides the `Thunk` type, which is a statically-typed
//! function wrapper that implements the `Evaluate` trait.
//!
//! # Examples
//!
//! ```rust
//! use rustica::traits::evaluate::{Evaluate, EvaluateExt};
//! use rustica::datatypes::wrapper::thunk::Thunk;
//!
//! // Create a thunk that produces a value
//! let computation = Thunk::new(|| 42);
//!
//! // Evaluate by reference
//! assert_eq!(computation.evaluate(), 42);
//!
//! // Using extension methods
//! let string_result: String = computation.fmap_evaluate(|x| x.to_string());
//! assert_eq!(string_result, "42");
//!
//! // Evaluate by consuming the thunk
//! let result: i32 = computation.evaluate_owned();
//! assert_eq!(result, 42);
//! ```
//!
//! # Performance Characteristics
//!
//! - Time Complexity: O(1) for creation, O(F) for evaluation where F is the complexity of the wrapped function
//! - Space Complexity: O(1) for the wrapper itself, plus the size of the wrapped function
//! - Memory Usage: Minimal overhead - only stores the function object and a zero-sized PhantomData

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
/// # Evaluate Laws
///
/// Thunk satisfies the following laws:
///
/// 1. **Idempotence**: Evaluating multiple times produces the same result for pure functions
///    ```rust
///    # use rustica::datatypes::wrapper::thunk::Thunk;
///    # use rustica::traits::evaluate::Evaluate;
///    let thunk = Thunk::new(|| 42);
///    assert_eq!(thunk.evaluate(), thunk.evaluate()); // Should be true for pure functions
///    ```
///
/// 2. **Referential Transparency**: Replacing a thunk with its evaluated result doesn't change behavior
///    ```rust
///    # use rustica::datatypes::wrapper::thunk::Thunk;
///    # use rustica::traits::evaluate::Evaluate;
///    let thunk = Thunk::new(|| 42);
///    let value = thunk.evaluate();
///    
///    // These should be equivalent operations:
///    let result1 = thunk.evaluate() + 1;
///    let result2 = value + 1;
///    assert_eq!(result1, result2);
///    ```
#[derive(Clone)]
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
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::wrapper::thunk::Thunk;
    /// use rustica::traits::evaluate::Evaluate;
    ///
    /// // Create a simple thunk
    /// let thunk = Thunk::new(|| "Hello, world!".to_string());
    ///
    /// // Create a thunk with captured variables
    /// let base = 10;
    /// let calculation = Thunk::new(move || base * 5);
    /// assert_eq!(calculation.evaluate(), 50);
    ///
    /// // Create a thunk with potentially expensive computation
    /// let complex = Thunk::new(|| {
    ///     // This won't execute until evaluate() is called
    ///     (0..5).fold(1, |acc, x| acc * (x + 1))
    /// });
    /// assert_eq!(complex.evaluate(), 120); // 5!
    /// ```
    ///
    /// # Performance
    ///
    /// - Time Complexity: O(1) - Just stores the function
    /// - Space Complexity: O(1) plus the size of the function closure
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
    /// Evaluates the thunk by reference, producing the wrapped value.
    ///
    /// # Returns
    ///
    /// The result of executing the wrapped function
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::wrapper::thunk::Thunk;
    /// use rustica::traits::evaluate::Evaluate;
    ///
    /// let counter = std::cell::Cell::new(0);
    /// let thunk = Thunk::new(|| {
    ///     counter.set(counter.get() + 1);
    ///     counter.get()
    /// });
    ///
    /// assert_eq!(thunk.evaluate(), 1); // First evaluation
    /// assert_eq!(thunk.evaluate(), 2); // Second evaluation
    /// ```
    ///
    /// # Performance
    ///
    /// - Time Complexity: O(F) where F is the complexity of the wrapped function
    /// - Does not consume the thunk, allowing for repeated evaluations
    #[inline]
    fn evaluate(&self) -> T {
        (self.function)()
    }

    /// Evaluates the thunk by consuming it, producing the wrapped value.
    ///
    /// This can be more efficient than `evaluate()` when the thunk is no longer needed.
    ///
    /// # Returns
    ///
    /// The result of executing the wrapped function
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::wrapper::thunk::Thunk;
    /// use rustica::traits::evaluate::Evaluate;
    ///
    /// // Create a thunk that captures a value
    /// let value = String::from("Hello");
    /// let thunk = Thunk::new(move || value.clone() + ", world!");
    ///
    /// // Consume the thunk to get the result
    /// let result = thunk.evaluate_owned();
    /// assert_eq!(result, "Hello, world!");
    /// ```
    ///
    /// # Performance
    ///
    /// - Time Complexity: O(F) where F is the complexity of the wrapped function
    /// - More efficient than `evaluate()` when the thunk won't be used again
    #[inline]
    fn evaluate_owned(self) -> T {
        (self.function)()
    }
}
