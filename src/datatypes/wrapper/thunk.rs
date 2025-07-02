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
    /// This method executes the wrapped function and returns its result
    /// without consuming the thunk, allowing for repeated evaluations.
    /// Note that with impure functions, each evaluation may produce different results.
    ///
    /// # Performance
    ///
    /// - **Time Complexity**: O(F) where F is the complexity of the wrapped function
    /// - **Memory Usage**: Depends on the function's implementation and result
    /// - **Laziness**: Computation only happens when `evaluate()` is called, not when the thunk is created
    /// - **Multiple Calls**: The function will be executed each time `evaluate()` is called
    ///
    /// # Type Class Laws
    ///
    /// ## Idempotence Law (for pure functions)
    ///
    /// ```rust
    /// use rustica::datatypes::wrapper::thunk::Thunk;
    /// use rustica::traits::evaluate::Evaluate;
    ///
    /// // For pure functions, multiple evaluations should yield the same result
    /// fn verify_idempotence<T: PartialEq>(pure_fn: impl Fn() -> T) -> bool {
    ///     let thunk = Thunk::new(pure_fn);
    ///     
    ///     // Two evaluations should produce the same result
    ///     thunk.evaluate() == thunk.evaluate()
    /// }
    ///
    /// assert!(verify_idempotence(|| 42));
    /// assert!(verify_idempotence(|| "constant".to_string()));
    /// ```
    ///
    /// ## Referential Transparency Law
    ///
    /// ```rust
    /// use rustica::datatypes::wrapper::thunk::Thunk;
    /// use rustica::traits::evaluate::Evaluate;
    ///
    /// // Replacing a thunk with its evaluated result should not change behavior
    /// fn verify_ref_transparency<T: Clone + PartialEq + std::ops::Add<Output = T> + From<u8>>(x: T) -> bool {
    ///     let thunk = Thunk::new(move || x.clone());
    ///     let result = thunk.evaluate();
    ///     
    ///     // Both ways of adding 1 should yield the same result
    ///     let result1 = thunk.evaluate() + T::from(1);
    ///     let result2 = result + T::from(1);
    ///     
    ///     result1 == result2
    /// }
    ///
    /// assert!(verify_ref_transparency(41));
    /// ```
    ///
    /// # Examples
    ///
    /// Basic usage with a pure function:
    ///
    /// ```rust
    /// use rustica::datatypes::wrapper::thunk::Thunk;
    /// use rustica::traits::evaluate::Evaluate;
    ///
    /// // Create a thunk for a pure computation
    /// let factorial = Thunk::new(|| (1..=5).product::<i32>());
    ///
    /// // Evaluate it
    /// assert_eq!(factorial.evaluate(), 120); // 5! = 120
    ///
    /// // Can evaluate multiple times (thunk is not consumed)
    /// assert_eq!(factorial.evaluate(), 120);
    /// ```
    ///
    /// With an impure function that tracks state:
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
    /// assert_eq!(thunk.evaluate(), 3); // Third evaluation
    /// ```
    ///
    /// With captured environment variables:
    ///
    /// ```rust
    /// use rustica::datatypes::wrapper::thunk::Thunk;
    /// use rustica::traits::evaluate::Evaluate;
    ///
    /// let base = 10;
    /// let multiplier = 5;
    ///
    /// let calculation = Thunk::new(move || {
    ///     // The values of base and multiplier are captured
    ///     base * multiplier
    /// });
    ///
    /// assert_eq!(calculation.evaluate(), 50);
    /// ```
    ///
    /// Using with error handling:
    ///
    /// ```rust
    /// use rustica::datatypes::wrapper::thunk::Thunk;
    /// use rustica::traits::evaluate::Evaluate;
    ///
    /// fn may_fail(input: i32) -> Result<i32, &'static str> {
    ///     if input > 0 {
    ///         Ok(input * 2)
    ///     } else {
    ///         Err("Input must be positive")
    ///     }
    /// }
    ///
    /// // Create thunks for different inputs
    /// let success_thunk = Thunk::new(|| may_fail(5));
    /// let error_thunk = Thunk::new(|| may_fail(-5));
    ///
    /// assert_eq!(success_thunk.evaluate(), Ok(10));
    /// assert_eq!(error_thunk.evaluate(), Err("Input must be positive"));
    /// ```
    #[inline]
    fn evaluate(&self) -> T {
        (self.function)()
    }

    /// Evaluates the thunk by consuming it, producing the wrapped value.
    ///
    /// This method executes the wrapped function and returns its result while consuming the thunk.
    /// This can be more efficient than `evaluate()` when the thunk will not be used again, as it
    /// allows the compiler to optimize memory usage by freeing resources associated with the thunk.
    ///
    /// # Performance
    ///
    /// - **Time Complexity**: O(F) where F is the complexity of the wrapped function
    /// - **Memory Usage**: Depends on the function's implementation and result
    /// - **Ownership**: Consumes the thunk, freeing resources associated with it
    /// - **Single-Use**: The function will be executed exactly once and then the thunk is dropped
    ///
    /// # Type Class Laws
    ///
    /// ## Owned Equivalence Law
    ///
    /// ```rust
    /// use rustica::datatypes::wrapper::thunk::Thunk;
    /// use rustica::traits::evaluate::Evaluate;
    ///
    /// // evaluate_owned() should produce the same result as evaluate() for pure functions
    /// fn verify_owned_equivalence<T: PartialEq>(pure_fn: impl Fn() -> T + Clone) -> bool {
    ///     let thunk1 = Thunk::new(pure_fn.clone());
    ///     let thunk2 = Thunk::new(pure_fn);
    ///     
    ///     thunk1.evaluate() == thunk2.evaluate_owned()
    /// }
    ///
    /// assert!(verify_owned_equivalence(|| 42));
    /// assert!(verify_owned_equivalence(|| "constant".to_string()));
    /// ```
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```rust
    /// use rustica::datatypes::wrapper::thunk::Thunk;
    /// use rustica::traits::evaluate::Evaluate;
    ///
    /// let thunk = Thunk::new(|| 42);
    /// let result = thunk.evaluate_owned();
    ///
    /// assert_eq!(result, 42);
    /// // Note: thunk is consumed and can no longer be used
    /// ```
    ///
    /// With captured variables that would be moved:
    ///
    /// ```rust
    /// use rustica::datatypes::wrapper::thunk::Thunk;
    /// use rustica::traits::evaluate::Evaluate;
    ///
    /// // Create a thunk that captures a value
    /// let value = String::from("Hello");
    /// let thunk = Thunk::new(move || value + ", world!"); // value is moved into the closure
    ///
    /// // Consume the thunk to get the result
    /// let result = thunk.evaluate_owned();
    /// assert_eq!(result, "Hello, world!");
    /// ```
    ///
    /// With expensive computations or resources:
    ///
    /// ```rust
    /// use rustica::datatypes::wrapper::thunk::Thunk;
    /// use rustica::traits::evaluate::Evaluate;
    /// use std::collections::HashMap;
    ///
    /// // Create a large data structure
    /// let mut map = HashMap::new();
    /// for i in 0..1000 {
    ///     map.insert(i, i.to_string());
    /// }
    ///
    /// // Create a thunk that processes the data structure
    /// let thunk = Thunk::new(move || {
    ///     // Process the map - compute sum of keys
    ///     map.keys().sum::<i32>()
    /// });
    ///
    /// // Process once and free memory
    /// let sum = thunk.evaluate_owned();
    /// assert_eq!(sum, 499500); // Sum of 0..999
    /// ```
    ///
    /// In a processing chain:
    ///
    /// ```rust
    /// use rustica::datatypes::wrapper::thunk::Thunk;
    /// use rustica::traits::evaluate::Evaluate;
    /// use rustica::traits::evaluate::EvaluateExt;
    ///
    /// // Create and process a thunk in one chain
    /// let result = Thunk::new(|| "hello".to_string())
    ///     .fmap_evaluate_owned(|s| s.to_uppercase());
    ///
    /// assert_eq!(result, "HELLO");
    /// ```
    #[inline]
    fn evaluate_owned(self) -> T {
        (self.function)()
    }
}
