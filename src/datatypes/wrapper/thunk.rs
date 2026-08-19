//! # Thunk
//!
//! A lightweight thunk that can be evaluated.
//!
//! This module provides the `Thunk` type, which is a statically-typed
//! function wrapper that implements the `Evaluate` trait.
//!
//! ## Functional Programming Context
//!
//! Thunks are a fundamental concept in functional programming, representing delayed computations.
//! They enable:
//!
//! - **Lazy evaluation**: Computations are only performed when their results are needed
//! - **Separation of definition and execution**: Define what to compute separately from when to compute it
//! - **Memoization potential**: Results can be cached after first evaluation (not implemented in this type)
//!
//! ## Type Class Laws
//!
//! ### Evaluate Laws
//!
//! Thunk satisfies the following laws:
//!
//! - **Idempotence**: For pure functions, multiple evaluations produce the same result
//!   - `thunk.evaluate() == thunk.evaluate()` for any pure function thunk
//!
//! - **Referential Transparency**: A thunk can be replaced with its evaluated result without changing behavior
//!   - For any pure function thunk and any function `f`, `f(thunk.evaluate())` is equivalent to `f(value)`
//!     where `value` is the result of evaluating the thunk
//!
//! - **Composition**: Thunks compose with other higher-order operations in a predictable manner
//!   - For any thunk `t` and functions `f` and `g`, applying `f` then `g` to the evaluated result is
//!     equivalent to applying the composition of `f` and `g` to the evaluated result
//!
//! ## Type Class Implementations
//!
//! - **Evaluate**: Core functionality for executing the wrapped function
//! - **HKT**: Higher-kinded type support for working with generic type transformations
//! - **Clone**: Allows duplicating the thunk with its wrapped function
//!
//! ## Quick Start
//!
//! ```rust
//! use rustica::datatypes::wrapper::thunk::Thunk;
//!
//! // Create a thunk with a lazy computation
//! let thunk = Thunk::new(|| 2 + 3);
//!
//! // The computation isn't performed until evaluation
//! assert_eq!(thunk.evaluate(), 5);
//! assert_eq!(thunk.evaluate_owned(), 5);
//!
//! // Thunks can capture variables
//! let base = 10;
//! let complex_thunk = Thunk::new(move || base * base + 1);
//! assert_eq!(complex_thunk.evaluate(), 101);
//!
//! // Useful for expensive computations that might not be needed
//! let expensive_computation = Thunk::new(|| {
//!     (1..=1000).sum::<i32>()
//! });
//! assert_eq!(expensive_computation.evaluate(), 500500);
//! ```
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
///    let thunk = Thunk::new(|| 42);
///    assert_eq!(thunk.evaluate(), thunk.evaluate()); // Should be true for pure functions
///    ```
///
/// 2. **Referential Transparency**: Replacing a thunk with its evaluated result doesn't change behavior
///    ```rust
///    # use rustica::datatypes::wrapper::thunk::Thunk;
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
    _phantom: PhantomData<T>,
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
            _phantom: PhantomData,
        }
    }

    /// Evaluates the thunk by executing the wrapped function.
    #[inline]
    pub fn evaluate(&self) -> T {
        (self.function)()
    }

    /// Evaluates the thunk, consuming it.
    #[inline]
    pub fn evaluate_owned(self) -> T {
        (self.function)()
    }
}

impl<F, T> HKT for Thunk<F, T>
where
    F: Fn() -> T,
{
    type Source = T;
    type Output<U> = Thunk<Box<dyn Fn() -> U>, U>;
}
