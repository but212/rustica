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
//! ## Performance Characteristics
//!
//! - **Time Complexity**: O(1) for creation, O(F) for evaluation where F is the complexity of the wrapped function
//! - **Space Complexity**: O(1) for the wrapper itself, plus the size of the wrapped function
//! - **Memory Usage**: Minimal overhead - only stores the function object and a zero-sized PhantomData
//! - **Laziness**: Computation is deferred until explicitly evaluated
//!
//! ## Type Class Implementations
//!
//! - **Evaluate**: Core functionality for executing the wrapped function
//! - **HKT**: Higher-kinded type support for working with generic type transformations
//! - **Clone**: Allows duplicating the thunk with its wrapped function
//!
//! ## Documentation Notes
//!
//! For detailed practical examples demonstrating the type class laws, usage patterns, and
//! performance characteristics, please refer to the function-level documentation of the
//! relevant methods such as `evaluate`, `evaluate_owned`, and others.

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
    /// # Examples
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
    #[inline]
    fn evaluate_owned(self) -> T {
        (self.function)()
    }
}
