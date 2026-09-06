//! A lightweight thunk that can be evaluated.
//!
//! This module provides the `Thunk` type, which is a statically-typed
//! function wrapper for delayed computation.
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
//!
//! // Thunks can capture and consume move-only variables
//! let string = String::from("hello");
//! let move_thunk = Thunk::new(move || string + " world");
//! assert_eq!(move_thunk.evaluate(), "hello world");
//! ```
use crate::traits::hkt::HKT;
use std::marker::PhantomData;

/// A thunk that lazily produces a value when evaluated.
///
/// This type provides a lightweight wrapper around an `FnOnce() -> T` computation.
///
/// # Type Parameters
///
/// * `F` - The function type that produces the value
/// * `T` - The type of value produced by the function
#[derive(Clone)]
pub struct Thunk<F, T> {
    function: F,
    _phantom: PhantomData<T>,
}

impl<F, T> Thunk<F, T>
where
    F: FnOnce() -> T,
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
    /// assert_eq!(thunk.evaluate(), "Hello, world!");
    /// ```
    #[inline]
    pub fn new(f: F) -> Self {
        Thunk {
            function: f,
            _phantom: PhantomData,
        }
    }

    /// Evaluates the thunk, consuming it and returning the result.
    #[inline]
    pub fn evaluate(self) -> T {
        (self.function)()
    }
}

impl<F, T> HKT for Thunk<F, T>
where
    F: FnOnce() -> T,
{
    type Source = T;
    type Output<U> = Thunk<Box<dyn FnOnce() -> U>, U>;
}

#[cfg(test)]
mod tests {
    use super::Thunk;

    #[test]
    fn pure_thunks_evaluate_correctly() {
        let thunk = Thunk::new(|| 42);
        assert_eq!(thunk.evaluate(), 42);
    }

    #[test]
    fn thunk_supports_move_only_closure() {
        let s = String::from("Rustica");
        let thunk = Thunk::new(move || {
            let mut s = s;
            s.push_str(" FP");
            s
        });
        assert_eq!(thunk.evaluate(), "Rustica FP");
    }
}
