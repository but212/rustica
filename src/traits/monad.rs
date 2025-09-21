//! # Monad
//!
//! The `Monad` module provides trait definitions for implementing monadic operations
//! in Rust, a core concept in functional programming.
//!
//! A monad is a design pattern that allows for chaining operations while preserving
//! a computational context. Monads are particularly useful for handling effects like
//! optional values, error handling, state management, or asynchronous operations.
//!
//! ## Performance Characteristics
//!
//! ### Time Complexity
//! - **bind**: O(f) where f is the complexity of the bound function
//! - **join**: O(1) for flattening nested monadic structures
//! - **Chain operations**: O(f1 + f2 + ... + fn) where fi is the complexity of each bound function
//! - **Short-circuiting**: O(1) for early termination (e.g., Nothing, Left, etc.)
//!
//! ### Memory Usage
//! - **Structure Overhead**: Typically minimal - just the cost of the monadic wrapper
//! - **Function Composition**: No additional memory for function storage (immediate application)
//! - **Chain Depth**: Memory usage is generally constant regardless of bind chain depth
//! - **Context Preservation**: Memory used to maintain computational context
//!
//! ## Quick Start
//!
//! Chain computations that may fail using monadic operations:
//!
//! ```rust
//! use rustica::traits::monad::Monad;
//! use rustica::datatypes::maybe::Maybe;
//!
//! // Chain operations with bind - short-circuits on Nothing
//! let safe_divide = |x: &i32, y: &i32| -> Maybe<i32> {
//!     if *y == 0 { Maybe::Nothing } else { Maybe::Just(x / y) }
//! };
//!
//! let result = Maybe::Just(20)
//!     .bind(|x| safe_divide(x, &4))  // 20 / 4 = 5
//!     .bind(|x| safe_divide(x, &2))  // 5 / 2 = 2
//!     .bind(|x| Maybe::Just(x * 10)); // 2 * 10 = 20
//!
//! assert_eq!(result, Maybe::Just(20));
//!
//! // Automatic short-circuiting on failure
//! let failed = Maybe::Just(10)
//!     .bind(|x| safe_divide(x, &0))  // Division by zero!
//!     .bind(|x| Maybe::Just(x * 100)); // This won't execute
//!
//! assert_eq!(failed, Maybe::Nothing);
//! ```
//!
//! ## Relationship to other traits
//!
//! Monads are an extension of the Applicative functor concept, which itself extends Functors:
//!
//! ```text
//! Functor -> Applicative -> Monad
//! ```
//!
//! Each level adds more capabilities for working with values in contexts:
//! - Functors: Transforming values in a context (`fmap`)
//! - Applicatives: Applying functions in a context to values in a context (`apply`)
//! - Monads: Sequencing operations that return values in a context (`bind`)
//!
//! ## Mathematical Definition
//!
//! Monads are applicative functors with additional structure:
//! - `bind`: M A -> (A -> M B) -> M B
//! - `join`: M (M A) -> M A
//!
//! ## Laws
//!
//! For a valid Monad implementation, the following laws must hold:
//!
//! 1. Left Identity:
//!    ```text
//!    pure(x).bind(f) == f(x)
//!    ```
//!    Applying a function to a pure value should be the same as applying the function directly.
//!
//! 2. Right Identity:
//!    ```text
//!    m.bind(pure) == m
//!    ```
//!    Lifting a monadic value into a pure context should not change the value.
//!
//! 3. Associativity:
//!    ```text
//!    m.bind(f).bind(g) == m.bind(|x| f(x).bind(g))
//!    ```
//!    The order of binding operations should not matter.
//!
//! ## Examples
//!
//! ```rust
//! use rustica::traits::monad::Monad;
//! use rustica::traits::pure::Pure;
//! use rustica::traits::functor::Functor;
//! use rustica::traits::applicative::Applicative;
//! use rustica::datatypes::validated::Validated;
//!
//! // Creating a validated value
//! let valid: Validated<&str, i32> = Validated::valid(42);
//!
//! // Using bind to sequence operations
//! let result: Validated<&str, i32> = valid.bind(|x| {
//!     if *x > 0 {
//!         Validated::valid(x * 2)
//!     } else {
//!         Validated::invalid("Value must be positive")
//!     }
//! });
//!
//! assert!(matches!(result, Validated::Valid(84)));
//!
//! // Using join to flatten nested monads
//! let nested: Validated<&str, Validated<&str, i32>> = Validated::valid(Validated::valid(42));
//! let flattened: Validated<&str, i32> = nested.join();
//! assert!(matches!(flattened, Validated::Valid(42)));
//! ```
//!

use crate::traits::applicative::Applicative;

/// A trait for monads, which are applicative functors that support sequencing of operations.
///
/// Monads provide a way to chain computations while maintaining context. They are particularly
/// useful for handling effects like optional values, error handling, or state management.
///
/// # Type Parameters
/// The trait inherits type parameters from `Applicative`:
/// * `Source`: The type of values being transformed
/// * `Output<T>`: The result type after transformation
///
/// # Laws
/// For a valid Monad implementation, the following laws must hold:
///
/// 1. Left Identity:
///    pure(x).bind(f) == f(x)
///    Applying a function to a pure value should be the same as applying the function directly.
///
/// 2. Right Identity:
///    m.bind(pure) == m
///    Lifting a monadic value into a pure context should not change the value.
///
/// 3. Associativity:
///    m.bind(f).bind(g) == m.bind(|x| f(x).bind(g))
///    The order of binding operations should not matter.
///
/// 4. Applicative Consistency:
///    m.bind(|x| pure(f(x))) == m.fmap(f)
///    Binding with a pure function should be equivalent to fmap.
///
/// 5. Join Consistency:
///    m.bind(f) == m.fmap(f).join()
///    Binding can be decomposed into fmap followed by join.
pub trait Monad: Applicative {
    /// Flattens a nested monad structure.
    ///
    /// This operation is also known as "flatten" in some contexts.
    /// It takes a monad of a monad and collapses it into a single layer.
    ///
    /// # Type Parameters
    /// * `U`: The type contained in the inner monad
    ///
    /// # Returns
    /// A monad containing the inner value directly
    fn join<U>(&self) -> Self::Output<U>
    where
        Self::Source: Clone + Into<Self::Output<U>>,
        U: Clone;

    /// Applies a function that returns a monadic value to the contents of this monad.
    ///
    /// This is the core operation of a monad, allowing for sequencing of monadic computations.
    /// It is also known as "flatMap" or "chain" in some contexts.
    ///
    /// # Type Parameters
    /// * `U`: The return type of the applied function
    /// * `F`: The function type that transforms a value to a monadic value
    ///
    /// # Returns
    /// A monad containing the result of applying the function to the value
    fn bind<U, F>(&self, f: F) -> Self::Output<U>
    where
        F: Fn(&Self::Source) -> Self::Output<U>,
        Self::Source: Clone,
        U: Clone;

    /// Applies a function that returns a monadic value to the contents of this monad, consuming the original.
    ///
    /// This variant of `bind` takes ownership of `self`, allowing for more efficient implementations
    /// when the original monad is no longer needed.
    /// when the original monad is no longer needed.
    ///
    /// # Type Parameters
    /// * `U`: The return type of the applied function
    /// * `F`: The function type that transforms a value to a monadic value
    ///
    /// # Returns
    /// A new monad containing the result of applying the function to the consumed value
    fn bind_owned<U, F>(self, f: F) -> Self::Output<U>
    where
        F: Fn(Self::Source) -> Self::Output<U>,
        U: Clone,
        Self: Sized;

    /// Flattens a nested monad structure, consuming the original.
    ///
    /// This operation is like `join` but takes ownership of `self`, making it more
    /// efficient when the original monad is no longer needed.
    ///
    /// # Type Parameters
    /// * `U`: The type contained in the inner monad
    ///
    /// # Returns
    /// A monad containing the inner value directly
    fn join_owned<U>(self) -> Self::Output<U>
    where
        Self::Source: Into<Self::Output<U>>,
        U: Clone,
        Self: Sized;

    /// Alias for `bind` that matches common functional programming terminology.
    ///
    /// This method provides compatibility with other functional programming libraries
    /// and languages that use the term "flatMap".
    ///
    /// * `U`: The type of the resulting monadic value
    /// * `F`: The type of the function to apply
    ///
    /// # Parameters
    /// * `f`: A function that takes a value of type `T` and returns a monadic value
    ///
    /// # Returns
    /// A new monadic value of type `Self::Output<U>`
    #[inline]
    fn flat_map<U, F>(&self, f: F) -> Self::Output<U>
    where
        F: Fn(&Self::Source) -> Self::Output<U>,
        U: Clone,
        Self::Source: Clone,
    {
        self.bind(f)
    }

    /// Ownership-based variant of `flat_map`.
    ///
    /// This method consumes the original monad, making it more efficient when
    /// the original value is no longer needed.
    ///
    /// # Type Parameters
    /// * `U`: The type of the resulting monadic value
    /// * `F`: The type of the function to apply
    ///
    /// # Parameters
    /// * `f`: A function that takes a value of type `T` and returns a monadic value
    ///
    /// # Returns
    /// A new monadic value of type `Self::Output<U>`
    #[inline]
    fn flat_map_owned<U, F>(self, f: F) -> Self::Output<U>
    where
        F: Fn(Self::Source) -> Self::Output<U>,
        U: Clone,
        Self: Sized,
    {
        self.bind_owned(f)
    }

    /// Performs a monadic map operation with a simpler function.
    ///
    /// This is a convenience method that maps a function over the monad's value
    /// and then wraps the result in a monad using `pure`.
    ///
    /// # Type Parameters
    /// * `U`: The type of the resulting value
    /// * `F`: The type of the function to apply
    ///
    /// # Parameters
    /// * `f`: A function that takes a value of type `T` and returns a value of type `U`
    ///
    /// # Returns
    /// A new monadic value of type `Self::Output<U>`
    #[inline]
    fn map_and_pure<U: Clone, F>(&self, f: F) -> Self::Output<U>
    where
        F: Fn(&Self::Source) -> U,
        Self::Source: Clone,
        Self: crate::traits::pure::Pure,
    {
        self.bind(|x| {
            let result = f(x);
            Self::pure(&result)
        })
    }

    /// Applies a monadic function to a non-monadic value, with error handling.
    ///
    /// This method allows for safe application of a function that may fail, providing
    /// a default value in case of failure.
    ///
    /// # Type Parameters
    /// * `U`: The type of the resulting value
    /// * `E`: The error type
    /// * `F`: The type of the function to apply
    ///
    /// # Parameters
    /// * `default`: The default value to use in case of error
    /// * `f`: A function that returns a `Result<U, E>`
    ///
    /// # Returns
    /// A new monadic value of type `Self::Output<U>`
    #[inline]
    fn try_bind<U: Clone, E, F>(&self, default: &U, f: F) -> Self::Output<U>
    where
        F: Fn(&Self::Source) -> Result<Self::Output<U>, E>,
        Self::Source: Clone,
        Self: crate::traits::pure::Pure,
    {
        self.bind(|x| match f(x) {
            Ok(m) => m,
            Err(_) => Self::pure(default),
        })
    }
}

// Implementation for Option
impl<T: Clone> Monad for Option<T> {
    #[inline]
    fn join<U>(&self) -> Self::Output<U>
    where
        Self::Source: Clone + Into<Self::Output<U>>,
    {
        self.as_ref().and_then(|x| x.clone().into())
    }

    #[inline]
    fn bind<U, F>(&self, f: F) -> Self::Output<U>
    where
        F: Fn(&Self::Source) -> Self::Output<U>,
        Self::Source: Clone,
    {
        self.as_ref().and_then(f)
    }

    #[inline]
    fn bind_owned<U, F>(self, f: F) -> Self::Output<U>
    where
        F: Fn(Self::Source) -> Self::Output<U>,
        Self: Sized,
    {
        self.and_then(f)
    }

    #[inline]
    fn join_owned<U>(self) -> Self::Output<U>
    where
        Self::Source: Into<Self::Output<U>>,
        Self: Sized,
    {
        self.and_then(Into::into)
    }
}

// Implementation for Result
impl<T: Clone, E: std::fmt::Debug + Clone> Monad for Result<T, E> {
    #[inline]
    fn join<U>(&self) -> Self::Output<U>
    where
        Self::Source: Clone + Into<Self::Output<U>>,
    {
        match self {
            Ok(x) => x.clone().into(),
            Err(e) => Err(e.clone()),
        }
    }

    #[inline]
    fn bind<U, F>(&self, f: F) -> Self::Output<U>
    where
        F: Fn(&Self::Source) -> Self::Output<U>,
        Self::Source: Clone,
    {
        match self {
            Ok(x) => f(x),
            Err(e) => Err(e.clone()),
        }
    }

    #[inline]
    fn bind_owned<U, F>(self, f: F) -> Self::Output<U>
    where
        F: Fn(Self::Source) -> Self::Output<U>,
        Self: Sized,
    {
        self.and_then(f)
    }

    #[inline]
    fn join_owned<U>(self) -> Self::Output<U>
    where
        Self::Source: Into<Self::Output<U>>,
        Self: Sized,
    {
        self.and_then(Into::into)
    }
}
