//! # Monad
//!
//! The `Monad` module provides trait definitions for implementing monadic operations
//! in Rust, a core concept in functional programming.
//!
//! A monad is a design pattern that allows for chaining operations while preserving
//! a computational context. Monads are particularly useful for handling effects like
//! optional values, error handling, state management, or asynchronous operations.
//!
//! ## Quick Start
//!
//! Chain computations that may fail using monadic operations:
//!
//! ```rust
//! use rustica::traits::monad::Monad;
//!
//! // Chain operations with bind - short-circuits on None
//! let safe_divide = |x: i32, y: i32| -> Option<i32> {
//!     if y == 0 { None } else { Some(x / y) }
//! };
//!
//! let result = Some(20)
//!     .bind(|x| safe_divide(x, 4))  // 20 / 4 = 5
//!     .bind(|x| safe_divide(x, 2))  // 5 / 2 = 2
//!     .bind(|x| Some(x * 10)); // 2 * 10 = 20
//!
//! assert_eq!(result, Some(20));
//!
//! // Automatic short-circuiting on failure
//! let failed = Some(10)
//!     .bind(|x| safe_divide(x, 0))  // Division by zero!
//!     .bind(|x| Some(x * 100)); // This won't execute
//!
//! assert_eq!(failed, None);
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
    /// Applies a function that returns a monadic value to the contents of this monad, consuming self.
    fn bind<U, F>(self, f: F) -> Self::Output<U>
    where
        F: FnMut(Self::Source) -> Self::Output<U>;

    /// Flattens a nested monad structure, consuming self.
    fn join<U>(self) -> Self::Output<U>
    where
        Self::Source: Into<Self::Output<U>>;

    /// Alias for `bind` that matches common functional programming terminology.
    #[inline]
    fn flat_map<U, F>(self, f: F) -> Self::Output<U>
    where
        F: FnMut(Self::Source) -> Self::Output<U>,
        Self: Sized,
    {
        self.bind(f)
    }

    /// Performs a monadic map operation with a simpler function.
    #[inline]
    fn map_and_pure<U, F>(self, f: F) -> Self::Output<U>
    where
        F: FnMut(Self::Source) -> U,
        Self: Sized,
    {
        self.fmap(f)
    }

    /// Applies a monadic function to a non-monadic value, with error handling.
    #[inline]
    fn try_bind<U: Clone, E, F>(self, default: U, mut f: F) -> Self::Output<U>
    where
        F: FnMut(Self::Source) -> Result<Self::Output<U>, E>,
        Self: Sized,
    {
        self.bind(move |x| match f(x) {
            Ok(m) => m,
            Err(_) => Self::pure(default.clone()),
        })
    }
}

// Implementation for Option
impl<T> Monad for Option<T> {
    #[inline]
    fn bind<U, F>(self, f: F) -> Self::Output<U>
    where
        F: FnMut(Self::Source) -> Self::Output<U>,
    {
        self.and_then(f)
    }

    #[inline]
    fn join<U>(self) -> Self::Output<U>
    where
        Self::Source: Into<Self::Output<U>>,
    {
        self.and_then(Into::into)
    }
}

// Implementation for Result
impl<T, E: std::fmt::Debug + Clone> Monad for Result<T, E> {
    #[inline]
    fn bind<U, F>(self, f: F) -> Self::Output<U>
    where
        F: FnMut(Self::Source) -> Self::Output<U>,
    {
        self.and_then(f)
    }

    #[inline]
    fn join<U>(self) -> Self::Output<U>
    where
        Self::Source: Into<Self::Output<U>>,
    {
        self.and_then(Into::into)
    }
}

#[cfg(test)]
mod tests {
    use super::Monad;
    use crate::datatypes::validated::Validated;

    #[test]
    fn validated_bind_and_join_preserve_valid_values() {
        let valid: Validated<&str, i32> = Validated::valid(42);
        let result: Validated<&str, i32> = valid.bind(|value| {
            if value > 0 {
                Validated::valid(value * 2)
            } else {
                Validated::invalid("Value must be positive")
            }
        });
        assert!(matches!(result, Validated::Valid(84)));

        let nested: Validated<&str, Validated<&str, i32>> = Validated::valid(Validated::valid(42));
        let flattened: Validated<&str, i32> = nested.join();
        assert!(matches!(flattened, Validated::Valid(42)));
    }
}

#[cfg(test)]
mod standard_law_tests {
    use super::Monad;
    use crate::traits::{functor::Functor, pure::Pure};
    use quickcheck_macros::quickcheck;

    #[quickcheck]
    fn option_monad_laws(m: Option<i32>, value: i32) -> bool {
        let f = |x: i32| {
            if x > 0 {
                Some(x.saturating_mul(2))
            } else {
                None
            }
        };
        let g = |x: i32| Some(x.saturating_add(10));
        Option::<i32>::pure(value).bind(f) == f(value)
            && m.clone().bind(Option::<i32>::pure) == m
            && m.clone().bind(f).bind(g) == m.clone().bind(|x| f(x).bind(g))
            && m.fmap(f).join() == m.bind(f)
    }

    #[quickcheck]
    fn result_monad_laws(m: Result<i32, i8>, value: i32) -> bool {
        let f = |x: i32| -> Result<i32, i8> { Ok(x.saturating_mul(2)) };
        let g = |x: i32| -> Result<i32, i8> { Ok(x.saturating_add(10)) };
        Result::<i32, i8>::pure(value).bind(f) == f(value)
            && m.clone().bind(Result::<i32, i8>::pure) == m
            && m.clone().bind(f).bind(g) == m.clone().bind(|x| f(x).bind(g))
            && m.fmap(f).join() == m.bind(f)
    }

    #[test]
    fn join_handles_nested_standard_values() {
        let nested_some: Option<Option<i32>> = Some(Some(42));
        assert_eq!(nested_some.join(), Some(42));
        let nested_err: Result<Result<i32, &str>, &str> = Ok(Err("inner"));
        assert_eq!(nested_err.join(), Err("inner"));
    }
}
