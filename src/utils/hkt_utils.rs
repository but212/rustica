//! # Higher-Kinded Type Utilities
//!
//! This module provides utility functions and combinators for working with higher-kinded types
//! and functional programming patterns.

// ===== Pipeline Functions =====

/// Chains a sequence of operations that may return `Option<T>`.
#[inline]
pub fn pipeline_option<A, B, I, Func>(initial: A, operations: I) -> Option<B>
where
    Func: Fn(B) -> Option<B>,
    A: Into<B>,
    I: IntoIterator<Item = Func>,
{
    operations
        .into_iter()
        .try_fold(initial.into(), |acc, op| op(acc))
}

/// Chains a sequence of operations that may return `Result<T, E>`.
#[inline]
pub fn pipeline_result<A, B, E, Func>(initial: A, operations: Vec<Func>) -> Result<B, E>
where
    Func: Fn(B) -> Result<B, E>,
    A: Into<B>,
{
    operations
        .into_iter()
        .try_fold(initial.into(), |value, op| op(value))
}
