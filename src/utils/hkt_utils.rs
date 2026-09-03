//! # Higher-Kinded Type Utilities
//!
//! This module provides utility functions and combinators for working with higher-kinded types
//! and functional programming patterns.

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
pub fn pipeline_result<A, B, E, I, Func>(initial: A, operations: I) -> Result<B, E>
where
    Func: Fn(B) -> Result<B, E>,
    A: Into<B>,
    I: IntoIterator<Item = Func>,
{
    operations
        .into_iter()
        .try_fold(initial.into(), |value, op| op(value))
}

#[cfg(test)]
mod unit_tests {
    use super::pipeline_result;

    #[test]
    fn result_pipeline_handles_empty_input_and_short_circuits() {
        assert_eq!(
            pipeline_result::<_, i32, &'static str, _, _>(
                7,
                Vec::<fn(i32) -> Result<i32, &'static str>>::new()
            ),
            Ok(7)
        );
        fn add_one(value: i32) -> Result<i32, &'static str> {
            Ok(value + 1)
        }
        fn stop(_: i32) -> Result<i32, &'static str> {
            Err("stop")
        }
        assert_eq!(pipeline_result(1, vec![add_one, add_one]), Ok(3));
        assert_eq!(pipeline_result(1, vec![add_one, stop]), Err("stop"));
    }
}
