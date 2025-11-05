//! # Higher-Kinded Type Utilities
//!
//! This module provides utility functions and combinators for working with higher-kinded types
//! and functional programming patterns. These utilities simplify common operations and enable
//! more expressive functional code in Rust.
//!
//! ## Categories of Utilities
//!
//! - **Collection Operations**: Functions like `filter_map` and `zip_with` that work with collections
//! - **Pipeline Functions**: Utilities like `pipeline_option` and `pipeline_result` for chaining operations
//! - **Function Transformers**: Utilities that transform functions to work with different contexts
//! - **Composition Utilities**: Functions for combining and composing operations
//!
//! These utilities complement the traits in the `traits` module and provide ready-to-use
//! implementations of common functional programming patterns.
//!
//! ## Performance Characteristics
//!
//! ### Collection Operations
//! - **filter_map**: O(n) time complexity where n is the collection size
//! - **zip_with**: O(min(n, m)) where n and m are the sizes of input collections
//! - **Memory Usage**: Linear with output size, single-pass processing for efficiency
//!
//! ### Pipeline Operations
//! - **pipeline_option/pipeline_result**: O(f1 + f2 + ... + fn) where fi is each function complexity
//! - **Short-circuiting**: Early termination on None/Error for optimal performance
//!
//! ### Function Transformers
//! - **compose**: O(f + g) where f and g are the composed function complexities

// ===== Collection Operations =====

/// Filters and maps a collection in a single pass.
///
/// This function combines filtering and mapping operations for better performance
/// and cleaner code. It first filters elements using the predicate and then
/// applies the transformation function to the filtered elements.
///
/// # Type Parameters
///
/// * `A`: The type of elements in the input collection
/// * `B`: The type of elements in the output collection
/// * `C`: The type of the input collection
/// * `P`: The type of the predicate function
/// * `F`: The type of the mapping function
///
/// # Arguments
///
/// * `collection`: The input collection to filter and map
/// * `predicate`: A function that decides which elements to keep
/// * `f`: A function that transforms kept elements
///
/// # Returns
///
/// A new vector containing the transformed elements that passed the predicate
///
/// # Examples
///
/// ```rust
/// use rustica::utils::hkt_utils::filter_map;
///
/// let numbers = vec![1, 2, 3, 4, 5, 6];
///
/// // Keep only even numbers and square them
/// let result = filter_map(
///     numbers,
///     |&n| n % 2 == 0,  // Keep only even numbers
///     |n| n * n        // Square the kept numbers
/// );
///
/// assert_eq!(result, vec![4, 16, 36]);
/// ```
#[inline]
pub fn filter_map<A, B, C, P, F>(collection: C, predicate: P, f: F) -> Vec<B>
where
    C: IntoIterator<Item = A>,
    P: Fn(&A) -> bool,
    F: Fn(A) -> B,
{
    let iter = collection.into_iter();
    let (lower, _) = iter.size_hint();

    // Pre-allocate with estimated capacity (assume ~50% pass filter)
    let estimated_capacity = std::cmp::max(lower / 2, 8);
    let mut result = Vec::with_capacity(estimated_capacity);

    for item in iter {
        if predicate(&item) {
            result.push(f(item));
        }
    }

    result
}

/// Combines elements from two collections using a combining function.
///
/// This function pairs elements from two collections and applies a combining function
/// to each pair, producing a new collection of the results. The length of the output
/// will be the minimum of the lengths of the two input collections.
///
/// # Type Parameters
///
/// * `A`: The type of elements in the first input collection
/// * `B`: The type of elements in the second input collection
/// * `C`: The type of elements in the output collection
/// * `F`: The type of the combining function
///
/// # Arguments
///
/// * `xs`: The first input collection
/// * `ys`: The second input collection
/// * `f`: A function that combines elements from both collections
///
/// # Returns
///
/// A new vector containing the combined elements
///
/// # Examples
///
/// ```rust
/// use rustica::utils::hkt_utils::zip_with;
///
/// let numbers = vec![1, 2, 3, 4];
/// let multipliers = vec![10, 20, 30];
///
/// // Multiply corresponding elements
/// let result = zip_with(
///     numbers,
///     multipliers,
///     |n, m| n * m
/// );
///
/// assert_eq!(result, vec![10, 40, 90]);  // Note: only 3 elements (minimum length)
/// ```
#[inline]
pub fn zip_with<A, B, C, F>(xs: Vec<A>, ys: Vec<B>, f: F) -> Vec<C>
where
    F: Fn(A, B) -> C,
{
    xs.into_iter().zip(ys).map(|(x, y)| f(x, y)).collect()
}

// ===== Pipeline Functions =====

/// Chains a sequence of operations that may return `Option<T>`.
///
/// This function allows you to chain multiple operations where each operation
/// may fail (returning `None`). The chain short-circuits on the first `None`.
///
/// # Type Parameters
///
/// * `A`: The type of the initial value
/// * `B`: The type that the initial value is converted to and operations work with
/// * `Func`: The type of the operation functions
///
/// # Arguments
///
/// * `initial`: The starting value for the pipeline
/// * `operations`: A sequence of operations to apply
///
/// # Returns
///
/// The final transformed value, or `None` if any operation failed
///
/// # Examples
///
/// ```rust
/// use rustica::utils::hkt_utils::pipeline_option;
///
/// // Define operations that work with our pipeline
/// let parse_int = |s: &str| -> Option<i32> { s.parse::<i32>().ok() };
///
/// // Create operations for our pipeline
/// let double_if_even = |n: i32| -> Option<i32> {
///     if n % 2 == 0 { Some(n * 2) } else { None }
/// };
///
/// // Chain operations - this will succeed
/// let result1 = pipeline_option(
///     10,  // Initial i32 value
///     vec![double_if_even]
/// );
/// assert_eq!(result1, Some(20));  // 10 -> Some(20)
///
/// // Chain operations - this will fail
/// let result2 = pipeline_option(
///     11,  // Initial i32 value (odd number)
///     vec![double_if_even]
/// );
/// assert_eq!(result2, None);
/// ```
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
///
/// This function allows you to chain multiple operations where each operation
/// may fail (returning `Err`). The chain short-circuits on the first `Err`.
///
/// # Type Parameters
///
/// * `A`: The type of the initial value
/// * `B`: The type that the initial value is converted to and operations work with
/// * `E`: The error type
/// * `Func`: The type of the operation functions
///
/// # Arguments
///
/// * `initial`: The starting value for the pipeline
/// * `operations`: A sequence of operations to apply
///
/// # Returns
///
/// The final transformed value, or the first error encountered
///
/// # Examples
///
/// ```rust
/// use rustica::utils::hkt_utils::pipeline_result;
///
/// // Some example operations that might fail
/// let checked_div = |n: i32| -> Result<i32, &'static str> {
///     if n % 3 == 0 {
///         Ok(n / 3)
///     } else {
///         Err("not divisible by 3")
///     }
/// };
///
/// let checked_add = |n: i32| -> Result<i32, &'static str> {
///     if n < 100 {
///         Ok(n + 10)
///     } else {
///         Err("result too large")
///     }
/// };
///
/// // Chain operations - this will succeed
/// let result1 = pipeline_result(
///     9,  // Initial value
///     vec![checked_div, checked_add]
/// );
/// assert_eq!(result1, Ok(13));  // (9 / 3) + 10 = 13
///
/// // Chain operations - this will fail at the first operation
/// let result2 = pipeline_result(
///     10,  // Initial value (not divisible by 3)
///     vec![checked_div, checked_add]
/// );
/// assert_eq!(result2, Err("not divisible by 3"));
/// ```
#[inline]
pub fn pipeline_result<A, B, E, Func>(initial: A, operations: Vec<Func>) -> Result<B, E>
where
    Func: Fn(B) -> Result<B, E>,
    A: Into<B>,
{
    let mut iter = operations.into_iter();

    // Handle the first operation or just use the initial value
    let initial_result = match iter.next() {
        Some(first_op) => first_op(initial.into()),
        None => Ok(initial.into()),
    };

    // Apply the remaining operations
    iter.fold(initial_result, |acc, op| match acc {
        Ok(value) => op(value),
        Err(e) => Err(e),
    })
}

/// Convenience wrapper around `pipeline_result` with a more intuitive name.
///
/// This function is identical to `pipeline_result` but with a name that better
/// reflects its error handling behavior.
///
/// # Type Parameters
///
/// * `A`: The type of the initial value
/// * `B`: The type that the initial value is converted to and operations work with
/// * `E`: The error type
/// * `F`: The type of the operation functions
///
/// # Arguments
///
/// * `initial`: The starting value for the pipeline
/// * `operations`: A sequence of operations to apply
///
/// # Returns
///
/// The final transformed value, or the first error encountered
///
/// # Examples
///
/// ```rust
/// use rustica::utils::hkt_utils::try_pipeline;
///
/// // Define operations that may fail
/// let parse_as_f64 = |s: &str| -> Result<f64, &'static str> {
///     s.parse::<f64>().map_err(|_| "parse error")
/// };
///
/// let sqrt = |n: f64| -> Result<f64, &'static str> {
///     if n >= 0.0 {
///         Ok(n.sqrt())
///     } else {
///         Err("cannot take square root of negative number")
///     }
/// };
///
/// // Chain operations with try_pipeline
/// let result = try_pipeline(
///     "16".to_string(),
///     vec![
///         Box::new(|s: String| parse_as_f64(&s).map(|n| n.to_string())) as Box<dyn Fn(String) -> Result<String, &'static str>>,
///         Box::new(|s: String| parse_as_f64(&s).and_then(sqrt).map(|n| n.to_string()))
///     ]
/// );
///
/// assert_eq!(result.map(|s| s.parse::<f64>().unwrap()), Ok(4.0));
/// ```
#[inline]
pub fn try_pipeline<A, B, E, F>(initial: A, operations: Vec<F>) -> Result<B, E>
where
    F: Fn(B) -> Result<B, E>,
    A: Into<B>,
{
    pipeline_result(initial, operations)
}

// ===== Function Transformers =====

/// Lifts a function to work with `Option` values.
///
/// This function transforms a regular function into one that works with
/// `Option` values by applying the function only when the option is `Some`.
///
/// # Type Parameters
///
/// * `A`: The input type of the original function
/// * `B`: The output type of the original function
/// * `F`: The type of the function to lift
///
/// # Arguments
///
/// * `f`: The function to lift to work with `Option`
///
/// # Returns
///
/// A new function that takes an `Option<A>` and returns an `Option<B>`
///
/// # Examples
///
/// ```rust
/// use rustica::utils::hkt_utils::lift_option;
///
/// // Define a regular function
/// let double = |x: i32| x * 2;
///
/// // Lift it to work with Option
/// let option_double = lift_option(double);
///
/// // Use the lifted function
/// assert_eq!(option_double(Some(5)), Some(10));
/// assert_eq!(option_double(None), None);
///
/// // We can also use it in a pipeline
/// let values: Vec<Option<i32>> = vec![Some(1), None, Some(3)];
/// let doubled: Vec<Option<i32>> = values.into_iter().map(option_double).collect();
/// assert_eq!(doubled, vec![Some(2), None, Some(6)]);
/// ```
#[inline]
pub fn lift_option<A, B, F>(f: F) -> impl Fn(Option<A>) -> Option<B>
where
    F: Fn(A) -> B,
{
    move |opt| opt.map(&f)
}

/// Maps a function over a `Result` value.
///
/// This function applies a transformation to the success value of a `Result`,
/// leaving any error value unchanged.
///
/// # Type Parameters
///
/// * `A`: The success type of the input `Result`
/// * `B`: The success type of the output `Result`
/// * `E`: The error type of both input and output `Result`
/// * `F`: The type of the mapping function
///
/// # Arguments
///
/// * `result`: The input `Result` value
/// * `f`: The function to apply to the success value
///
/// # Returns
///
/// A new `Result` with the success value transformed
///
/// # Examples
///
/// ```rust
/// use rustica::utils::hkt_utils::map_result;
///
/// // Example Result values
/// let ok_value: Result<i32, &str> = Ok(5);
/// let err_value: Result<i32, &str> = Err("error occurred");
///
/// // Transform the success value
/// let mapped_ok = map_result(ok_value, |n| n * 2);
/// assert_eq!(mapped_ok, Ok(10));
///
/// // Error values pass through unchanged
/// let mapped_err = map_result(err_value, |n| n * 2);
/// assert_eq!(mapped_err, Err("error occurred"));
/// ```
#[inline]
pub fn map_result<A, B, E, F>(result: Result<A, E>, f: F) -> Result<B, E>
where
    F: Fn(A) -> B,
{
    result.map(f)
}

// ===== Multi-Operation Utilities =====

/// Applies multiple operations to a single input value.
///
/// This function takes a value and a collection of operations, applies each
/// operation to the input value, and collects the results. This is useful when
/// you need to transform a single input in multiple different ways.
///
/// # Type Parameters
///
/// * `A`: The type of the input value
/// * `B`: The type of the output values
/// * `F`: The type of the operation functions
///
/// # Arguments
///
/// * `input`: The input value to transform
/// * `operations`: A collection of operations to apply
///
/// # Returns
///
/// A vector containing the results of applying each operation to the input
///
/// # Examples
///
/// ```rust
/// use rustica::utils::hkt_utils::fan_out;
///
/// // Single input value
/// let value = 10;
///
/// // Multiple operations to apply
/// let ops = vec![
///     |n: i32| n + 5,
///     |n: i32| n * 2,
///     |n: i32| n * n
/// ];
///
/// // Apply all operations to the input
/// let results = fan_out(value, ops);
///
/// // We get the result of each operation
/// assert_eq!(results, vec![15, 20, 100]);
/// ```
#[inline]
pub fn fan_out<A: Clone, B, F>(input: A, operations: Vec<F>) -> Vec<B>
where
    F: Fn(A) -> B,
{
    operations.into_iter().map(|op| op(input.clone())).collect()
}

/// Composes multiple transformations into a single function.
///
/// This function takes a sequence of transformations and composes them into
/// a single function that applies all transformations in sequence.
///
/// # Type Parameters
///
/// * `A`: The input and intermediate type
/// * `B`: The final output type
///
/// # Arguments
///
/// * `transformations`: A vector of transformation functions
///
/// # Returns
///
/// A boxed function that applies all transformations in sequence
///
/// # Examples
///
/// ```rust
/// use rustica::utils::hkt_utils::compose_all;
/// use std::ops::Add;
///
/// // Define some transformations
/// let add_5: Box<dyn Fn(i32) -> i32> = Box::new(|n| n + 5);
/// let multiply_2: Box<dyn Fn(i32) -> i32> = Box::new(|n| n * 2);
/// let square: Box<dyn Fn(i32) -> i32> = Box::new(|n| n * n);
///
/// // Compose all transformations
/// let composed: Box<dyn Fn(i32) -> i32> = compose_all(vec![add_5, multiply_2, square]);
///
/// // ((10 + 5) * 2)² = 30² = 900
/// assert_eq!(composed(10), 900);
/// ```
#[inline]
pub fn compose_all<A, B>(transformations: Vec<Box<dyn Fn(A) -> A>>) -> Box<dyn Fn(A) -> B>
where
    A: 'static,
    B: 'static + From<A>,
{
    Box::new(move |input| {
        let result = transformations.iter().fold(input, |acc, f| f(acc));
        B::from(result)
    })
}
