//! # Categorical Utilities
//!
//! This module provides utility functions inspired by category theory concepts,
//! specifically designed to work with Rust's type safety and ownership system.
//! These utilities extend common operations on `Option`, `Result`, and other
//! functorial types while maintaining purity and immutability.
//!
//! ## Design Philosophy
//!
//! The utilities follow the principle: **Categorical Correctness > Type Safety > Performance**
//!
//! - **Categorical Correctness**: All functions preserve the mathematical laws of
//!   functors, applicatives, and monads
//! - **Type Safety**: Leverages Rust's generics and ownership to ensure memory safety
//! - **Performance**: Zero-cost abstractions with inline closures for minimal overhead
//!
//! ## Core Concepts
//!
//! ### Functor-Inspired Mapping
//! Functions that preserve structure while transforming contents, following the
//! functor laws of identity and composition.
//!
//! ### Monad-Inspired Chaining
//! Functions that enable sequencing of computations with context, following the
//! monad laws of left identity, right identity, and associativity.
//!
//! ### Immutability and Purity
//! All functions avoid mutable state and side effects, promoting functional
//! programming patterns that are safe and predictable.
//!
//! ## Performance Characteristics
//!
//! ### Time Complexity
//! - **Map operations**: O(f) where f is the complexity of the mapping function
//! - **Flat map operations**: O(f) where f is the complexity of the chaining function
//! - **Curry operations**: O(1) - Zero-cost function transformation
//! - **Compose operations**: O(f + g) where f and g are the composed function complexities
//!
//! ### Memory Usage
//! - **Zero-cost abstractions**: No additional heap allocation beyond what's needed
//! - **Move semantics**: Leverages Rust's ownership to avoid unnecessary copies
//! - **Iterator-based**: Uses lazy evaluation where possible for memory efficiency
//!
//! ## Quick Start
//!
//! ```rust
//! use rustica::utils::categorical_utils::*;
//!
//! // Functor-inspired mapping
//! let maybe_num = Some(42);
//! let maybe_string = map_option(maybe_num, |x| x.to_string());
//! assert_eq!(maybe_string, Some("42".to_string()));
//!
//! // Monad-inspired chaining
//! let result = flat_map_result(Ok(10), |x| {
//!     if x > 0 { Ok(x * 2) } else { Err("negative") }
//! });
//! assert_eq!(result, Ok(20));
//!
//! // Function composition
//! let add_one = |x: i32| x + 1;
//! let double = |x: i32| x * 2;
//! let composed = compose(add_one, double);
//! assert_eq!(composed(5), 12); // (5 + 1) * 2
//!
//! // Argument flipping for different perspectives
//! let subtract = |x: i32, y: i32| x - y;
//! let flipped_subtract = flip(subtract);
//! assert_eq!(flipped_subtract(3, 10), 7); // 10 - 3 = 7
//! ```

use crate::traits::monoid::Monoid;

// ===== Functor-Inspired Mapping Helpers =====

/// Maps a function over an `Option` value, preserving the structure.
///
/// This function applies the functor pattern to `Option` types, following the
/// mathematical laws of functors:
/// - Identity: `map_option(opt, |x| x) == opt`
/// - Composition: `map_option(map_option(opt, f), g) == map_option(opt, |x| g(f(x)))`
///
/// # Performance
///
/// - **Time Complexity**: O(f) where f is the complexity of the mapping function
/// - **Memory Usage**: Zero additional allocation beyond the result
/// - **Optimization**: Function is inlined for zero-cost abstraction
///
/// # Arguments
///
/// * `opt` - The `Option` value to map over
/// * `f` - The function to apply to the contained value (if `Some`)
///
/// # Returns
///
/// A new `Option` with the function applied to the contained value
///
/// # Examples
///
/// ```rust
/// use rustica::utils::categorical_utils::map_option;
///
/// // Transform a Some value
/// let result = map_option(Some(42), |x| x * 2);
/// assert_eq!(result, Some(84));
///
/// // None values remain None
/// let result: Option<i32> = map_option(None, |x: i32| x * 2);
/// assert_eq!(result, None);
///
/// // Chaining transformations
/// let result = map_option(
///     map_option(Some("hello"), |s| s.to_uppercase()),
///     |s| format!("{}!", s)
/// );
/// assert_eq!(result, Some("HELLO!".to_string()));
/// ```
///
/// # Type Class Laws
///
/// This function satisfies the functor laws:
///
/// ```rust
/// use rustica::utils::categorical_utils::map_option;
///
/// // Identity Law: mapping with identity function returns the original
/// let original = Some(42);
/// assert_eq!(map_option(original, |x| x), original);
///
/// // Composition Law: mapping f then g equals mapping the composition
/// let f = |x: i32| x + 1;
/// let g = |x: i32| x * 2;
/// let option = Some(5);
///
/// let result1 = map_option(map_option(option, f), g);
/// let result2 = map_option(option, |x| g(f(x)));
/// assert_eq!(result1, result2);
/// ```
#[inline]
pub fn map_option<T, U, F>(opt: Option<T>, f: F) -> Option<U>
where
    F: FnOnce(T) -> U,
{
    opt.map(f)
}

/// Maps a function over the success value of a `Result`, preserving error cases.
///
/// This function applies the functor pattern to `Result` types, transforming
/// the success value while leaving error cases unchanged.
///
/// # Performance
///
/// - **Time Complexity**: O(f) for `Ok` cases, O(1) for `Err` cases
/// - **Memory Usage**: Zero additional allocation beyond the result
/// - **Short-circuiting**: `Err` values bypass the function completely
///
/// # Arguments
///
/// * `result` - The `Result` value to map over
/// * `f` - The function to apply to the success value (if `Ok`)
///
/// # Returns
///
/// A new `Result` with the function applied to the success value
///
/// # Examples
///
/// ```rust
/// use rustica::utils::categorical_utils::map_result;
///
/// // Transform a success value
/// let result: Result<String, &str> = map_result(Ok(42), |x| x.to_string());
/// assert_eq!(result, Ok("42".to_string()));
///
/// // Error values remain unchanged
/// let result: Result<String, &str> = map_result(Err("error"), |x: i32| x.to_string());
/// assert_eq!(result, Err("error"));
/// ```
#[inline]
pub fn map_result<T, U, E, F>(result: Result<T, E>, f: F) -> Result<U, E>
where
    F: FnOnce(T) -> U,
{
    result.map(f)
}

/// Maps a function over both the error and success values of a `Result`.
///
/// This function provides bimap functionality for `Result` types, allowing
/// transformation of both the success and error cases simultaneously.
///
/// # Performance
///
/// - **Time Complexity**: O(f) for `Ok` cases, O(g) for `Err` cases
/// - **Memory Usage**: Zero additional allocation beyond the result
/// - **Branch Optimization**: Compiler can optimize based on the result variant
///
/// # Arguments
///
/// * `result` - The `Result` value to map over
/// * `f_ok` - Function to apply to the success value
/// * `f_err` - Function to apply to the error value
///
/// # Returns
///
/// A new `Result` with both success and error cases potentially transformed
///
/// # Examples
///
/// ```rust
/// use rustica::utils::categorical_utils::bimap_result;
///
/// // Transform both success and error cases
/// let success: Result<i32, &str> = Ok(42);
/// let result = bimap_result(success, |x| x * 2, |e| e.to_uppercase());
/// assert_eq!(result, Ok(84));
///
/// let error: Result<i32, &str> = Err("error");
/// let result = bimap_result(error, |x| x * 2, |e| e.to_uppercase());
/// assert_eq!(result, Err("ERROR".to_string()));
/// ```
#[inline]
pub fn bimap_result<T, U, E, F, G, H>(result: Result<T, E>, f_ok: G, f_err: H) -> Result<U, F>
where
    G: FnOnce(T) -> U,
    H: FnOnce(E) -> F,
{
    match result {
        Ok(value) => Ok(f_ok(value)),
        Err(error) => Err(f_err(error)),
    }
}

// ===== Monad-Inspired Chaining Helpers =====

/// Chains computations on `Option` values using monadic bind.
///
/// This function applies the monad pattern to `Option` types, enabling
/// sequencing of computations that may fail. It follows the monad laws:
/// - Left Identity: `flat_map_option(Some(x), f) == f(x)`
/// - Right Identity: `flat_map_option(opt, Some) == opt`
/// - Associativity: `flat_map_option(flat_map_option(opt, f), g) == flat_map_option(opt, |x| flat_map_option(f(x), g))`
///
/// # Performance
///
/// - **Time Complexity**: O(f) where f is the complexity of the chaining function
/// - **Memory Usage**: Zero additional allocation beyond the result
/// - **Short-circuiting**: `None` values bypass the function completely
///
/// # Arguments
///
/// * `opt` - The `Option` value to chain from
/// * `f` - The function that returns an `Option` (monadic operation)
///
/// # Returns
///
/// The result of the monadic computation
///
/// # Examples
///
/// ```rust
/// use rustica::utils::categorical_utils::flat_map_option;
///
/// // Chain successful computations
/// let safe_divide = |x: i32, y: i32| -> Option<i32> {
///     if y != 0 { Some(x / y) } else { None }
/// };
///
/// let result = flat_map_option(Some(20), |x| safe_divide(x, 4));
/// assert_eq!(result, Some(5));
///
/// // Chain operations that may fail
/// let result = flat_map_option(Some(10), |x| safe_divide(x, 0));
/// assert_eq!(result, None);
///
/// // None values short-circuit
/// let result = flat_map_option(None, |x: i32| Some(x * 2));
/// assert_eq!(result, None);
/// ```
#[inline]
pub fn flat_map_option<T, U, F>(opt: Option<T>, f: F) -> Option<U>
where
    F: FnOnce(T) -> Option<U>,
{
    opt.and_then(f)
}

/// Chains computations on `Result` values using monadic bind.
///
/// This function applies the monad pattern to `Result` types, enabling
/// sequencing of computations that may fail with error propagation.
///
/// # Performance
///
/// - **Time Complexity**: O(f) for `Ok` cases, O(1) for `Err` cases
/// - **Memory Usage**: Zero additional allocation beyond the result
/// - **Error Propagation**: `Err` values are propagated without executing the function
///
/// # Arguments
///
/// * `result` - The `Result` value to chain from
/// * `f` - The function that returns a `Result` (monadic operation)
///
/// # Returns
///
/// The result of the monadic computation
///
/// # Examples
///
/// ```rust
/// use rustica::utils::categorical_utils::flat_map_result;
///
/// // Chain successful computations
/// let parse_and_double = |s: &str| -> Result<i32, &'static str> {
///     s.parse::<i32>().map(|x| x * 2).map_err(|_| "parse error")
/// };
///
/// let result = flat_map_result(Ok("21"), parse_and_double);
/// assert_eq!(result, Ok(42));
///
/// // Error propagation
/// let result = flat_map_result(Err("initial error"), parse_and_double);
/// assert_eq!(result, Err("initial error"));
/// ```
#[inline]
pub fn flat_map_result<T, U, E, F>(result: Result<T, E>, f: F) -> Result<U, E>
where
    F: FnOnce(T) -> Result<U, E>,
{
    result.and_then(f)
}

// ===== Function Composition Utilities =====

/// Composes two functions, creating a new function that applies the first then the second.
///
/// This function implements mathematical function composition: `(g ∘ f)(x) = g(f(x))`.
/// The composition follows the associativity law and provides a pure functional approach
/// to combining operations.
///
/// # Performance
///
/// - **Time Complexity**: O(f + g) where f and g are the complexities of the composed functions
/// - **Memory Usage**: Zero-cost abstraction - no additional allocation
/// - **Optimization**: Functions are inlined for optimal performance
///
/// # Arguments
///
/// * `f` - The first function to apply
/// * `g` - The second function to apply to the result of the first
///
/// # Returns
///
/// A new function that represents the composition of `f` and `g`
///
/// # Examples
///
/// ```rust
/// use rustica::utils::categorical_utils::compose;
///
/// let add_one = |x: i32| x + 1;
/// let double = |x: i32| x * 2;
///
/// // Compose functions: first add one, then double
/// let add_one_then_double = compose(add_one, double);
/// assert_eq!(add_one_then_double(5), 12); // (5 + 1) * 2
///
/// // Function composition is associative
/// let triple = |x: i32| x * 3;
/// let comp1 = compose(compose(add_one, double), triple);
/// let comp2 = compose(add_one, compose(double, triple));
/// assert_eq!(comp1(2), comp2(2)); // Both equal 18
/// ```
#[inline]
pub fn compose<A, B, C, F, G>(f: F, g: G) -> impl Fn(A) -> C
where
    F: Fn(A) -> B,
    G: Fn(B) -> C,
{
    move |x| g(f(x))
}

/// Flips the arguments of a two-argument function.
///
/// This function takes a function `f(a, b) -> c` and returns a function `f(b, a) -> c`,
/// effectively swapping the order of arguments. This is useful for partial application
/// and function composition.
///
/// # Performance
///
/// - **Time Complexity**: O(f) where f is the complexity of the original function
/// - **Memory Usage**: Zero-cost abstraction - no additional allocation
/// - **Optimization**: Function is inlined for minimal overhead
///
/// # Arguments
///
/// * `f` - The function whose arguments should be flipped
///
/// # Returns
///
/// A function with arguments in reverse order
///
/// # Examples
///
/// ```rust
/// use rustica::utils::categorical_utils::flip;
///
/// // Original function that subtracts second from first
/// let subtract = |x: i32, y: i32| x - y;
///
/// // Flip the arguments
/// let flipped_subtract = flip(subtract);
///
/// assert_eq!(subtract(10, 3), 7);  // 10 - 3 = 7
/// assert_eq!(flipped_subtract(10, 3), -7);  // 3 - 10 = -7
///
/// // Useful for creating different partial applications
/// let divide = |x: f64, y: f64| x / y;
/// let flipped_divide = flip(divide);
///
/// // Now we can easily create "divide into X" functions
/// let numbers = vec![8.0, 4.0, 2.0];
/// let halved: Vec<f64> = numbers.iter().map(|x| flipped_divide(2.0, *x)).collect();
/// assert_eq!(halved, vec![4.0, 2.0, 1.0]);
/// ```
#[inline]
pub fn flip<A, B, C, F>(f: F) -> impl Fn(B, A) -> C
where
    F: Fn(A, B) -> C,
{
    move |b, a| f(a, b)
}

// ===== Collection Utilities =====

/// Filters and maps over a collection in a single pass, preserving only successful transformations.
///
/// This function combines filtering with mapping and Option handling, applying a function
/// that returns `Option<U>` and keeping only the `Some` results. This is equivalent to
/// the Haskell `mapMaybe` function.
///
/// # Performance
///
/// - **Time Complexity**: O(n * f) where n is collection size and f is function complexity
/// - **Memory Usage**: Linear with the number of successful transformations
/// - **Single Pass**: Efficient iteration without intermediate collections
///
/// # Arguments
///
/// * `iter` - An iterator over the input collection
/// * `f` - A function that transforms elements to `Option<U>`
///
/// # Returns
///
/// A vector containing only the successful transformations
///
/// # Examples
///
/// ```rust
/// use rustica::utils::categorical_utils::filter_map_collect;
///
/// let numbers = vec!["1", "not_a_number", "3", "4", "not_a_number"];
///
/// // Parse numbers, keeping only successful parses
/// let parsed = filter_map_collect(
///     numbers.iter(),
///     |s| s.parse::<i32>().ok()
/// );
///
/// assert_eq!(parsed, vec![1, 3, 4]);
///
/// // Transform and filter in one step
/// let doubled_evens = filter_map_collect(
///     (1..=10).into_iter(),
///     |x| if x % 2 == 0 { Some(x * 2) } else { None }
/// );
///
/// assert_eq!(doubled_evens, vec![4, 8, 12, 16, 20]);
/// ```
#[inline]
pub fn filter_map_collect<I, T, U, F>(iter: I, f: F) -> Vec<U>
where
    I: IntoIterator<Item = T>,
    F: Fn(T) -> Option<U>,
{
    let iter = iter.into_iter();
    let (lower, _) = iter.size_hint();

    // Estimate capacity (assume ~50% items pass the filter)
    let estimated_capacity = std::cmp::max(lower / 2, 8);
    let mut result = Vec::with_capacity(estimated_capacity);

    for item in iter {
        if let Some(value) = f(item) {
            result.push(value);
        }
    }

    result
}

/// Sequences a vector of `Option` values into an `Option` of vector.
///
/// This function converts `Vec<Option<T>>` to `Option<Vec<T>>`, succeeding only
/// if all elements are `Some`. This is a common operation in functional programming
/// for handling collections of optional values.
///
/// # Performance
///
/// - **Time Complexity**: O(n) where n is the vector length
/// - **Memory Usage**: Linear with vector size for successful case
/// - **Short-circuiting**: Returns `None` immediately on first `None` encountered
///
/// # Arguments
///
/// * `options` - A vector of `Option` values
///
/// # Returns
///
/// `Some(Vec<T>)` if all elements are `Some`, otherwise `None`
///
/// # Examples
///
/// ```rust
/// use rustica::utils::categorical_utils::sequence_options;
///
/// // All Some values
/// let all_some = vec![Some(1), Some(2), Some(3)];
/// let result = sequence_options(all_some);
/// assert_eq!(result, Some(vec![1, 2, 3]));
///
/// // Contains None
/// let has_none = vec![Some(1), None, Some(3)];
/// let result = sequence_options(has_none);
/// assert_eq!(result, None);
///
/// // Empty vector
/// let empty: Vec<Option<i32>> = vec![];
/// let result = sequence_options(empty);
/// assert_eq!(result, Some(vec![]));
/// ```
pub fn sequence_options<T>(options: Vec<Option<T>>) -> Option<Vec<T>> {
    options.into_iter().collect()
}

/// Sequences a vector of `Result` values into a `Result` of vector.
///
/// This function converts `Vec<Result<T, E>>` to `Result<Vec<T>, E>`, succeeding only
/// if all elements are `Ok`. Returns the first error encountered if any exist.
///
/// # Performance
///
/// - **Time Complexity**: O(n) where n is the vector length
/// - **Memory Usage**: Linear with vector size for successful case
/// - **Error Propagation**: Returns first error immediately without processing remaining elements
///
/// # Arguments
///
/// * `results` - A vector of `Result` values
///
/// # Returns
///
/// `Ok(Vec<T>)` if all elements are `Ok`, otherwise the first `Err` encountered
///
/// # Examples
///
/// ```rust
/// use rustica::utils::categorical_utils::sequence_results;
///
/// // All Ok values
/// let all_ok: Vec<Result<i32, &str>> = vec![Ok(1), Ok(2), Ok(3)];
/// let result = sequence_results(all_ok);
/// assert_eq!(result, Ok(vec![1, 2, 3]));
///
/// // Contains Err
/// let has_err: Vec<Result<i32, &str>> = vec![Ok(1), Err("error"), Ok(3)];
/// let result = sequence_results(has_err);
/// assert_eq!(result, Err("error"));
/// ```
pub fn sequence_results<T, E>(results: Vec<Result<T, E>>) -> Result<Vec<T>, E> {
    results.into_iter().collect()
}

/// Folds an iterator using a monoid's combine operation with automatic wrapping.
///
/// This function converts each element to the monoid type `W` and combines them
/// using the monoid's `combine` operation. If the iterator is empty, returns the
/// monoid's identity element (`empty()`).
///
/// # Performance
///
/// - **Time Complexity**: O(n) where n is the iterator length
/// - **Memory Usage**: Constant space beyond iterator storage
/// - **Optimization**: Marked with `#[inline]` for compiler optimization
///
/// # Type Parameters
///
/// * `I` - Iterator type that yields items of type `T`
/// * `T` - Item type that can be converted to the monoid wrapper `W`
/// * `W` - Monoid wrapper type (Sum, Product, First, Last, Min, Max, etc.)
///
/// # Arguments
///
/// * `iter` - An iterator of items to fold
///
/// # Returns
///
/// The result of combining all elements, or the identity element if empty
///
/// # Examples
///
/// ```rust
/// use rustica::utils::categorical_utils::fold_with;
/// use rustica::datatypes::wrapper::{sum::Sum, product::Product, first::First, last::Last, min::Min, max::Max};
/// use rustica::traits::identity::Identity;
///
/// // Sum operations
/// let numbers = vec![1, 2, 3, 4, 5];
/// let total: Sum<i32> = fold_with(numbers);
/// assert_eq!(*total.value(), 15);
///
/// // Product operations
/// let factors = vec![2, 3, 4];
/// let product: Product<i32> = fold_with(factors);
/// assert_eq!(*product.value(), 24);
///
/// // First operations
/// let values = vec![Some(10), None, Some(20)];
/// let first: First<i32> = fold_with(values.clone());
/// assert_eq!(*first.value(), 10);
///
/// // First operations
/// let direct_values = vec![42, 99, 7];
/// let first_direct: First<i32> = fold_with(direct_values);
/// assert_eq!(*first_direct.value(), 42);
///
/// // Last operations
/// let last: Last<i32> = fold_with(values);
/// assert_eq!(*last.value(), 20);
///
/// // Last operations
/// let last_direct: Last<i32> = fold_with(vec![1, 2, 3]);
/// assert_eq!(*last_direct.value(), 3);
///
/// // Min operations
/// let unsorted = vec![5, 2, 8, 1, 9];
/// let minimum: Min<i32> = fold_with(unsorted);
/// assert_eq!(*minimum.value(), 1);
///
/// // Max operations
/// let values = vec![3, 7, 2, 9, 4];
/// let maximum: Max<i32> = fold_with(values);
/// assert_eq!(*maximum.value(), 9);
///
/// // Empty iterator returns identity
/// let empty: Vec<i32> = vec![];
/// let zero: Sum<i32> = fold_with(empty);
/// assert_eq!(*zero.value(), 0);
/// ```
#[inline]
pub fn fold_with<I, T, W>(iter: I) -> W
where
    I: IntoIterator<Item = T>,
    W: From<T> + Monoid,
{
    let mut iter = iter.into_iter();
    iter.next()
        .map(|first| iter.fold(W::from(first), |acc, x| acc.combine(&W::from(x))))
        .unwrap_or_else(W::empty)
}
