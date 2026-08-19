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
//! ## Quick Start
//!
//! ```rust
//! use rustica::utils::categorical_utils::*;
//!
//! // Functor-inspired mapping uses the standard `Option::map` API.
//! let maybe_num = Some(42);
//! let maybe_string = maybe_num.map(|x| x.to_string());
//! assert_eq!(maybe_string, Some("42".to_string()));
//!
//! // Monad-inspired chaining uses the standard `Result::and_then` API.
//! let result = Ok(10).and_then(|x| {
//!     if x > 0 { Ok(x * 2) } else { Err("negative") }
//! });
//! assert_eq!(result, Ok(20));
//!
//! // Function composition: compose(g, f) means "g after f"
//! let add_one = |x: i32| x + 1;
//! let double = |x: i32| x * 2;
//! let composed = compose(double, add_one);
//! assert_eq!(composed(5), 12); // double(add_one(5)) = (5 + 1) * 2
//!
//! // Argument flipping: flip(f)(a, b) = f(b, a)
//! let subtract = |x: i32, y: i32| x - y;
//! let flipped_subtract = flip(subtract);
//! assert_eq!(flipped_subtract(3, 10), 7); // subtract(10, 3) = 10 - 3 = 7
//! ```

use crate::traits::monoid::Monoid;

/// Maps a function over both the error and success values of a `Result`.
///
/// This function provides bimap functionality for `Result` types, allowing
/// transformation of both the success and error cases simultaneously.
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

// ===== Function Composition Utilities =====

/// Composes two functions, creating a new function that applies `f` first, then `g`.
///
/// This function implements mathematical function composition: `(g ∘ f)(x) = g(f(x))`.
/// Note that the argument order follows mathematical convention where `compose(g, f)`
/// means "g after f", so `f` is applied first and `g` is applied to its result.
///
/// The composition follows the associativity law and provides a pure functional approach
/// to combining operations.
///
/// # Arguments
///
/// * `g` - The outer function, applied second to the result of `f`
/// * `f` - The inner function, applied first to the input
///
/// # Returns
///
/// A new function that represents the composition `g ∘ f`
///
/// # Examples
///
/// ```rust
/// use rustica::utils::categorical_utils::compose;
///
/// let add_one = |x: i32| x + 1;
/// let double = |x: i32| x * 2;
///
/// // Compose functions: compose(double, add_one) means "double after add_one"
/// // So add_one is applied first, then double
/// let add_one_then_double = compose(double, add_one);
/// assert_eq!(add_one_then_double(5), 12); // double(add_one(5)) = (5 + 1) * 2
///
/// // Function composition is associative
/// let triple = |x: i32| x * 3;
/// let comp1 = compose(triple, compose(double, add_one));
/// let comp2 = compose(compose(triple, double), add_one);
/// assert_eq!(comp1(2), comp2(2));
/// ```
#[inline]
pub fn compose<A, B, C, F, G>(g: G, f: F) -> impl Fn(A) -> C
where
    F: Fn(A) -> B,
    G: Fn(B) -> C,
{
    move |x| g(f(x))
}

/// Pipes the output of one function into another, creating a pipeline.
///
/// This function implements function piping: `pipe(f, g)(x) = g(f(x))`.
/// Unlike `compose`, which reads right-to-left, `pipe` reads left-to-right,
/// making it more intuitive for sequential data transformations.
///
/// # Arguments
///
/// * `f` - The first function to apply
/// * `g` - The second function to apply to the result of the first
///
/// # Returns
///
/// A new function that represents the pipeline of `f` then `g`
///
/// # Examples
///
/// ```rust
/// use rustica::utils::categorical_utils::pipe;
///
/// let add_one = |x: i32| x + 1;
/// let double = |x: i32| x * 2;
///
/// // Pipe functions: first add one, then double
/// let add_one_then_double = pipe(add_one, double);
/// assert_eq!(add_one_then_double(5), 12); // (5 + 1) * 2
///
/// // Chain multiple transformations
/// let to_string = |x: i32| x.to_string();
/// let pipeline = pipe(pipe(add_one, double), to_string);
/// assert_eq!(pipeline(3), "8"); // (3 + 1) * 2 = "8"
/// ```
#[inline]
pub fn pipe<A, B, C, F, G>(f: F, g: G) -> impl Fn(A) -> C
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
/// assert_eq!(subtract(10, 3), 7);       // 10 - 3 = 7
/// assert_eq!(flipped_subtract(10, 3), -7); // flip swaps args: subtract(3, 10) = 3 - 10 = -7
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

/// Folds an iterator using a monoid's combine operation with automatic wrapping.
///
/// This function converts each element to the monoid type `W` and combines them
/// using the monoid's `combine` operation. If the iterator is empty, returns the
/// monoid's identity element (`empty()`).
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
/// use rustica::datatypes::maybe::Maybe;
/// use rustica::datatypes::wrapper::{sum::Sum, product::Product, first::First, last::Last, min::Min, max::Max};
///
/// // Sum operations
/// let numbers = vec![1, 2, 3, 4, 5];
/// let total: Sum<i32> = fold_with(numbers);
/// assert_eq!(total.unwrap(), 15);
///
/// // Product operations
/// let factors = vec![2, 3, 4];
/// let product: Product<i32> = fold_with(factors);
/// assert_eq!(product.unwrap(), 24);
///
/// // First operations
/// let values = vec![10, 20, 30];
/// let first: First<i32> = fold_with(values.clone());
/// assert_eq!(first.unwrap(), 10);
///
/// // Last operations
/// let last: Last<i32> = fold_with(values);
/// assert_eq!(last.unwrap(), 30);
///
/// // Min operations
/// let unsorted = vec![5, 2, 8, 1, 9];
/// let minimum: Min<i32> = fold_with(unsorted);
/// assert_eq!(minimum.unwrap(), 1);
///
/// // Max operations
/// let values = vec![3, 7, 2, 9, 4];
/// let maximum: Max<i32> = fold_with(values);
/// assert_eq!(maximum.unwrap(), 9);
///
/// // Empty iterator returns identity
/// let empty: Vec<i32> = vec![];
/// let zero: Sum<i32> = fold_with(empty);
/// assert_eq!(zero.unwrap(), 0);
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
