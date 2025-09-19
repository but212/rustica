//! # Deprecated Composable Function Operations
//!
//! **DEPRECATED**: This module is deprecated. Use `FunctionCategory` from
//! `rustica::category::function_category` instead for category-theoretically sound function composition.
//!
//! This module previously provided traits and utilities for function composition, but has been
//! replaced by the more mathematically rigorous `FunctionCategory` implementation.
//!
//! # TODO: Improvement Opportunities
//!
//! - **API Consistency**: Add ownership-based and reference-based versions of all composition methods
//!   similar to the improvements in the Functor trait.
//!   - Added `compose_owned` and `compose_when_owned` methods
//!
//! - **Performance Optimization**:
//!   - Added `#[inline]` attributes to all methods
//!   - Add specialized implementations for common use cases
//!   - Consider using associated type patterns to avoid boxing futures where possible
//!
//! - **Extended Functionality**:
//!   - Added `compose_fallible` for Result/Option composition
//!   - Added `compose_iter` for iterator-based composition
//!   - Implemented `compose_par` for parallel composition using rayon
//!
//! - **Type Safety Improvements**:
//!   - Add specialized composer traits (MonadicComposable, CollectionComposable, AsyncComposable)
//!     - Note: Initial implementation was removed; plan to re-implement in future releases with improved design
//!   - Consider adding HKT-based extensions for container types
//!   - Provide better type inference for complex compositions
//!
//! - **Documentation and Examples**:
//!   - Enhanced examples for all composition functions
//!   - Include performance benchmarks for different composition strategies
//!   - Enhance doctest coverage for all edge cases
//!
//! # Mathematical Definition
//!
//! Function composition is defined as (g ∘ f)(x) = g(f(x)), where:
//! - f: X → Y is a function from set X to set Y
//! - g: Y → Z is a function from set Y to set Z
//! - (g ∘ f): X → Z is their composition
//!
//! # Laws
//!
//! 1. Identity:
//!    ```text
//!    f ∘ id = f
//!    id ∘ f = f
//!    ```
//!
//! 2. Associativity:
//!    ```text
//!    (h ∘ g) ∘ f = h ∘ (g ∘ f)
//!    ```
//!
//! 3. Type Safety:
//!    - If f: A → B and g: B → C, then (g ∘ f): A → C
//!    - Types must align at composition boundaries
//!
//! # Migration Guide
//!
//! **All functions in this module are deprecated**. Use `FunctionCategory` instead:
//!
//! - **Basic Composition**: Use `FunctionCategory::compose_morphisms`
//! - **Multiple Composition**: Use `FunctionCategory::compose_all` or `FunctionCategory::sequence`
//! - **Conditional Composition**: Use `FunctionCategory::compose_when`
//! - **Function Lifting**: Use `FunctionCategory::lift` or `FunctionCategory::arrow`
//!
//! For specialized composition (async, fallible, parallel), combine `FunctionCategory`
//! with appropriate libraries (tokio, rayon, etc.) rather than using the deprecated utilities.
//!
//! # Migration Example
//!
//! **Old (Deprecated)**:
//! ```rust,ignore
//! use rustica::traits::composable::Composable;
//!
//! struct SimpleCompose<T>(T);
//! impl<T> HKT for SimpleCompose<T> {
//!     type Source = T;
//!     type Output<U> = SimpleCompose<U>;
//! }
//! impl<T> Composable for SimpleCompose<T> {}
//!
//! let add_one = |x: i32| x + 1;
//! let multiply_two = |x: i32| x * 2;
//! let composed = SimpleCompose::<i32>::compose(&add_one, &multiply_two);
//! ```
//!
//! **New (Recommended)**:
//! ```rust
//! use rustica::category::function_category::{FunctionCategory, function};
//! use rustica::traits::category::Category;
//!
//! // Using the function! macro for clean syntax
//! function!(add_one: i32 => i32 = |x: i32| x + 1);
//! function!(multiply_two: i32 => i32 = |x: i32| x * 2);
//! let composed = FunctionCategory::compose_morphisms(&add_one, &multiply_two);
//! assert_eq!(composed(3), 8);  // (3 + 1) * 2 = 8
//!
//! // Or using the compose! macro
//! use rustica::category::function_category::compose;
//! let pipeline = compose!(
//!     |x: i32| x + 1,
//!     |x: i32| x * 2
//! );
//! assert_eq!(pipeline(3), 8);
//! ```
//!
//! # Common Use Cases
//!
//! 1. **Data Transformation Pipelines**
//!    - Building complex data transformations from simple steps
//!    - Creating reusable transformation components
//!
//! 2. **Error Handling**
//!    - Composing functions that may fail
//!    - Building robust error propagation chains
//!
//! 3. **Stream Processing**
//!    - Creating data processing pipelines
//!    - Composing stream transformations
//!
//! 4. **Event Handling**
//!    - Building event processing chains
//!    - Composing event handlers

use crate::traits::hkt::HKT;
use std::future::Future;
use std::pin::Pin;

/// A trait for composable functions that can be chained together in a type-safe manner.
///
/// **DEPRECATED**: This trait violates category theory principles. Use `FunctionCategory` instead.
///
/// # Migration Guide
///
/// Replace:
/// ```rust,ignore
/// use rustica::traits::composable::Composable;
/// SimpleCompose::<i32>::compose(&f, &g)
/// ```
///
/// With:
/// ```rust,ignore
/// use rustica::category::function_category::FunctionCategory;
/// use rustica::traits::arrow::Arrow;
/// let f_morph = FunctionCategory::arrow(f);
/// let g_morph = FunctionCategory::arrow(g);
/// FunctionCategory::compose_morphisms(&g_morph, &f_morph)
/// ```
#[deprecated(
    note = "Use FunctionCategory from rustica::category::function_category instead. This trait violates category theory principles."
)]
pub trait Composable: HKT {
    /// Composes two functions into a single function.
    ///
    /// This is the reference-based version that doesn't take ownership of the functions.
    ///
    /// # Type Parameters
    ///
    /// * `T`: Intermediate type between `f` and `g`
    /// * `U`: Output type of the composed function
    /// * `F`: Type of the first function
    /// * `G`: Type of the second function
    ///
    /// # Arguments
    ///
    /// * `f`: First function to compose
    /// * `g`: Second function to compose
    ///
    /// # Returns
    ///
    /// A new function that applies `f` and then `g`
    #[inline]
    fn compose<T, U, F, G>(f: F, g: G) -> impl Fn(Self::Source) -> U
    where
        F: Fn(Self::Source) -> T,
        G: Fn(T) -> U,
    {
        move |x| g(f(x))
    }

    /// Composes two functions conditionally based on a predicate.
    ///
    /// This is the reference-based version that doesn't take ownership of the functions.
    ///
    /// # Type Parameters
    ///
    /// * `U`: Output type of both functions
    /// * `F`: Type of the first function
    /// * `G`: Type of the second function
    /// * `P`: Type of the predicate function
    ///
    /// # Arguments
    ///
    /// * `f`: Initial transformation function
    /// * `g`: Conditional transformation function
    /// * `predicate`: Function that decides whether to apply `g`
    ///
    /// # Returns
    ///
    /// A new function that applies `f`, then conditionally applies `g` based on the predicate.
    fn compose_when<U, F, G, P>(f: F, g: G, predicate: P) -> impl Fn(Self::Source) -> U
    where
        F: Fn(Self::Source) -> U,
        G: Fn(U) -> U,
        P: Fn(&U) -> bool,
    {
        move |x| {
            let result = f(x);
            if predicate(&result) {
                g(result)
            } else {
                result
            }
        }
    }
}

/// **DEPRECATED**: Use `FunctionCategory::compose_morphisms` instead.
///
/// Composes two functions and returns a new function.
///
/// # Migration Guide
///
/// Replace:
/// ```rust,ignore
/// use rustica::traits::composable::compose;
/// let composed = compose(f, g);
/// ```
///
/// With:
/// ```rust,ignore
/// use rustica::category::function_category::FunctionCategory;
/// use rustica::traits::category::Category;
/// use rustica::traits::arrow::Arrow;
///
/// let f_morph = FunctionCategory::arrow(f);
/// let g_morph = FunctionCategory::arrow(g);
/// let composed = FunctionCategory::compose_morphisms(&f_morph, &g_morph);
/// ```
#[deprecated(
    note = "Use FunctionCategory::compose_morphisms instead for category-theoretic composition"
)]
#[inline]
pub fn compose<T, U, V, F, G>(f: F, g: G) -> impl Fn(T) -> V
where
    F: Fn(T) -> U,
    G: Fn(U) -> V,
{
    move |x| g(f(x))
}

/// **DEPRECATED**: Use `FunctionCategory::compose_all` or `FunctionCategory::sequence` instead.
///
/// # Migration Guide
///
/// Replace:
/// ```rust,ignore
/// use rustica::traits::composable::compose_all;
/// let composed = compose_all(vec![f1, f2, f3]);
/// ```
///
/// With:
/// ```rust,ignore
/// use rustica::category::function_category::FunctionCategory;
/// let composed = FunctionCategory::sequence(vec![f1, f2, f3]);
/// ```
#[deprecated(
    note = "Use FunctionCategory::sequence for owned functions or FunctionCategory::compose_all for morphism references"
)]
#[inline]
pub fn compose_all<T, F>(functions: Vec<F>) -> impl Fn(T) -> T
where
    F: Fn(T) -> T,
{
    move |initial| functions.iter().fold(initial, |acc, f| f(acc))
}

/// Composes two asynchronous functions to create a new asynchronous function.
///
/// This function applies two asynchronous functions in sequence, first
/// applying `f` to the input and then applying `g` to the result.
///
/// # Type Parameters
///
/// * `A`: Input type of the first function
/// * `B`: Output type of the first function and input type of the second function
/// * `C`: Output type of the second function
/// * `F`: Function type that takes `A` and returns `Future<Output = B>`
/// * `G`: Function type that takes `B` and returns `Future<Output = C>`
/// * `FutB`: Future type returned by `F`
/// * `FutC`: Future type returned by `G`
///
/// # Arguments
///
/// * `f`: First asynchronous function
/// * `g`: Second asynchronous function
/// * `input`: Initial input value
///
/// # Returns
///
/// The result `C` after sequentially applying `f` and `g`
///
/// # Examples
///
/// ```rust,no_run
/// use rustica::traits::composable::compose_async;
///
/// # async fn example() {
/// async fn add_one(x: i32) -> i32 { x + 1 }
/// async fn double(x: i32) -> i32 { x * 2 }
///
/// let result = compose_async(add_one, double, 3).await;
/// assert_eq!(result, 8);  // (3 + 1) * 2 = 8
/// # }
/// ```
#[inline]
pub async fn compose_async<A, B, C, F, G, FutB, FutC>(f: F, g: G, input: A) -> C
where
    F: Fn(A) -> FutB,
    G: Fn(B) -> FutC,
    FutB: Future<Output = B>,
    FutC: Future<Output = C>,
{
    let intermediate = f(input).await;
    g(intermediate).await
}

/// Composes two asynchronous functions into a single asynchronous function.
///
/// This function takes two asynchronous functions `f` and `g` and returns a new function
/// that applies `f` first and then `g` to the result.
///
/// # Type Parameters
///
/// * `A`: Input type of the first function
/// * `B`: Output type of the first function and input type of the second function
/// * `C`: Output type of the second function
/// * `F`: First asynchronous function type
/// * `G`: Second asynchronous function type
/// * `FutB`: Future type returned by `F`
/// * `FutC`: Future type returned by `G`
///
/// # Arguments
///
/// * `f`: First asynchronous function
/// * `g`: Second asynchronous function
///
/// # Returns
///
/// A new function that composes `f` and `g` asynchronously
///
/// # Example
///
/// ```rust,no_run
/// use std::future::Future;
/// use rustica::traits::composable::compose_async_fn;
///
/// // Define async functions with explicit type annotations
/// async fn add_one(x: i32) -> i32 { x + 1 }
/// async fn double(x: i32) -> i32 { x * 2 }
///
/// # async fn example() {
/// // Compose the async functions
/// let composed = compose_async_fn(add_one, double);
///
/// // Use the composed function
/// let result = composed(3).await;
/// assert_eq!(result, 8);  // (3 + 1) * 2 = 8
/// # }
/// ```
#[inline]
pub fn compose_async_fn<A, B, C, F, G, FutB, FutC>(
    f: F, g: G,
) -> impl Fn(A) -> Pin<Box<dyn Future<Output = C> + 'static>>
where
    F: Fn(A) -> FutB + Clone + 'static,
    G: Fn(B) -> FutC + Clone + 'static,
    FutB: Future<Output = B> + 'static,
    FutC: Future<Output = C> + 'static,
    A: 'static,
    B: 'static,
    C: 'static,
{
    move |a| {
        let f = f.clone();
        let g = g.clone();
        Box::pin(async move {
            let b = f(a).await;
            g(b).await
        })
    }
}

/// **DEPRECATED**: Use `FunctionCategory::compose_when` instead.
///
/// # Migration Guide
///
/// Replace:
/// ```rust,ignore
/// use rustica::traits::composable::compose_when;
/// let conditional = compose_when(f, g, predicate);
/// ```
///
/// With:
/// ```rust,ignore
/// use rustica::category::function_category::FunctionCategory;
/// use rustica::traits::arrow::Arrow;
/// let f_morph = FunctionCategory::arrow(f);
/// let g_morph = FunctionCategory::arrow(g);
/// let conditional = FunctionCategory::compose_when(&f_morph, &g_morph, predicate);
/// ```
#[deprecated(
    note = "Use FunctionCategory::compose_when for category-theoretic conditional composition"
)]
pub fn compose_when<A, B, F, G, P>(f: F, g: G, predicate: P) -> impl Fn(A) -> B
where
    F: Fn(A) -> B,
    G: Fn(B) -> B,
    P: Fn(&B) -> bool,
{
    move |x| {
        let result = f(x);
        if predicate(&result) {
            g(result)
        } else {
            result
        }
    }
}

/// **DEPRECATED**: Use monadic composition with `FunctionCategory` instead.
///
/// This function composes two functions where both can return errors. If the first function
/// returns an error, that error is propagated. Otherwise, the second function is applied
/// to the success value of the first function.
///
/// # Type Parameters
///
/// * `A`: Input type of the first function
/// * `B`: Intermediate type (output of first function, input to second function)
/// * `C`: Output type of the second function
/// * `E`: Error type for both functions
/// * `F`: Type of the first function
/// * `G`: Type of the second function
///
/// # Arguments
///
/// * `f`: First fallible function
/// * `g`: Second fallible function
///
/// # Returns
///
/// A new function that returns a Result, propagating errors or applying both functions
///
/// # Examples
///
/// ```rust
/// use rustica::traits::composable::compose_fallible;
/// use std::num::ParseIntError;
///
/// // Define two fallible functions
/// fn parse_string(s: &str) -> Result<i32, ParseIntError> {
///     s.parse::<i32>()
/// }
///
/// fn double_if_positive(n: i32) -> Result<i32, &'static str> {
///     if n > 0 {
///         Ok(n * 2)
///     } else {
///         Err("Number was not positive")
///     }
/// }
///
/// // Compose them with error type conversion
/// let composed = compose_fallible(
///     |s| parse_string(s).map_err(|_| "Parse error"),
///     double_if_positive
/// );
///
/// assert_eq!(composed("5"), Ok(10));
/// assert_eq!(composed("-5"), Err("Number was not positive"));
/// assert_eq!(composed("not_a_number"), Err("Parse error"));
/// ```
#[inline]
pub fn compose_fallible<A, B, C, E, F, G>(f: F, g: G) -> impl Fn(A) -> Result<C, E>
where
    F: Fn(A) -> Result<B, E>,
    G: Fn(B) -> Result<C, E>,
{
    // Using basic compose function with Result's and_then
    compose(f, move |result: Result<B, E>| result.and_then(&g))
}

/// **DEPRECATED**: Use monadic composition with `FunctionCategory` instead.
///
/// If the first function returns None, that None is propagated. If it returns Some,
/// the second function is applied, and its Result is converted to Option (Ok -> Some, Err -> None).
///
/// # Type Parameters
///
/// * `A`: Input type of the first function
/// * `B`: Intermediate type (output of first function, input to second function)
/// * `C`: Output type of the second function
/// * `E`: Error type of the second function's Result
/// * `F`: Type of the first function
/// * `G`: Type of the second function
///
/// # Arguments
///
/// * `f`: First function returning Option
/// * `g`: Second function returning Result
///
/// # Returns
///
/// A new function that returns an Option, propagating None or converting Result to Option
///
/// # Examples
///
/// ```rust
/// use rustica::traits::composable::compose_option_result;
///
/// // Define a function that returns an Option
/// fn parse_as_int(s: &str) -> Option<i32> {
///     s.parse::<i32>().ok()
/// }
///
/// // Define a function that returns a Result
/// fn divide_100_by(n: i32) -> Result<f64, String> {
///     if n == 0 {
///         Err("Division by zero".to_string())
///     } else {
///         Ok(100.0 / n as f64)
///     }
/// }
///
/// // Compose them
/// let composed = compose_option_result(parse_as_int, divide_100_by);
///
/// assert!(composed("5").is_some());
/// assert_eq!(composed("5").unwrap(), 20.0);
/// assert_eq!(composed("0"), None);           // Result::Err becomes None
/// assert_eq!(composed("not_a_number"), None); // Option::None stays None
/// ```
#[inline]
pub fn compose_option_result<A, B, C, E, F, G>(f: F, g: G) -> impl Fn(A) -> Option<C>
where
    F: Fn(A) -> Option<B>,
    G: Fn(B) -> Result<C, E>,
{
    // Using basic compose function
    compose(f, move |opt: Option<B>| opt.and_then(|b| g(b).ok()))
}

/// **DEPRECATED**: Use monadic composition with `FunctionCategory` instead.
///
/// This function is similar to using `and_then` on an Option. If the first function
/// returns None, that None is propagated. Otherwise, the second function is applied
/// to the value inside the Some.
///
/// # Type Parameters
///
/// * `A`: Input type of the first function
/// * `B`: Intermediate type (output of first function, input to second function)
/// * `C`: Output type of the second function
/// * `F`: Type of the first function
/// * `G`: Type of the second function
///
/// # Arguments
///
/// * `f`: First function returning Option
/// * `g`: Second function returning Option
///
/// # Returns
///
/// A new function that returns an Option, propagating None or applying both functions
///
/// # Examples
///
/// ```rust
/// use rustica::traits::composable::compose_option;
///
/// // Define two functions that return Options
/// fn parse_as_int(s: &str) -> Option<i32> {
///     s.parse::<i32>().ok()
/// }
///
/// fn double_if_positive(n: i32) -> Option<i32> {
///     if n > 0 {
///         Some(n * 2)
///     } else {
///         None
///     }
/// }
///
/// // Compose them
/// let composed = compose_option(parse_as_int, double_if_positive);
///
/// assert_eq!(composed("5"), Some(10));
/// assert_eq!(composed("-5"), None);         // Not positive
/// assert_eq!(composed("not_a_number"), None); // Parse error
/// ```
#[inline]
pub fn compose_option<A, B, C, F, G>(f: F, g: G) -> impl Fn(A) -> Option<C>
where
    F: Fn(A) -> Option<B>,
    G: Fn(B) -> Option<C>,
{
    // Using basic compose function with Option's and_then
    compose(f, move |opt: Option<B>| opt.and_then(&g))
}

/// **DEPRECATED**: Use `FunctionCategory` with iterator methods instead.
///
/// # Type Parameters
///
/// * `A`: Input type of the first function
/// * `B`: Output type of the first function and output of the composed function
/// * `F`: Type of the first function
/// * `P`: Type of the predicate function
///
/// # Arguments
///
/// * `f`: Function producing a collection
/// * `predicate`: Predicate to filter elements
///
/// # Returns
///
/// A function that applies the first function and then filters the results
///
/// # Examples
///
/// ```rust
/// use rustica::traits::composable::compose_filter;
///
/// fn get_numbers(max: usize) -> Vec<i32> {
///     (0..max as i32).collect()
/// }
///
/// fn is_even(x: &i32) -> bool {
///     x % 2 == 0
/// }
///
/// // Compose these functions
/// let get_even_numbers = compose_filter(get_numbers, is_even);
///
/// // Apply the composed function
/// let evens = get_even_numbers(5);
/// assert_eq!(evens, vec![0, 2, 4]);
/// ```
#[inline]
pub fn compose_filter<A, B, F, P>(f: F, predicate: P) -> impl Fn(A) -> Vec<B>
where
    F: Fn(A) -> Vec<B>,
    P: Fn(&B) -> bool + Clone,
{
    // Using compose to build the filter operation
    compose(f, move |collection: Vec<B>| {
        let predicate = predicate.clone();
        collection
            .into_iter()
            .filter(move |item| predicate(item))
            .collect()
    })
}

/// **DEPRECATED**: Use `FunctionCategory` with iterator methods instead.
///
/// # Type Parameters
///
/// * `A`: Input type to all functions
/// * `B`: Output item type of all functions
/// * `F`: Type of the functions
///
/// # Arguments
///
/// * `functions`: Vector of functions that each produce a collection
///
/// # Returns
///
/// A function that chains all the iterators produced by the given functions
///
/// # Examples
///
/// ```rust
/// use rustica::traits::composable::compose_iter_chain;
///
/// // Define iterator-producing functions for different ranges
/// fn range_1_to_3(_: ()) -> Vec<i32> { vec![1, 2, 3] }
/// fn range_4_to_6(_: ()) -> Vec<i32> { vec![4, 5, 6] }
/// fn range_7_to_9(_: ()) -> Vec<i32> { vec![7, 8, 9] }
///
/// // Chain them together
/// let combined = compose_iter_chain(vec![range_1_to_3, range_4_to_6, range_7_to_9]);
///
/// // Use the combined function
/// let all_numbers: Vec<_> = combined(());
///
/// // Contains all numbers from all three iterators, in order of the iterators
/// // First all numbers from range1 (1..100), then all numbers from range2 (100..200), then all numbers from range3 (200..300)
/// assert_eq!(all_numbers.len(), 9);
/// ```
pub fn compose_iter_chain<A, B, F>(functions: Vec<F>) -> impl Fn(A) -> Vec<B>
where
    F: Fn(A) -> Vec<B> + Clone,
    A: Clone,
{
    // Building upon the concept of compose_all, but for iterator-producing functions
    move |a| {
        // Using flat_map to chain the results of each function
        functions
            .iter()
            .flat_map(|f| {
                let f = f.clone();
                let a = a.clone();
                f(a)
            })
            .collect()
    }
}

/// **DEPRECATED**: Use `FunctionCategory` with rayon directly instead.
///
/// This function requires the "rayon" feature to be enabled.
///
/// # Type Parameters
///
/// * `A`: Input type of the first function
/// * `B`: Output type of the first function and output of the composed function
/// * `F`: Type of the first function
/// * `P`: Type of the predicate function
///
/// # Arguments
///
/// * `f`: Function producing a collection
/// * `predicate`: Predicate to filter elements in parallel
///
/// # Returns
///
/// A function that composes the two functions with parallel execution of the filtering
///
/// # Examples
///
/// ```rust
/// use rustica::traits::composable::compose_par_filter;
///
/// // A function that produces a vector of numbers
/// fn generate_numbers(count: usize) -> Vec<u64> {
///     (1..=count as u64).collect()
/// }
///
/// // A computationally intensive primality test
/// fn is_prime(n: &u64) -> bool {
///     if *n <= 1 {
///         return false;
///     }
///     if *n <= 3 {
///         return true;
///     }
///     if *n % 2 == 0 || *n % 3 == 0 {
///         return false;
///     }
///     
///     let limit = (*n as f64).sqrt() as u64 + 1;
///     for i in (5..=limit).step_by(6) {
///         if *n % i == 0 || *n % (i + 2) == 0 {
///             return false;
///         }
///     }
///     true
/// }
///
/// // Use the composed function (will run in parallel)
/// let get_primes = compose_par_filter(generate_numbers, is_prime);
/// let primes = get_primes(100);
/// ```
pub fn compose_par_filter<A, B, F, P>(f: F, predicate: P) -> impl Fn(A) -> Vec<B>
where
    F: Fn(A) -> Vec<B>,
    P: Fn(&B) -> bool + Clone + Send + Sync,
    B: Send,
{
    // Using compose to build the parallel filter operation
    compose(f, move |collection: Vec<B>| {
        let predicate = predicate.clone();
        collection
            .into_par_iter()
            .filter(move |item| predicate(item))
            .collect()
    })
}

// Note: Rayon-based parallel composition functions are deprecated.
// For parallel processing, use rayon directly with FunctionCategory morphisms.
use rayon::prelude::*;

/// **DEPRECATED**: Use `FunctionCategory` with rayon directly instead.
///
/// This function requires the "rayon" feature to be enabled.
///
/// # Type Parameters
///
/// * `A`: Input type of the first function
/// * `B`: Output type of the first function, input of the mapping function
/// * `C`: Output type of the mapping function
/// * `F`: Type of the first function
/// * `G`: Type of the mapping function
///
/// # Arguments
///
/// * `f`: Function producing a collection
/// * `g`: Function to apply to each element in parallel
///
/// # Returns
///
/// A function that composes the two functions with parallel execution of the mapping
///
/// # Examples
///
/// ```rust
/// use rustica::traits::composable::compose_par;
///
/// // A function that produces a vector of large numbers
/// fn generate_large_numbers(count: usize) -> Vec<u64> {
///     (1..=count as u64).collect()
/// }
///
/// // A computationally intensive function to calculate factorial
/// fn factorial(n: u64) -> u64 {
///     (1..=n).product()
/// }
///
/// // Use the composed function (will run in parallel)
/// let get_factorials = compose_par(generate_large_numbers, factorial);
/// let factorials = get_factorials(10);
/// ```
#[inline]
pub fn compose_par<A, B, C, F, G>(f: F, g: G) -> impl Fn(A) -> Vec<C>
where
    F: Fn(A) -> Vec<B>,
    G: Fn(B) -> C + Clone + Send + Sync,
    B: Send,
    C: Send,
{
    // Using compose to build the parallel mapping operation
    compose(f, move |collection: Vec<B>| {
        let g = g.clone();
        collection.into_par_iter().map(g).collect()
    })
}

/// **DEPRECATED**: Use `FunctionCategory` with rayon directly instead.
///
/// This function requires the "rayon" feature to be enabled.
///
/// # Type Parameters
///
/// * `A`: Input type to all functions
/// * `B`: Output item type of all functions
/// * `F`: Type of the functions
///
/// # Arguments
///
/// * `functions`: Vector of functions that each produce a collection
///
/// # Returns
///
/// A function that chains all the collections produced by the given functions
///
/// # Examples
///
/// ```rust
/// use rustica::traits::composable::compose_par_chain;
///
/// // Define collection-producing functions for different ranges
/// fn range1(_: ()) -> Vec<i32> { (1..100).collect() }
/// fn range2(_: ()) -> Vec<i32> { (100..200).collect() }
/// fn range3(_: ()) -> Vec<i32> { (200..300).collect() }
///
/// // Chain them together
/// let combined = compose_par_chain(vec![range1, range2, range3]);
///
/// // Use the composed function (elements will be processed in parallel)
/// let all_numbers: Vec<_> = combined(());
///
/// // Contains all numbers from all three iterators, in order of the iterators
/// // First all numbers from range1 (1..100), then all numbers from range2 (100..200), then all numbers from range3 (200..300)
/// assert_eq!(all_numbers.len(), 299);
/// ```
pub fn compose_par_chain<A, B, F>(functions: Vec<F>) -> impl Fn(A) -> Vec<B>
where
    F: Fn(A) -> Vec<B> + Clone + Send + Sync,
    A: Clone + Send + Sync,
    B: Send,
{
    // Building upon the concept of compose_all, but for iterator-producing functions
    move |a| {
        // Using flat_map to chain the results of each function
        functions
            .par_iter()
            .flat_map(|f| {
                let f = f.clone();
                let a = a.clone();
                f(a)
            })
            .collect()
    }
}

/// **DEPRECATED**: Use `FunctionCategory` with rayon directly instead.
///
/// This function requires the "rayon" feature to be enabled.
///
/// # Type Parameters
///
/// * `A`: Input type to all functions
/// * `B`: Output type of all functions
/// * `F`: Type of the transformation functions
///
/// # Arguments
///
/// * `input`: The input value to transform
/// * `transformations`: Vector of functions to apply to the input
///
/// # Returns
///
/// A vector containing the results of all transformations
///
/// # Examples
///
/// ```rust
/// use rustica::traits::composable::apply_par_all;
///
/// // Define a set of transformation functions
/// fn add_ten(x: i32) -> i32 { x + 10 }
/// fn multiply_two(x: i32) -> i32 { x * 2 }
/// fn square(x: i32) -> i32 { x * x }
/// fn negate(x: i32) -> i32 { -x }
///
/// // Apply all transformations in parallel
/// let results = apply_par_all(10, vec![add_ten, multiply_two, square, negate]);
///
/// // Should contain results of all transformations: [20, 20, 100, -10]
/// assert_eq!(results.len(), 4);
/// ```
pub fn apply_par_all<A, B, F>(input: A, transformations: Vec<F>) -> Vec<B>
where
    F: Fn(A) -> B + Clone + Send + Sync,
    A: Clone + Send + Sync,
    B: Send,
{
    transformations
        .par_iter()
        .map(|f| {
            let f = f.clone();
            let input = input.clone();
            f(input)
        })
        .collect()
}
