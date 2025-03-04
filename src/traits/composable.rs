use crate::traits::hkt::HKT;
use std::future::Future;
use std::pin::Pin;

/// A trait for composable functions that can be chained together in a type-safe manner.
/// This trait provides a foundation for function composition, enabling the creation of complex
/// transformations from simpler ones.
///
/// # Mathematical Definition
///
/// Function composition is defined as (g ∘ f)(x) = g(f(x)), where:
/// - f: X → Y is a function from set X to set Y
/// - g: Y → Z is a function from set Y to set Z
/// - (g ∘ f): X → Z is their composition
///
/// # Laws
///
/// 1. Identity:
///    ```text
///    f ∘ id = f
///    id ∘ f = f
///    ```
///
/// 2. Associativity:
///    ```text
///    (h ∘ g) ∘ f = h ∘ (g ∘ f)
///    ```
///
/// 3. Type Safety:
///    - If f: A → B and g: B → C, then (g ∘ f): A → C
///    - Types must align at composition boundaries
///
/// # Examples
///
/// ```rust
/// use rustica::prelude::*;
/// use rustica::traits::composable::Composable;
///
/// // A simple implementation of function composition
/// struct SimpleCompose<T>(T);
/// 
/// impl<T> HKT for SimpleCompose<T> {
///     type Source = T;
///     type Output<U> = SimpleCompose<U>;
///     type Source2 = T;
///     type BinaryOutput<U, V> = ();
/// }
///
/// impl<T> Composable for SimpleCompose<T> {}
///
/// // Basic numeric transformation
/// let add_one = |x: i32| x + 1;
/// let multiply_two = |x: i32| x * 2;
/// let composed = SimpleCompose::<i32>::compose(&add_one, &multiply_two);
/// assert_eq!(composed(3), 8);  // (3 + 1) * 2 = 8
///
/// // String processing
/// let to_string = |x: i32| x.to_string();
/// let add_exclamation = |s: String| s + "!";
/// let excited = SimpleCompose::<i32>::compose(&to_string, &add_exclamation);
/// assert_eq!(excited(42), "42!");
///
/// // Option handling
/// let safe_divide = |x: f64| if x == 0.0 { None } else { Some(1.0 / x) };
/// let safe_sqrt = |x: f64| if x >= 0.0 { Some(x.sqrt()) } else { None };
/// let option_and_then_safe_sqrt = |x: Option<f64>| x.and_then(safe_sqrt);
/// let composed = SimpleCompose::<f64>::compose(&safe_divide, &option_and_then_safe_sqrt);
/// assert_eq!(composed(4.0), Some(0.5));  // sqrt(1/4) = 0.5
/// assert_eq!(composed(0.0), None);       // Division by zero
/// ```
///
/// # Common Use Cases
///
/// 1. **Data Transformation Pipelines**
///    - Building complex data transformations from simple steps
///    - Creating reusable transformation components
///
/// 2. **Error Handling**
///    - Composing functions that may fail
///    - Building robust error propagation chains
///
/// 3. **Stream Processing**
///    - Creating data processing pipelines
///    - Composing stream transformations
///
/// 4. **Event Handling**
///    - Building event processing chains
///    - Composing event handlers
///
/// # Type Parameters
///
/// * `T`: Input type of the first function
/// * `U`: Output type of the first function and input type of the second function
/// * `V`: Output type of the second function
pub trait Composable: HKT {
    /// Composes two functions into a single function.
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
    fn compose<T, U, F, G>(f: F, g: G) -> impl Fn(Self::Source) -> U
    where
        F: Fn(Self::Source) -> T,
        G: Fn(T) -> U
    {
        move |x| g(f(x))
    }

    /// Composes two functions conditionally based on a predicate.
    ///
    /// # Type Parameters
    ///
    /// * `U`: Output type of both functions
    /// * `V`: Unused (consider removing)
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
    fn compose_when<U, V, F, G, P>(f: F, g: G, predicate: P) -> impl Fn(Self::Source) -> U
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

/// Composes two functions and returns a new function.
///
/// # Type Parameters
///
/// * `T`: Input type of the first function
/// * `U`: Output type of the first function and input type of the second function
/// * `V`: Output type of the second function
/// * `F`: Function of type `Fn(T) -> U`
/// * `G`: Function of type `Fn(U) -> V`
///
/// # Arguments
///
/// * `f`: First function to compose
/// * `g`: Second function to compose
///
/// # Returns
///
/// Returns a new function that is the composition of `f` and `g`.
pub fn compose<T, U, V, F, G>(f: F, g: G) -> impl Fn(T) -> V
where
    F: Fn(T) -> U,
    G: Fn(U) -> V,
{
    move |x| g(f(x))
}

/// Composes multiple functions into a single function.
///
/// This function takes a vector of functions and returns a new function that applies
/// all the given functions in sequence, from left to right.
///
/// # Type Parameters
///
/// * `T`: The type of both input and output for all functions
/// * `F`: The type of the functions to be composed
///
/// # Arguments
///
/// * `functions`: A vector of functions to compose
///
/// # Returns
///
/// A new function that represents the composition of all input functions
///
/// # Examples
///
/// ```
/// use rustica::traits::composable::compose_all;
/// 
/// let add_one = |x| x + 1;
/// let double = |x| x * 2;
/// let composed = compose_all(vec![add_one, double, add_one]);
/// assert_eq!(composed(3), 9);  // ((3 + 1) * 2) + 1 = 9
/// ```
pub fn compose_all<T, F>(functions: Vec<F>) -> impl Fn(T) -> T
where
    F: Fn(T) -> T,
{
    move |initial| {
        functions.iter().fold(initial, |acc, f| f(acc))
    }
}


/// Composes two asynchronous functions to create a new asynchronous function.
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
pub async fn compose_async<A, B, C, F, G, FutB, FutC>(f: F, g: G, input: A) -> C
where
    F: Fn(A) -> FutB,
    G: Fn(B) -> FutC,
    FutB: Future<Output = B>,
    FutC: Future<Output = C>,
{
    let b = f(input).await;
    g(b).await
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
/// ```
/// use std::future::Future;
/// use rustica::traits::composable::compose_async_fn;
///
/// async fn add_one(x: i32) -> i32 { x + 1 }
/// async fn double(x: i32) -> i32 { x * 2 }
///
/// #[tokio::main]
/// async fn main() {
///     let composed = compose_async_fn(add_one, double);
///     let result = composed(3).await;
///     assert_eq!(result, 8);  // (3 + 1) * 2 = 8
/// }
/// ```
pub fn compose_async_fn<A, B, C, F, G, FutB, FutC>(
    f: F,
    g: G,
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


/// Composes two functions conditionally based on a predicate.
///
/// This function takes three functions:
/// - `f`: The initial transformation function
/// - `g`: The secondary transformation function
/// - `predicate`: A function that decides whether to apply `g`
///
/// # Type Parameters
///
/// * `A`: Input type of the first function
/// * `B`: Output type of both functions
/// * `F`: Type of the first function
/// * `G`: Type of the second function
/// * `P`: Type of the predicate function
///
/// # Arguments
///
/// * `f`: Initial transformation function
/// * `g`: Secondary transformation function
/// * `predicate`: Function that decides whether to apply `g`
///
/// # Returns
///
/// A new function that applies `f`, then conditionally applies `g` based on the predicate.
///
/// # Example
///
/// ```
/// use rustica::traits::composable::compose_when;
///
/// let add_one = |x: i32| x + 1;
/// let double = |x: i32| x * 2;
/// let is_even = |&x: &i32| x % 2 == 0;
///
/// let conditional = compose_when(add_one, double, is_even);
/// assert_eq!(conditional(1), 4);  // (1 + 1) * 2 = 4
/// assert_eq!(conditional(2), 3);  // (2 + 1) = 3 (not doubled)
/// ```
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