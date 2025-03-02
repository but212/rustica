use crate::traits::hkt::HKT;

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
/// impl<T> Composable for SimpleCompose<T> {
///     fn compose<U, V, F, G>(f: F, g: G) -> impl Fn(Self::Source) -> V
///     where
///         F: Fn(Self::Source) -> U,
///         G: Fn(U) -> V,
///     {
///         move |x| g(f(x))
///     }
/// }
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
    /// * `T`: Input type of the first function
    /// * `U`: Output type of the first function and input type of the second function
    /// * `V`: Output type of the second function
    ///
    /// # Arguments
    ///
    /// * `f`: First function to compose
    /// * `g`: Second function to compose
    ///
    /// # Returns
    ///
    /// A new function that represents the composition of `f` and `g`
    fn compose<T, U, F, G>(f: F, g: G) -> impl Fn(Self::Source) -> U
    where
        F: Fn(Self::Source) -> T,
        G: Fn(T) -> U;
}
