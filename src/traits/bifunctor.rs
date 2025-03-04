use crate::traits::hkt::HKT;

/// A bifunctor is a type constructor that takes two type arguments and is a functor in both arguments.
/// This means it provides a way to map functions over both type parameters independently or simultaneously.
///
/// # Laws
///
/// A valid bifunctor instance must satisfy these laws:
///
/// 1. Identity:
///    bimap(id, id) == id
///
/// 2. Composition:
///    bimap(f . g, h . i) == bimap(f, h) . bimap(g, i)
///
/// # Examples
///
/// Here's an example implementation for Result:
/// ```rust
/// use std::fmt::Debug;
/// use rustica::traits::hkt::HKT;
/// use rustica::traits::bifunctor::Bifunctor;
///
/// // A wrapper for Result to implement HKT and Bifunctor
/// #[derive(Debug, Clone, PartialEq)]
/// struct BiResult<T, E>(Result<T, E>);
///
/// // HKT implementation for the first type parameter
/// impl<T, E> HKT for BiResult<T, E> {
///     type Source = T;
///     type Output<U> = BiResult<U, E>;
///     type Source2 = E;
///     type BinaryOutput<U, V> = BiResult<U, V>;
/// }
///
/// impl<T: Clone + Default, E: Clone + Default> Bifunctor for BiResult<T, E> {
///     fn first<C, F>(&self, f: F) -> Self::BinaryOutput<C, E>
///     where
///         F: Fn(&T) -> C,
///     {
///         BiResult(match &self.0 {
///             Ok(a) => Ok(f(a)),
///             Err(e) => Err(e.clone()),
///         })
///     }
/// 
///     fn second<D, G>(&self, g: G) -> Self::BinaryOutput<T, D>
///     where
///         G: Fn(&E) -> D,
///     {
///         BiResult(match &self.0 {
///             Ok(a) => Ok(a.clone()),
///             Err(e) => Err(g(e)),
///         })
///     }
/// 
///     fn bimap<C, D, F, G>(&self, f: F, g: G) -> Self::BinaryOutput<C, D>
///     where
///         F: Fn(&T) -> C,
///         G: Fn(&E) -> D,
///     {
///         BiResult(match &self.0 {
///             Ok(a) => Ok(f(a)),
///             Err(e) => Err(g(e)),
///         })
///     }
/// }
///
/// // Example usage:
/// let success: BiResult<i32, &str> = BiResult(Ok(5));
/// let error: BiResult<i32, &str> = BiResult(Err("error"));
///
/// // Transform the success value
/// let doubled = success.first(|x| x * 2);
/// assert_eq!(doubled, BiResult(Ok(10)));
///
/// // Transform the error value
/// let mapped_error = error.second(|e| e.to_string());
/// assert_eq!(mapped_error, BiResult(Err("error".to_string())));
///
/// // Transform both simultaneously
/// let both_mapped = success.bimap(|x| x * 2, |e| e.to_string());
/// assert_eq!(both_mapped, BiResult(Ok(10)));
///
/// // Chain operations
/// let result = success
///     .first(|x| x + 3)      // 5 -> 8
///     .first(|x| x * 2)      // 8 -> 16
///     .second(|e| e.to_string());
/// assert_eq!(result, BiResult(Ok(16)));
///
/// ```
///
/// # Common Use Cases
///
/// Bifunctors are particularly useful in these scenarios:
///
/// 1. Error Handling:
///    - Transform both success and error values in Result types
///    - Map error types to a common error type while preserving success values
///
/// 2. Data Processing:
///    - Process pairs of values independently
///    - Transform both components of a tuple simultaneously
///
/// 3. Type Conversion:
///    - Convert between different error types in error handling
///    - Transform data structures that contain two type parameters
pub trait Bifunctor: HKT {
    /// Maps a function over the first type parameter.
    ///
    /// This is similar to `fmap` for regular functors, but it operates on the first
    /// type parameter while leaving the second unchanged.
    ///
    /// # Arguments
    /// * `f`: Function to apply to the first type parameter
    ///
    /// # Returns
    /// A new bifunctor with the first type parameter transformed
    fn first<C, F>(&self, f: F) -> Self::BinaryOutput<C, Self::Source2>
    where
        F: Fn(&Self::Source) -> C;

    /// Maps a function over the second type parameter.
    ///
    /// This is the counterpart to `first` that operates on the second type parameter
    /// while leaving the first unchanged.
    ///
    /// # Arguments
    /// * `f`: Function to apply to the second type parameter
    ///
    /// # Returns
    /// A new bifunctor with the second type parameter transformed
    fn second<D, G>(&self, f: G) -> Self::BinaryOutput<Self::Source, D>
    where
        G: Fn(&Self::Source2) -> D;

    /// Maps two functions over both type parameters simultaneously.
    ///
    /// This combines the functionality of `first` and `second` into a single operation.
    /// It's equivalent to applying `first` followed by `second`, but may be more efficient.
    ///
    /// # Arguments
    /// * `f`: Function to apply to the first type parameter
    /// * `g`: Function to apply to the second type parameter
    ///
    /// # Returns
    /// A new bifunctor with both type parameters transformed
    fn bimap<C, D, F, G>(&self, f: F, g: G) -> Self::BinaryOutput<C, D>
    where
        F: Fn(&Self::Source) -> C,
        G: Fn(&Self::Source2) -> D;
}
