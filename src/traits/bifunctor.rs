//! # Bifunctors
//!
//! A bifunctor is a type constructor that takes two type arguments and is a functor in both arguments.
//! It extends the concept of a functor to data types with two type parameters, allowing functions
//! to be mapped over both parameters independently or simultaneously.
//!
//! ## Mathematical Definition
//!
//! In category theory, a bifunctor is a functor of two arguments:
//!
//! ```text
//! F: C × D → E
//! ```
//!
//! Where C, D, and E are categories. In Rust terms, a bifunctor provides three operations:
//!
//! - `first`: Map a function over the first type parameter
//! - `second`: Map a function over the second type parameter
//! - `bimap`: Map two functions over both type parameters simultaneously
//!
//! ## Laws
//!
//! For a valid bifunctor implementation, the following laws must hold:
//!
//! 1. Identity:
//! ```text
//! bimap(id, id) == id
//! ```
//!
//! 2. Composition:
//! ```text
//! bimap(f . g, h . i) == bimap(f, h) . bimap(g, i)
//! ```
//!
//! ## Common Bifunctors
//!
//! Some common bifunctors in Rust include:
//!
//! - `Either<L, R>`: Can be mapped over both branches (Left/Right)
//! - `Tuple2<A, B>`: Functor in both tuple components `A` and `B`
//!
//! ## Use Cases
//!
//! Bifunctors are particularly useful for:
//!
//! 1. **Error Handling**: Transform both branches of sum types (e.g., Left/Right)
//! 2. **Data Transformation**: Process pairs of values independently
//! 3. **Type Conversion**: Convert between different type combinations while preserving structure
//!
//! ## Examples
//!
//! ```rust
//! use rustica::traits::bifunctor::Bifunctor;
//! use rustica::traits::hkt::{HKT, BinaryHKT};
//!
//! // Example with a tuple type
//! #[derive(Debug, PartialEq, Clone)]
//! struct BiTuple<A, B>(A, B);
//!
//! impl<A, B> HKT for BiTuple<A, B> {
//!     type Source = A;
//!     type Output<U> = BiTuple<U, B>;
//! }
//!
//! impl<A, B> BinaryHKT for BiTuple<A, B> {
//!     type Source2 = B;
//!     type BinaryOutput<U, V> = BiTuple<U, V>;
//!
//!     fn map_second<F, NewType2>(&self, f: F) -> Self::BinaryOutput<Self::Source, NewType2>
//!     where
//!         F: Fn(&Self::Source2) -> NewType2,
//!         Self::Source: Clone,
//!     {
//!         BiTuple(self.0.clone(), f(&self.1))
//!     }
//!
//!     fn map_second_owned<F, NewType2>(self, f: F) -> Self::BinaryOutput<Self::Source, NewType2>
//!     where
//!         F: Fn(Self::Source2) -> NewType2,
//!     {
//!         BiTuple(self.0, f(self.1))
//!     }
//! }
//!
//! impl<A, B> Bifunctor for BiTuple<A, B>
//! where
//!     A: Clone,
//!     B: Clone,
//! {
//!     fn first<C, F>(&self, f: F) -> BiTuple<C, B>
//!     where
//!         F: Fn(&A) -> C,
//!     {
//!         BiTuple(f(&self.0), self.1.clone())
//!     }
//!
//!     fn second<D, G>(&self, g: G) -> BiTuple<A, D>
//!     where
//!         G: Fn(&B) -> D,
//!     {
//!         BiTuple(self.0.clone(), g(&self.1))
//!     }
//!
//!     fn bimap<C, D, F, G>(&self, f: F, g: G) -> BiTuple<C, D>
//!     where
//!         F: Fn(&A) -> C,
//!         G: Fn(&B) -> D,
//!     {
//!         BiTuple(f(&self.0), g(&self.1))
//!     }
//! }
//!
//! // Usage
//! let tuple = BiTuple(10, "hello");
//! let mapped = tuple.bimap(|x| x * 2, |s| s.len());
//! assert_eq!(mapped.0, 20);
//! assert_eq!(mapped.1, 5);
//! ```
//!
//! ## Relationship to Other Traits
//!
//! - **Functor**: A bifunctor is a generalization of a functor to two type parameters
//! - **Profunctor**: While a bifunctor is covariant in both arguments, a profunctor is
//!   contravariant in its first argument and covariant in its second

use crate::traits::hkt::BinaryHKT;

/// A bifunctor is a type constructor that takes two type arguments and can be mapped over both sides.
/// This means it provides a way to map functions over both type parameters independently or simultaneously.
///
/// Note: in this crate, `Bifunctor` is defined in terms of `BinaryHKT`:
///
/// - `first` maps over `Self::Source`
/// - `second` maps over `Self::Source2`
///
/// # Important: Type Parameter Mapping
///
/// For some types, the associated types may not correspond to the lexical order of type parameters.
/// This is particularly important for `Either<L, R>`:
///
/// | Type | `Source` | `Source2` | Rationale |
/// |------|----------|-----------|-----------|
/// | `Either<L, R>` | `R` (Right) | `L` (Left) | Right is the "success" path, consistent with Functor |
/// | `Result<T, E>` | `T` (Ok) | `E` (Err) | Ok is the "success" path |
/// | `(A, B)` | `A` | `B` | Lexical order |
///
/// This convention follows the functional programming tradition where the "right" or "success"
/// value is the one that gets mapped by default (via Functor's `fmap`).
///
/// # Laws
///
/// A valid bifunctor instance must satisfy these laws:
///
/// 1. Identity:
///    ```text
///    bimap(id, id) == id
///    ```
///
/// 2. Composition:
///    ```text
///    bimap(f . g, h . i) == bimap(f, h) . bimap(g, i)
///    ```
///
/// # Examples
///
/// Here's an example implementation for a wrapper around `Result`:
/// ```rust
/// use std::fmt::Debug;
/// use rustica::traits::hkt::{HKT, BinaryHKT};
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
/// }
///
/// impl<T, E> BinaryHKT for BiResult<T, E> {
///     type Source2 = E;
///     type BinaryOutput<U, V> = BiResult<U, V>;
///
///     fn map_second<F, NewType2>(&self, f: F) -> Self::BinaryOutput<T, NewType2>
///     where
///         F: Fn(&Self::Source2) -> NewType2,
///         T: Clone,
///     {
///         BiResult(match &self.0 {
///             Ok(a) => Ok(a.clone()),
///             Err(e) => Err(f(e)),
///         })
///     }
///
///     fn map_second_owned<F, NewType2>(self, f: F) -> Self::BinaryOutput<T, NewType2>
///     where
///         F: Fn(Self::Source2) -> NewType2,
///     {
///         BiResult(match self.0 {
///             Ok(a) => Ok(a),
///             Err(e) => Err(f(e)),
///         })
///     }
/// }
///
/// impl<T: Clone, E: Clone> Bifunctor for BiResult<T, E> {
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
pub trait Bifunctor: BinaryHKT {
    /// Maps a function over `Self::Source`.
    ///
    /// Maps a function over `Self::Source`, leaving `Self::Source2` unchanged.
    ///
    /// # Type Parameters
    ///
    /// * `C`: The new type for `Self::Source` after transformation
    /// * `F`: The function type to apply
    ///
    /// # Arguments
    ///
    /// * `f`: Function to apply to `Self::Source`
    ///
    /// # Returns
    ///
    /// A new bifunctor with `Self::Source` transformed
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::either::Either;
    /// use rustica::traits::bifunctor::Bifunctor;
    ///
    /// // For Either<L, R>, `Self::Source` is the Right value (R)
    /// let either: Either<String, i32> = Either::Right(10);
    /// let mapped = either.first(|n| n * 2);
    /// assert_eq!(mapped, Either::Right(20));
    /// ```
    fn first<C, F>(&self, f: F) -> Self::BinaryOutput<C, Self::Source2>
    where
        F: Fn(&Self::Source) -> C,
        C: Clone;

    /// Maps a function over `Self::Source2`.
    ///
    /// Maps a function over `Self::Source2`, leaving `Self::Source` unchanged.
    ///
    /// # Type Parameters
    ///
    /// * `D`: The new type for `Self::Source2` after transformation
    /// * `G`: The function type to apply
    ///
    /// # Arguments
    ///
    /// * `f`: Function to apply to `Self::Source2`
    ///
    /// # Returns
    ///
    /// A new bifunctor with `Self::Source2` transformed
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::either::Either;
    /// use rustica::traits::bifunctor::Bifunctor;
    ///
    /// // For Either<L, R>, `Self::Source2` is the Left value (L)
    /// let left: Either<String, i32> = Either::Left("hello".to_string());
    /// let mapped = left.second(|s| s.len());
    /// assert_eq!(mapped, Either::Left(5usize));
    /// ```
    fn second<D, G>(&self, f: G) -> Self::BinaryOutput<Self::Source, D>
    where
        G: Fn(&Self::Source2) -> D,
        D: Clone;

    /// Maps two functions over both type parameters simultaneously.
    ///
    /// This combines the functionality of `first` and `second` into a single operation.
    /// It's equivalent to applying `first` followed by `second`, but may be more efficient.
    ///
    /// # Type Parameters
    ///
    /// * `C`: The new type for the first parameter after transformation
    /// * `D`: The new type for the second parameter after transformation
    /// * `F`: The function type to apply to the first parameter
    /// * `G`: The function type to apply to the second parameter
    ///
    /// # Arguments
    ///
    /// * `f`: Function to apply to the first type parameter
    /// * `g`: Function to apply to the second type parameter
    ///
    /// # Returns
    ///
    /// A new bifunctor with both type parameters transformed
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::traits::bifunctor::Bifunctor;
    /// use rustica::traits::hkt::{HKT, BinaryHKT};
    ///
    /// #[derive(Debug, PartialEq, Clone)]
    /// struct Pair<A, B>(A, B);
    ///
    /// impl<A, B> HKT for Pair<A, B> {
    ///     type Source = A;
    ///     type Output<U> = Pair<U, B>;
    /// }
    ///
    /// impl<A, B> BinaryHKT for Pair<A, B> {
    ///     type Source2 = B;
    ///     type BinaryOutput<U, V> = Pair<U, V>;
    ///
    ///     fn map_second<F, NewType2>(&self, f: F) -> Self::BinaryOutput<Self::Source, NewType2>
    ///     where
    ///         F: Fn(&Self::Source2) -> NewType2,
    ///         Self::Source: Clone,
    ///     {
    ///         Pair(self.0.clone(), f(&self.1))
    ///     }
    ///
    ///     fn map_second_owned<F, NewType2>(self, f: F) -> Self::BinaryOutput<Self::Source, NewType2>
    ///     where
    ///         F: Fn(Self::Source2) -> NewType2,
    ///     {
    ///         Pair(self.0, f(self.1))
    ///     }
    /// }
    ///
    /// impl<A, B> Bifunctor for Pair<A, B>
    /// where
    ///     A: Clone,
    ///     B: Clone,
    /// {
    ///     fn first<C, F>(&self, f: F) -> Pair<C, B>
    ///     where
    ///         F: Fn(&A) -> C,
    ///     {
    ///         Pair(f(&self.0), self.1.clone())
    ///     }
    ///
    ///     fn second<D, G>(&self, g: G) -> Pair<A, D>
    ///     where
    ///         G: Fn(&B) -> D,
    ///     {
    ///         Pair(self.0.clone(), g(&self.1))
    ///     }
    ///
    ///     fn bimap<C, D, F, G>(&self, f: F, g: G) -> Pair<C, D>
    ///     where
    ///         F: Fn(&A) -> C,
    ///         G: Fn(&B) -> D,
    ///     {
    ///         Pair(f(&self.0), g(&self.1))
    ///     }
    /// }
    ///
    /// let pair: Pair<i32, String> = Pair(5, "hello".to_string());
    /// let mapped = pair.bimap(|x| x * 2, |s| s.len());
    /// assert_eq!(mapped, Pair(10, 5));
    ///
    /// // Equivalent to chaining first and second:
    /// let alternative = pair
    ///     .first(|x| x * 2)
    ///     .second(|s| s.len());
    /// assert_eq!(alternative, Pair(10, 5));
    /// ```
    fn bimap<C, D, F, G>(&self, f: F, g: G) -> Self::BinaryOutput<C, D>
    where
        F: Fn(&Self::Source) -> C,
        G: Fn(&Self::Source2) -> D,
        C: Clone,
        D: Clone;
}
