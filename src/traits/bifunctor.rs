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
//! - `Result<T, E>`: Functor in both success `T` and error `E`
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
//! use rustica::datatypes::validated::Validated;
//! use rustica::traits::bifunctor::Bifunctor;
//!
//! let value: Validated<String, i32> = Validated::valid(10);
//! let mapped = value.bimap(|n| n * 2, |error| format!("{error}!"));
//! assert_eq!(mapped, Validated::valid(20));
//!
//! let error: Validated<String, i32> = Validated::invalid("missing".into());
//! assert_eq!(error.second(|message| message.len()), Validated::invalid(7));
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
/// The concrete type determines which parameters are `Source` and `Source2`.
/// For example, `Validated<E, A>` maps its valid value with `first` and its error with
/// `second`; both can be transformed with `bimap`:
///
/// ```rust
/// use rustica::datatypes::validated::Validated;
/// use rustica::traits::bifunctor::Bifunctor;
///
/// let value: Validated<String, i32> = Validated::valid(5);
/// let result = value.bimap(|number| number * 2, |error| format!("{error}!"));
/// assert_eq!(result, Validated::valid(10));
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
    /// use rustica::traits::bifunctor::Bifunctor;
    /// use rustica::datatypes::validated::Validated;
    ///
    /// // For Validated<E, A>, `Self::Source` is the Valid value (A)
    /// let valid: Validated<String, i32> = Validated::valid(10);
    /// let mapped = valid.first(|n| n * 2);
    /// assert_eq!(mapped, Validated::valid(20));
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
    /// use rustica::traits::bifunctor::Bifunctor;
    /// use rustica::datatypes::validated::Validated;
    ///
    /// // For Validated<E, A>, `Self::Source2` is the Error value (E)
    /// let invalid: Validated<String, i32> = Validated::invalid("hello".to_string());
    /// let mapped = invalid.second(|s| s.len());
    /// assert_eq!(mapped, Validated::invalid(5usize));
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
    /// use rustica::datatypes::validated::Validated;
    /// use rustica::traits::bifunctor::Bifunctor;
    ///
    /// let value: Validated<String, i32> = Validated::valid(5);
    /// let mapped = value.bimap(|number| number * 2, |error| format!("{error}!"));
    /// assert_eq!(mapped, Validated::valid(10));
    /// ```
    fn bimap<C, D, F, G>(&self, f: F, g: G) -> Self::BinaryOutput<C, D>
    where
        F: Fn(&Self::Source) -> C,
        G: Fn(&Self::Source2) -> D,
        C: Clone,
        D: Clone;
}
