//! The `HKT` trait enables emulation of higher-kinded types in Rust.
//!
//! Higher-kinded types (HKTs) are type constructors that take a type and return
//! another type. Rust does not directly support higher-kinded types, but we can
//! emulate them using associated types.
//!
//! This module provides the `HKT` trait and related traits that form the
//! foundation for higher-kinded polymorphism in the Rustica library.
//!
//! ## Limitations of HKT Simulation in Rust
//!
//! While this implementation provides a workable approximation of higher-kinded types,
//! it has several important limitations compared to true HKT support:
//!
//! ### 1. **Associated Type Constraints**
//! - Each type constructor must explicitly implement the trait (typically once per wrapper type)
//! - Cannot express arbitrary type constructors at the type level
//! - Limited composability compared to true HKT systems
//!
//! ### 2. **Inference Limitations**
//! - Type inference often requires explicit type annotations
//! - Complex generic bounds can become unwieldy
//! - Some mathematically valid operations cannot be expressed
//!
//! ### 3. **Runtime Overhead**
//! - HKT emulation can lead to more complex bounds and less ergonomic APIs
//! - Some patterns may require trait objects or boxing (depending on the abstraction)
//! - Performance is typically still monomorphized, but designs built on HKT-style traits can
//!   encourage more abstraction layers
//!
//! ### 4. **Expressiveness Gaps**
//! - Cannot represent some category theory concepts directly
//! - Limited support for type-level computation
//! - Some functor laws cannot be verified at compile time
//!
//! ### 5. **Ergonomics Issues**
//! - Verbose syntax for complex type relationships
//! - Difficult to write generic code over multiple HKT instances
//! - Error messages can be cryptic and hard to debug
//!
//! Despite these limitations, this HKT simulation provides a practical foundation
//! for functional programming patterns in Rust while maintaining type safety.
//!
//! # Examples
//!
//! ```rust
//! use rustica::traits::hkt::HKT;
//!
//! // `Output` names the same type constructor with a new contained type.
//! type TextOption = <Option<i32> as HKT>::Output<String>;
//! let value: TextOption = Some("hkt".to_owned());
//! assert_eq!(value.as_deref(), Some("hkt"));
//! ```

/// A trait for types that can be treated as higher-kinded types.
///
/// In category theory, a functor is a mapping between categories. In Rust terms,
/// it can be seen as a container type that can be transformed while preserving
/// its structure.
///
/// The `HKT` trait provides a way to refer to the contained type and to construct
/// the same container with a different contained type.
///
/// # Type Parameters
///
/// * `Source` - The type contained in this HKT
/// * `Output<U>` - The same HKT but containing type U instead of Source
///
pub trait HKT {
    /// The type contained in this HKT.
    type Source;

    /// The same HKT but containing type `NewType` instead of `Source`.
    type Output<NewType>: HKT<Source = NewType>;
}

/// A trait for higher-kinded types that have two type parameters.
///
/// This trait extends the `HKT` trait to allow for types that have a second type
/// parameter, such as `Result<T, E>` or `Validated<E, T>`.
///
/// # Important: Type Parameter Mapping Convention
///
/// The mapping between lexical type parameters and `Source`/`Source2` follows
/// the functional programming convention where the "success" or "right" value
/// is the primary content (mapped by `Functor::fmap`):
///
/// | Type | `Source` (primary) | `Source2` (secondary) |
/// |------|--------------------|-----------------------|
/// | `Result<T, E>` | `T` (Ok value) | `E` (Err value) |
/// | `Validated<E, T>` | `T` (Valid value) | `E` (Error value) |
///
/// # Examples
///
/// `BinaryHKT` is useful when a type has a primary value and a separately mapped
/// secondary value:
///
/// ```rust
/// use rustica::datatypes::validated::Validated;
/// use rustica::traits::hkt::BinaryHKT;
///
/// let value = Validated::<String, i32>::invalid("bad".to_owned());
/// let mapped = value.map_second_owned(|error| error.len());
/// let _: Validated<usize, i32> = mapped;
/// ```
pub trait BinaryHKT: HKT {
    /// The second type parameter of this HKT.
    type Source2;

    /// The same HKT but with both type parameters replaced.
    type BinaryOutput<Type1, Type2>: BinaryHKT<Source = Type1, Source2 = Type2>;

    /// Maps a function over the second type parameter.
    ///
    /// # Type Parameters
    ///
    /// * `F` - The function type
    /// * `NewType2` - The type of the transformed second parameter
    ///
    /// # Parameters
    ///
    /// * `f` - A function that transforms the second type parameter
    ///
    /// # Returns
    ///
    /// A new HKT with the second type parameter transformed
    fn map_second<F, NewType2>(&self, f: F) -> Self::BinaryOutput<Self::Source, NewType2>
    where
        F: Fn(&Self::Source2) -> NewType2,
        Self::Source: Clone,
        Self::Source2: Clone,
        NewType2: Clone;

    /// Maps a function over the second type parameter, consuming the HKT.
    ///
    /// # Type Parameters
    ///
    /// * `F` - The function type
    /// * `NewType2` - The type of the transformed second parameter
    ///
    /// # Parameters
    ///
    /// * `f` - A function that transforms the second type parameter
    ///
    /// # Returns
    ///
    /// A new HKT with the second type parameter transformed
    fn map_second_owned<F, NewType2>(self, f: F) -> Self::BinaryOutput<Self::Source, NewType2>
    where
        F: Fn(Self::Source2) -> NewType2,
        NewType2: Clone;
}

// Implementations for common Rust types

impl<T> HKT for Option<T> {
    type Source = T;
    type Output<U> = Option<U>;
}

impl<T, E> HKT for Result<T, E>
where
    E: Clone,
{
    type Source = T;
    type Output<U> = Result<U, E>;
}

impl<T> HKT for Vec<T> {
    type Source = T;
    type Output<U> = Vec<U>;
}

impl<T> HKT for Box<T> {
    type Source = T;
    type Output<U> = Box<U>;
}
