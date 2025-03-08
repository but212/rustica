//! The `HKT` trait enables emulation of higher-kinded types in Rust.
//!
//! Higher-kinded types (HKTs) are type constructors that take a type and return
//! another type. Rust does not directly support higher-kinded types, but we can
//! emulate them using associated types.
//!
//! This module provides the `HKT` trait and related traits that form the
//! foundation for higher-kinded polymorphism in the Rustica library.
//!
//! # Examples
//!
//! ```rust
//! use rustica::traits::hkt::HKT;
//!
//! // Define our own wrapper types for the examples
//! // MyOption is a simple wrapper around Option
//! #[derive(Clone)]
//! struct MyOption<T>(Option<T>);
//!
//! // Implement HKT for our custom wrapper
//! impl<T> HKT for MyOption<T> {
//!     type Source = T;
//!     type Output<U> = MyOption<U>;
//! }
//!
//! // MyVec is a simple wrapper around Vec
//! #[derive(Clone)]
//! struct MyVec<T>(Vec<T>);
//!
//! // Implement HKT for our custom wrapper
//! impl<T> HKT for MyVec<T> {
//!     type Source = T;
//!     type Output<U> = MyVec<U>;
//! }
//!
//! // Writing a function that works with any HKT
//! fn map_hkt<H, T, U, F>(value: &H, f: F) -> H::Output<U>
//! where
//!     H: HKT<Source = T>,
//!     F: Fn(&T) -> U,
//! {
//!     // This would be the implementation in a real case
//!     // Here we're just demonstrating the type signatures
//!     unimplemented!()
//! }
//! ```

use std::marker::PhantomData;

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
/// # Examples
///
/// ```rust
/// use rustica::traits::hkt::HKT;
///
/// // Define our own wrapper types for the examples
/// // MyOption is a simple wrapper around Option
/// #[derive(Clone)]
/// struct MyOption<T>(Option<T>);
///
/// // Implement HKT for our custom wrapper
/// impl<T> HKT for MyOption<T> {
///     type Source = T;
///     type Output<U> = MyOption<U>;
/// }
///
/// // MyVec is a simple wrapper around Vec
/// #[derive(Clone)]
/// struct MyVec<T>(Vec<T>);
///
/// // Implement HKT for our custom wrapper
/// impl<T> HKT for MyVec<T> {
///     type Source = T;
///     type Output<U> = MyVec<U>;
/// }
///
/// // A function that uses HKT
/// fn transform<H, T, U>(container: &H, value: &T) -> H::Output<U>
/// where
///     H: HKT<Source = T>,
///     T: Clone,
///     U: From<T>,
/// {
///     // Just an example signature
///     unimplemented!()
/// }
/// ```
pub trait HKT {
    /// The type contained in this HKT.
    type Source;

    /// The same HKT but containing type `NewType` instead of `Source`.
    type Output<NewType>: HKT<Source = NewType>;
}

/// A trait for higher-kinded types that have two type parameters.
///
/// This trait extends the `HKT` trait to allow for types that have a second type
/// parameter, such as `Result<T, E>` or `Either<L, R>`.
///
/// # Examples
///
/// ```rust
/// use rustica::traits::hkt::{HKT, BinaryHKT};
///
/// // Define our own wrapper types for the examples
/// // MyResult is a simple wrapper around Result
/// #[derive(Clone)]
/// struct MyResult<T, E>(Result<T, E>);
///
/// // Implement HKT for our custom wrapper
/// impl<T, E> HKT for MyResult<T, E> {
///     type Source = T;
///     type Output<U> = MyResult<U, E>;
/// }
///
/// // Implement BinaryHKT for our custom wrapper
/// impl<T, E> BinaryHKT for MyResult<T, E> {
///     type Source2 = E;
///     type BinaryOutput<Type1, Type2> = MyResult<Type1, Type2>;
///     
///     fn map_second<F, NewType2>(&self, f: F) -> Self::BinaryOutput<Self::Source, NewType2>
///     where
///         F: Fn(&Self::Source2) -> NewType2,
///         Self::Source: Clone,
///         Self::Source2: Clone,
///     {
///         MyResult(match &self.0 {
///             Ok(v) => Ok(v.clone()),
///             Err(e) => Err(f(e)),
///         })
///     }
///
///     fn map_second_owned<F, NewType2>(self, f: F) -> Self::BinaryOutput<Self::Source, NewType2>
///     where
///         F: Fn(Self::Source2) -> NewType2,
///     {
///         MyResult(match self.0 {
///             Ok(v) => Ok(v),
///             Err(e) => Err(f(e)),
///         })
///     }
/// }
///
/// // A function that works with BinaryHKT
/// fn map_second_generic<H, T, E, U, F>(value: &H, f: F) -> H::BinaryOutput<T, U>
/// where
///     H: BinaryHKT<Source = T, Source2 = E>,
///     F: Fn(&E) -> U,
///     T: Clone,
///     E: Clone,
/// {
///     value.map_second(f)
/// }
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
        Self::Source2: Clone;

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
        F: Fn(Self::Source2) -> NewType2;
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

impl<T> HKT for std::marker::PhantomData<T> {
    type Source = T;
    type Output<U> = std::marker::PhantomData<U>;
}

/// A phantom type used to represent a higher-kinded type at the type level.
///
/// This struct is useful for type-level programming with higher-kinded types.
/// It has no runtime representation and is used only for type checking.
///
/// # Type Parameters
///
/// * `H`: The higher-kinded type to wrap
/// * `T`: The source type that the higher-kinded type will be applied to
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct HKTType<H, T>(PhantomData<H>, PhantomData<T>);

impl<H, T> HKTType<H, T> {
    /// Creates a new phantom type representing an application of type H to type T.
    ///
    /// # Returns
    ///
    /// A new phantom type
    #[inline]
    pub fn new() -> Self {
        Self(PhantomData, PhantomData)
    }
}