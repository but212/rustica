//! # Iso-based Prism
//!
//! This module provides a Prism optic based on the Iso abstraction.
//! A Prism is an optic that allows safe and functional access to a variant of a sum type (such as an enum),
//! and the ability to construct the sum type from the focused value.
//!
//! ## Core Idea
//!
//! - A Prism can be generalized as an Iso of the form S <-> Option<A>
//! - preview/review functions are wrapped as Iso's forward/backward operations
//!
//! ## Examples
//!
//! ```rust
//! use rustica::datatypes::iso_prism::IsoPrism;
//! use rustica::traits::iso::Iso;
//!
//! #[derive(Clone, Debug, PartialEq)]
//! enum MyEnum {
//!     Foo(i32),
//!     Bar(String),
//! }
//!
//! struct FooPrismIso;
//! impl Iso<MyEnum, Option<i32>> for FooPrismIso {
//!     type From = MyEnum;
//!     type To = Option<i32>;
//!     fn forward(&self, from: &MyEnum) -> Option<i32> {
//!         match from {
//!             MyEnum::Foo(x) => Some(*x),
//!             _ => None,
//!         }
//!     }
//!     fn backward(&self, to: &Option<i32>) -> MyEnum {
//!         match to {
//!             Some(x) => MyEnum::Foo(*x),
//!             None => MyEnum::Bar("default".to_string()),
//!         }
//!     }
//! }
//!
//! let prism = IsoPrism::new(FooPrismIso);
//! let foo = MyEnum::Foo(10);
//! assert_eq!(prism.preview(&foo), Some(10));
//! let bar = MyEnum::Bar("hi".to_string());
//! assert_eq!(prism.preview(&bar), None);
//! let reviewed = prism.review(&20);
//! assert_eq!(reviewed, MyEnum::Foo(20));
//! ```
//!
//! ## Lawful Optic Laws
//!
//! - **Review-Preview Law:** `prism.preview(&prism.review(&a)) == Some(a)`
//! - **Preview-Review Law:** If `prism.preview(s) == Some(a)`, then `prism.review(&a) == s`
//!
//! See also: [`crate::datatypes::prism`], [`crate::traits::iso::Iso`]

use crate::traits::iso::Iso;
use std::marker::PhantomData;

/// Iso-based Prism optic.
///
/// This struct represents a Prism built on top of an Iso abstraction.
/// It allows safe and functional partial access to a variant of a sum type (e.g., enum variant),
/// and the ability to construct the sum type from the focused value.
///
/// # Type Parameters
/// * `S` - The sum type (e.g., enum)
/// * `A` - The type of the focused variant
/// * `L` - The Iso implementation from `S` to `Option<A>`
///
/// # Examples
///
/// ```rust
/// use rustica::datatypes::iso_prism::IsoPrism;
/// use rustica::traits::iso::Iso;
///
/// // Define an enum (sum type)
/// #[derive(Clone, Debug, PartialEq)]
/// enum Result<T, E> {
///     Ok(T),
///     Err(E),
/// }
///
/// // Create an Iso for the Ok variant
/// struct OkIso<T, E>(std::marker::PhantomData<(T, E)>);
///
/// impl<T: Clone, E> Iso<Result<T, E>, Option<T>> for OkIso<T, E> {
///     type From = Result<T, E>;
///     type To = Option<T>;
///
///     fn forward(&self, from: &Result<T, E>) -> Option<T> {
///         match from {
///             Result::Ok(t) => Some(t.clone()),
///             Result::Err(_) => None,
///         }
///     }
///
///     fn backward(&self, to: &Option<T>) -> Result<T, E> {
///         match to {
///             Some(t) => Result::Ok(t.clone()),
///             None => panic!("Cannot construct Err variant without an error value"),
///         }
///     }
/// }
///
/// // Create and use the prism
/// let ok_prism = IsoPrism::new(OkIso(std::marker::PhantomData));
/// let ok_value = Result::Ok::<_, &str>("success".to_string());
/// let err_value = Result::Err::<String, _>("error");
///
/// assert_eq!(ok_prism.preview(&ok_value), Some("success".to_string()));
/// assert_eq!(ok_prism.preview(&err_value), None);
/// assert_eq!(ok_prism.review(&"new success".to_string()), Result::Ok("new success".to_string()));
/// ```
pub struct IsoPrism<S, A, L: Iso<S, Option<A>, From = S, To = Option<A>>> {
    iso: L,
    phantom: PhantomData<(S, A)>,
}

impl<S, A, L> IsoPrism<S, A, L>
where
    L: Iso<S, Option<A>, From = S, To = Option<A>>,
{
    /// Creates a new IsoPrism from an Iso implementation.
    ///
    /// # Arguments
    /// * `iso` - An Iso instance that defines a bidirectional mapping between the sum type and an Option of the focused variant.
    ///
    /// # Returns
    /// A new IsoPrism instance.
    ///
    /// # Examples
    /// ```rust
    /// use rustica::datatypes::iso_prism::IsoPrism;
    /// use rustica::traits::iso::Iso;
    ///
    /// #[derive(Clone, Debug, PartialEq)]
    /// enum MyEnum { Foo(i32), Bar(String) }
    ///
    /// struct FooPrismIso;
    /// impl Iso<MyEnum, Option<i32>> for FooPrismIso {
    ///     type From = MyEnum;
    ///     type To = Option<i32>;
    ///     fn forward(&self, from: &MyEnum) -> Option<i32> {
    ///         match from {
    ///             MyEnum::Foo(x) => Some(*x),
    ///             _ => None,
    ///         }
    ///     }
    ///     fn backward(&self, to: &Option<i32>) -> MyEnum {
    ///         match to {
    ///             Some(x) => MyEnum::Foo(*x),
    ///             None => MyEnum::Bar("default".to_string()),
    ///         }
    ///     }
    /// }
    ///
    /// let prism = IsoPrism::new(FooPrismIso);
    /// let foo = MyEnum::Foo(10);
    /// assert_eq!(prism.preview(&foo), Some(10));
    /// let bar = MyEnum::Bar("hi".to_string());
    /// assert_eq!(prism.preview(&bar), None);
    /// let reviewed = prism.review(&20);
    /// assert_eq!(reviewed, MyEnum::Foo(20));
    /// ```
    pub fn new(iso: L) -> Self {
        Self {
            iso,
            phantom: PhantomData,
        }
    }

    /// Attempts to extract the focused value from the sum type.
    ///
    /// # Arguments
    /// * `s` - A reference to the sum type value.
    ///
    /// # Returns
    /// An Option containing the focused value if present, or None otherwise.
    ///
    /// # Examples
    /// ```rust
    /// # use rustica::datatypes::iso_prism::IsoPrism;
    /// # use rustica::traits::iso::Iso;
    /// # #[derive(Clone, Debug, PartialEq)]
    /// # enum MyEnum { Foo(i32), Bar(String) }
    /// # struct FooPrismIso;
    /// # impl Iso<MyEnum, Option<i32>> for FooPrismIso {
    /// #     type From = MyEnum;
    /// #     type To = Option<i32>;
    /// #     fn forward(&self, from: &MyEnum) -> Option<i32> {
    /// #         match from {
    /// #             MyEnum::Foo(x) => Some(*x),
    /// #             _ => None,
    /// #         }
    /// #     }
    /// #     fn backward(&self, to: &Option<i32>) -> MyEnum {
    /// #         match to {
    /// #             Some(x) => MyEnum::Foo(*x),
    /// #             None => MyEnum::Bar("default".to_string()),
    /// #         }
    /// #     }
    /// # }
    /// let prism = IsoPrism::new(FooPrismIso);
    /// let foo = MyEnum::Foo(10);
    /// assert_eq!(prism.preview(&foo), Some(10));
    /// let bar = MyEnum::Bar("hi".to_string());
    /// assert_eq!(prism.preview(&bar), None);
    /// ```
    pub fn preview(&self, s: &S) -> Option<A>
    where
        A: Clone,
    {
        self.iso.forward(s)
    }

    /// Constructs the sum type from a focused value.
    ///
    /// # Arguments
    /// * `a` - A reference to the focused value.
    ///
    /// # Returns
    /// The sum type value constructed from the focused value.
    ///
    /// # Examples
    /// ```rust
    /// # use rustica::datatypes::iso_prism::IsoPrism;
    /// # use rustica::traits::iso::Iso;
    /// # #[derive(Clone, Debug, PartialEq)]
    /// # enum MyEnum { Foo(i32), Bar(String) }
    /// # struct FooPrismIso;
    /// # impl Iso<MyEnum, Option<i32>> for FooPrismIso {
    /// #     type From = MyEnum;
    /// #     type To = Option<i32>;
    /// #     fn forward(&self, from: &MyEnum) -> Option<i32> {
    /// #         match from {
    /// #             MyEnum::Foo(x) => Some(*x),
    /// #             _ => None,
    /// #         }
    /// #     }
    /// #     fn backward(&self, to: &Option<i32>) -> MyEnum {
    /// #         match to {
    /// #             Some(x) => MyEnum::Foo(*x),
    /// #             None => MyEnum::Bar("default".to_string()),
    /// #         }
    /// #     }
    /// # }
    /// let prism = IsoPrism::new(FooPrismIso);
    /// let reviewed = prism.review(&20);
    /// assert_eq!(reviewed, MyEnum::Foo(20));
    /// ```
    pub fn review(&self, a: &A) -> S
    where
        S: Clone,
        A: Clone,
    {
        self.iso.backward(&Some(a.clone()))
    }
}
