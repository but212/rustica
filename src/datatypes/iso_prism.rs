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

use crate::traits::iso::{ComposedIso, Iso};
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
#[derive(Clone, Debug, PartialEq)]
pub struct IsoPrism<S, A, L: Iso<S, Option<A>, From = S, To = Option<A>>> {
    pub iso: L,
    pub phantom: PhantomData<(S, A)>,
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
    #[inline]
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
    #[inline]
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
    #[inline]
    pub fn review(&self, a: &A) -> S
    where
        S: Clone,
        A: Clone,
    {
        self.iso.backward(&Some(a.clone()))
    }

    /// Composes this prism with another prism.
    ///
    /// # Arguments
    /// * `other` - The other prism to compose with.
    ///
    /// # Returns
    /// A new prism that is the composition of this prism and the other prism.
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
    /// # struct BarPrismIso;
    /// # impl Iso<i32, Option<String>> for BarPrismIso {
    /// #     type From = i32;
    /// #     type To = Option<String>;
    /// #     fn forward(&self, from: &i32) -> Option<String> {
    /// #         Some(from.to_string())
    /// #     }
    /// #     fn backward(&self, to: &Option<String>) -> i32 {
    /// #         to.as_ref().map(|s| s.parse::<i32>().unwrap()).unwrap_or(0)
    /// #     }
    /// # }
    /// let foo_prism = IsoPrism::new(FooPrismIso);
    /// let bar_prism = IsoPrism::new(BarPrismIso);
    /// let composed = foo_prism.compose(bar_prism);
    /// let foo = MyEnum::Foo(10);
    /// assert_eq!(composed.preview(&foo), Some("10".to_string()));
    /// ```
    pub fn compose<B, L2>(self, other: IsoPrism<A, B, L2>) -> ComposedIsoPrism<S, B, L, L2, A>
    where
        L2: Iso<A, Option<B>, From = A, To = Option<B>>,
        S: Clone,
        A: Clone,
        B: Clone,
    {
        let lifted = LiftedPrismIso {
            inner: other.iso,
            phantom: PhantomData,
        };
        let composed = ComposedIso {
            first: self.iso,
            second: lifted,
            phantom: PhantomData,
        };
        IsoPrism::new(composed)
    }
}

type ComposedIsoPrism<S, B, L, L2, A> =
    IsoPrism<S, B, ComposedIso<L, LiftedPrismIso<L2, A, B>, S, Option<A>, Option<B>>>;

/// Lifts a prism to work with `Option`s.
///
/// This struct is used to lift a prism to work with `Option`s, allowing it to be composed with other prisms.
pub struct LiftedPrismIso<L2, A, B>
where
    L2: Iso<A, Option<B>, From = A, To = Option<B>>,
{
    pub inner: L2,
    pub phantom: PhantomData<(A, B)>,
}

impl<L2, A, B> Iso<Option<A>, Option<B>> for LiftedPrismIso<L2, A, B>
where
    L2: Iso<A, Option<B>, From = A, To = Option<B>>,
    A: Clone,
    B: Clone,
{
    type From = Option<A>;
    type To = Option<B>;

    #[inline]
    fn forward(&self, from: &Option<A>) -> Option<B> {
        match from {
            Some(a) => self.inner.forward(a),
            None => None,
        }
    }

    #[inline]
    fn backward(&self, to: &Option<B>) -> Option<A> {
        to.as_ref().map(|b| self.inner.backward(&Some(b.clone())))
    }
}