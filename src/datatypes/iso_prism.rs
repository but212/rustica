//! # Iso-based Prism
//!
//! This module provides a Prism optic based on the Iso abstraction.
//! A Prism is an optic that allows safe and functional access to a variant of a sum type (such as an enum),
//! and the ability to construct the sum type from the focused value.
//!
//! ## Core Idea
//!
//! - A Prism can be generalized as an Iso of the form S <-> `Option<A>`
//! - preview/review functions are wrapped as Iso's forward/backward operations
//! - This abstraction builds on Iso to provide lawful prism behavior
//!
//! ## Functional Programming Context
//!
//! In functional programming, a Prism is a type of optic used for handling sum types (like enums in Rust).
//! Unlike Lens, which focuses on product types (like structs), Prisms handle cases where the focus might not
//! exist. This makes them particularly suitable for enum variants.
//!
//! The IsoPrism implementation specifically builds on the concept of isomorphisms (Iso), adapting
//! them to the partial nature of Prisms. This representation provides several advantages:
//!
//! - **Composable Abstractions**: IsoPrisms can be composed with other optics following function composition semantics
//! - **Type Safety**: Leverages Rust's type system to ensure correct handling of variants
//! - **Functional Purity**: Operations maintain referential transparency and avoid side effects
//! - **Law Abidance**: Follows the standard optic laws expected of well-behaved Prisms
//!
//! Related concepts in other functional languages include:
//!
//! - Haskell's Prism in libraries like lens
//! - Scala's Prism in libraries like Monocle
//! - PureScript's Prism
//! - TypeScript's Prism in fp-ts-optics
//!
//! ## Type Class Implementations
//!
//! IsoPrism implements several important functional programming interfaces:
//!
//! - **Composable Optic**: Prisms can be composed with other prisms using the `compose` method
//! - **Optional Getter**: Safely extracts a value if it exists via the `preview` method
//! - **Constructor**: Creates a value of the parent type from the focus type via `review`
//!
//! ## Examples
//!
//! ### Basic Usage
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
//! ### Composing IsoPrisms
//!
//! ```rust
//! use rustica::datatypes::iso_prism::IsoPrism;
//! use rustica::traits::iso::Iso;
//! use std::marker::PhantomData;
//!
//! // Nested enum structure
//! #[derive(Clone, Debug, PartialEq)]
//! enum Shape {
//!     Circle { radius: f64 },
//!     Rectangle { width: f64, height: f64 },
//! }
//!
//! #[derive(Clone, Debug, PartialEq)]
//! enum Drawing {
//!     Shape(Shape),
//!     Text(String),
//! }
//!
//! // Iso for focusing on the Shape variant in Drawing
//! struct ShapeIso;
//! impl Iso<Drawing, Option<Shape>> for ShapeIso {
//!     type From = Drawing;
//!     type To = Option<Shape>;
//!
//!     fn forward(&self, from: &Drawing) -> Option<Shape> {
//!         match from {
//!             Drawing::Shape(shape) => Some(shape.clone()),
//!             _ => None,
//!         }
//!     }
//!
//!     fn backward(&self, to: &Option<Shape>) -> Drawing {
//!         match to {
//!             Some(shape) => Drawing::Shape(shape.clone()),
//!             None => Drawing::Text("Placeholder".to_string()),
//!         }
//!     }
//! }
//!
//! // Iso for focusing on the Circle variant in Shape
//! struct CircleIso;
//! impl Iso<Shape, Option<f64>> for CircleIso {
//!     type From = Shape;
//!     type To = Option<f64>;
//!
//!     fn forward(&self, from: &Shape) -> Option<f64> {
//!         match from {
//!             Shape::Circle { radius } => Some(*radius),
//!             _ => None,
//!         }
//!     }
//!
//!     fn backward(&self, to: &Option<f64>) -> Shape {
//!         match to {
//!             Some(radius) => Shape::Circle { radius: *radius },
//!             None => Shape::Rectangle { width: 0.0, height: 0.0 },
//!         }
//!     }
//! }
//!
//! // Create the prisms
//! let shape_prism = IsoPrism::new(ShapeIso);
//! let circle_prism = IsoPrism::new(CircleIso);
//!
//! // Compose them to get a prism that focuses on Circle within Drawing
//! let circle_in_drawing_prism = shape_prism.compose(circle_prism);
//!
//! // Use the composed prism
//! let circle_drawing = Drawing::Shape(Shape::Circle { radius: 5.0 });
//! let rect_drawing = Drawing::Shape(Shape::Rectangle { width: 3.0, height: 4.0 });
//! let text_drawing = Drawing::Text("Hello".to_string());
//!
//! // Extract the radius from various drawings
//! assert_eq!(circle_in_drawing_prism.preview(&circle_drawing), Some(5.0));
//! assert_eq!(circle_in_drawing_prism.preview(&rect_drawing), None);
//! assert_eq!(circle_in_drawing_prism.preview(&text_drawing), None);
//!
//! // Create a new drawing with a circle of radius 10.0
//! let new_circle_drawing = circle_in_drawing_prism.review(&10.0);
//! assert_eq!(new_circle_drawing, Drawing::Shape(Shape::Circle { radius: 10.0 }));
//! ```
//!
//! ## Type Class Laws
//!
//! The `IsoPrism` type follows the standard prism laws. See the documentation for
//! the specific functions (`preview`, `review`) for examples demonstrating these laws.
//!
//! ### Review-Preview Law
//!
//! For any prism `p` and focus value `a`:
//!
//! `p.preview(&p.review(&a)) == Some(a)`
//!
//! If you review a value and then preview the result, you get back the original value.
//!
//! ### Preview-Review Law
//!
//! For any prism `p`, structure `s`, and focus value `a` where `p.preview(s) = Some(a)`:
//!
//! `p.review(&a) == s  // or equivalent to s`
//!
//! If you can preview a value from a structure, then reviewing that value should give you back
//! something equivalent to the original structure.
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
/// # Design Notes
///
/// * IsoPrism implements a prism using Iso's bidirectional mapping capabilities
/// * The abstraction treats the Prism as an isomorphism between S and `Option<A>`
/// * A well-behaved IsoPrism should uphold the prism laws
/// * Composition of IsoPrisms follows function composition semantics
///
/// # Type Parameters
/// * `S` - The sum type (e.g., enum)
/// * `A` - The type of the focused variant
/// * `L` - The Iso implementation from `S` to `Option<A>`
///
/// # Examples
///
/// ## Basic Usage
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
    pub _phantom: PhantomData<(S, A)>,
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
            _phantom: PhantomData,
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
            _phantom: PhantomData,
        };
        let composed = ComposedIso {
            first: self.iso,
            second: lifted,
            _phantom: PhantomData,
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
    pub _phantom: PhantomData<(A, B)>,
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
