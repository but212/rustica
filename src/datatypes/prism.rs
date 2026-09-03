//! # Prism (`Prism<S, A, PreviewFn, ReviewFn>`)
//!
//! Prisms are optics that focus on a specific case of a sum type.
//!
//! A prism provides a way to:
//! - Selectively view a specific variant of an enum (sum type)
//! - Construct a value of the sum type from a value of the specific variant
//!
//! ## Quick Start
//!
//! ```rust
//! use rustica::datatypes::prism::Prism;
//!
//! #[derive(Debug, Clone, PartialEq)]
//! enum Status { Active(String), Inactive, Pending(u32) }
//!
//! // Create prisms for enum variants
//! let active_prism = Prism::new(
//!     |s: &Status| match s {
//!         Status::Active(name) => Some(name.clone()),
//!         _ => None,
//!     },
//!     |name: &String| Status::Active(name.clone()),
//! );
//!
//! let pending_prism = Prism::new(
//!     |s: &Status| match s {
//!         Status::Pending(days) => Some(*days),
//!         _ => None,
//!     },
//!     |days: &u32| Status::Pending(*days),
//! );
//!
//! let active_user = Status::Active("Alice".to_string());
//! let pending_user = Status::Pending(7);
//!
//! // Extract values from matching variants
//! assert_eq!(active_prism.preview(&active_user), Some("Alice".to_string()));
//! assert_eq!(active_prism.preview(&pending_user), None);
//! assert_eq!(pending_prism.preview(&pending_user), Some(7));
//!
//! // Construct enum variants
//! let new_active = active_prism.review(&"Bob".to_string());
//! assert_eq!(new_active, Status::Active("Bob".to_string()));
//!
//! // Transform specific variants
//! let updated = pending_prism.modify(pending_user, |days| days + 1);
//! assert_eq!(updated, Status::Pending(8));
//! ```
//!
//! ## Functional Programming Context
//!
//! Prisms represent a fundamental optic in functional programming, originating from the Haskell lens library.
//! They're part of a family of functional optics that includes lenses, traversals, and isos, each serving
//! a specific role in immutable data manipulation.
//!
//! Key aspects of Prisms in functional programming:
//!
//! - **Partial Function Abstraction**: Prisms encapsulate the pattern of functions that may fail
//!   when attempting to extract a value, especially useful for accessing enum variants
//!
//! - **Compositionality**: Prisms can be composed with other optics (lenses, other prisms) to create
//!   pipelines for deeply nested data access and transformation
//!
//! - **Type Safety**: Provides compile-time guarantees that operations on the extracted data
//!   will be properly type-checked
//!
//! - **Immutability-Friendly**: Operations with prisms create new data structures rather than
//!   modifying existing ones, adhering to functional programming's immutability principles
//!
//! - **Bidirectionality**: Unlike ordinary accessor functions, prisms allow both extracting and
//!   constructing data in a symmetric fashion
//!
//! Similar constructs in other functional languages include:
//!
//! - Haskell's `Prism` type from the lens library
//! - PureScript's `Prism` from the profunctor-lenses library
//! - Scala's `Prism` from the Monocle library
//! - TypeScript's `Prism` from the monocle-ts library
//!
//! ## Type Class Implementations
//!
//! `Prism` implements several important type classes and functionality:
//!
//! - **Composable**: Enables creating complex data access pipelines
//! - **Preview**: Attempts to extract a focus value from a structure
//! - **Review**: Constructs a structure from a focus value
//! - **PreviewRef**: Non-cloning variant of preview when appropriate
//! - **Modify**: Applies a function to the focus if it exists
//!
//! # Key Features
//!
//! - **Partial Focus**: Unlike lenses which always succeed, prisms may fail to extract a value
//! - **Bidirectional**: Can both extract from and construct a sum type
//! - **Composable**: Can be combined with other optics for deeper access
//! - **Non-destructive**: Original data remains unchanged
//!
//! # Common Use Cases
//!
//! - Working with specific variants of enums
//! - Safely extracting data from sum types without pattern matching everywhere
//! - Building data transformation pipelines with error handling
//! - Composition with other optics for traversing complex data structures
//!
//! # Relationship to Lenses
//!
//! While lenses focus on a part of a product type (like a struct field), prisms focus on
//! a case of a sum type (like an enum variant). Lenses always succeed in getting/setting,
//! but prisms may fail to extract a value if the wrong variant is present.
//!
//! ## Basic Usage
//!
//! The quick-start example above covers preview, review, and modification.
//! Law and boundary behavior is covered by `tests/datatypes/test_prism.rs`.
//!
//! ## Type Class Laws
//!
//! Prisms must satisfy the following laws to be considered well-behaved. See the documentation for
//! the specific functions (`preview`, `review`) for examples demonstrating these laws.
//!
//! ### First Law: Preview-Review
//!
//! For any prism `p`, structure `s`, and focus value `a` where `p.preview(s) = Some(a)`:
//!
//! `p.review(&a)` constructs a value that, when previewed, yields the same focus:
//! `p.preview(&p.review(&a)) == Some(a)`
//!
//! If the focus type `A` contains exactly the information needed to reconstruct the matched case,
//! this typically implies `p.review(&a) == s`.
//!
//! ### Second Law: Review-Preview
//!
//! For any prism `p` and focus value `a`:
//!
//! `p.preview(&p.review(&a)) == Some(a)`
//!
//! If we review a value and then successfully preview it, we get back the original value.
//!
//! # Examples
//!
//! The quick-start example demonstrates the core Prism workflow. Nested prism
//! composition and variant-specific behavior are covered by
//! `tests/datatypes/test_prism.rs`.

use crate::traits::iso::Iso;
use std::marker::PhantomData;

/// A `Prism` is an optic that allows focusing on a specific case of a sum type.
///
/// It provides a way to:
/// - Extract a value of type `A` from a structure `S` (if it exists)
/// - Construct a value of type `S` from a value of type `A`
///
/// Prisms are useful when you want to work with a specific variant of an enum
/// without having to write pattern matching code everywhere. They also enable
/// composition with other optics for more complex data transformations.
///
/// # Type Class Laws
///
/// A well-behaved Prism should satisfy these laws:
///
/// 1. **Preview-Review**: For any source `s` where `preview(s)` succeeds with value `a`,
///    `review(a)` should produce a value equivalent to `s` when viewed through the prism.
///
/// 2. **Review-Preview**: For any value `a` of the focus type,
///    `preview(review(a))` should always succeed and return `a`.
///
/// # Type Parameters
///
/// * `S` - The source type (the sum type, typically an enum)
/// * `A` - The focus type (the case we're interested in, typically a variant's content)
/// * `PreviewFn` - The function type for extracting a value (`Fn(&S) -> Option<A>`)
/// * `ReviewFn` - The function type for constructing a sum type (`Fn(&A) -> S`)
///
/// # Design Notes
///
/// - The implementation is immutable and `Clone`-able
/// - Uses PhantomData to track the type parameters
/// - The `preview` operation may fail and returns `Option<A>`
/// - The `review` operation always succeeds and returns an `S`
/// - No runtime overhead beyond function calls and potential clones
/// - Can be composed with other optics for deep traversal of data structures
///
/// # Examples
///
/// Basic usage with an enum:
///
/// ```rust
/// use rustica::datatypes::prism::Prism;
///
/// #[derive(Debug, PartialEq, Clone)]
/// enum Status {
///     Active(String),
///     Inactive,
/// }
///
/// let active_prism = Prism::new(
///     |s: &Status| match s {
///         Status::Active(name) => Some(name.clone()),
///         _ => None,
///     },
///     |name: &String| Status::Active(name.clone()),
/// );
///
/// // Usage examples
/// let active_status = Status::Active("Alice".to_string());
/// let inactive_status = Status::Inactive;
///
/// // Preview (extract)
/// assert_eq!(active_prism.preview(&active_status), Some("Alice".to_string()));
/// assert_eq!(active_prism.preview(&inactive_status), None);
///
/// // Review (construct)
/// let new_active = active_prism.review(&"Bob".to_string());
/// assert!(matches!(new_active, Status::Active(name) if name == "Bob"));
/// ```
///
/// Complex variant extraction and nested composition are covered by
/// `tests/datatypes/test_prism.rs`.
#[derive(Clone, Debug, PartialEq)]
pub struct Prism<S, A, PreviewFn, ReviewFn>
where
    PreviewFn: Fn(&S) -> Option<A>,
    ReviewFn: Fn(&A) -> S,
{
    /// Function that attempts to extract a value of type A from S
    preview: PreviewFn,
    /// Function that constructs a value of type S from A
    review: ReviewFn,
    _phantom: PhantomData<(S, A)>,
}

impl<S, A, PreviewFn, ReviewFn> Prism<S, A, PreviewFn, ReviewFn>
where
    PreviewFn: Fn(&S) -> Option<A>,
    ReviewFn: Fn(&A) -> S,
{
    /// Creates a new Prism with the given preview and review functions.
    ///
    /// The `preview` function attempts to extract a value of type `A` from `S`,
    /// returning `None` if the extraction fails (e.g., if `S` is not the variant
    /// we're interested in).
    ///
    /// The `review` function constructs a value of type `S` from a value of type `A`.
    ///
    /// # Implementation Notes
    ///
    /// For a well-behaved prism, the provided functions should satisfy these conditions:
    ///
    /// 1. If `preview(s)` returns `Some(a)`, then `preview(review(a))` should also return `Some(a)`.
    /// 2. If `preview(s)` returns `Some(a)`, the result of `review(a)` when viewed through the
    ///    prism should be equivalent to the original `s`.
    ///
    /// Typical implementations use pattern matching in the preview function to extract
    /// data from a specific enum variant, and construct that variant in the review function.
    ///
    /// # Arguments
    ///
    /// * `preview` - A function that attempts to extract a value of type A from S
    /// * `review` - A function that constructs a value of type S from A
    ///
    /// # Type Parameters
    ///
    /// * `PreviewFn` - Type of the preview function: `Fn(&S) -> Option<A>`
    /// * `ReviewFn` - Type of the review function: `Fn(&A) -> S`
    ///
    /// # Examples
    ///
    /// Basic prism for an enum variant:
    ///
    /// ```rust
    /// use rustica::datatypes::prism::Prism;
    ///
    /// #[derive(Debug, Clone, PartialEq)]
    /// enum Result<T, E> {
    ///     Ok(T),
    ///     Err(E),
    /// }
    ///
    /// // Create a prism for the Ok variant
    /// let ok_prism = Prism::new(
    ///     |r: &Result<i32, String>| match r {
    ///         Result::Ok(v) => Some(*v),
    ///         Result::Err(_) => None,
    ///     },
    ///     |v: &i32| Result::Ok(*v),
    /// );
    /// ```
    pub fn new(preview: PreviewFn, review: ReviewFn) -> Self {
        Prism {
            preview,
            review,
            _phantom: PhantomData,
        }
    }

    /// Attempts to extract a value of type A from S.
    ///
    /// This operation is the "get" part of the prism. It attempts to extract
    /// a value of type `A` from `S`, returning `None` if the extraction fails
    /// (e.g., if `S` is not the variant we're interested in).
    ///
    /// # Design Notes
    ///
    /// * This is a non-destructive operation - it doesn't modify the source value
    /// * For enum variants with large data structures, consider minimizing unnecessary clones
    ///   in your preview function
    /// * Often used in combination with `Option` or with pattern matching to
    ///   handle both the success and failure cases
    ///
    /// # Arguments
    ///
    /// * `s` - The source value to extract from
    ///
    /// # Returns
    ///
    /// * `Some(A)` if the extraction was successful
    /// * `None` if the source value doesn't match the case we're interested in
    ///
    /// # Examples
    ///
    /// Basic usage with enum variants:
    ///
    /// ```rust
    /// use rustica::datatypes::prism::Prism;
    ///
    /// #[derive(Debug, Clone, PartialEq)]
    /// enum Message {
    ///     Text(String),
    ///     Binary(Vec<u8>),
    /// }
    ///
    /// let text_prism = Prism::new(
    ///     |m: &Message| match m {
    ///         Message::Text(t) => Some(t.clone()),
    ///         _ => None,
    ///     },
    ///     |t: &String| Message::Text(t.clone()),
    /// );
    ///
    /// let text_msg = Message::Text("Hello".to_string());
    /// let binary_msg = Message::Binary(vec![1, 2, 3]);
    ///
    /// assert_eq!(text_prism.preview(&text_msg), Some("Hello".to_string()));
    /// assert_eq!(text_prism.preview(&binary_msg), None);
    /// ```
    pub fn preview(&self, s: &S) -> Option<A> {
        (self.preview)(s)
    }

    /// Constructs a value of type S from A.
    ///
    /// This operation is the "set" part of the prism. It constructs a value
    /// of type `S` from a value of type `A`. Unlike `preview`, this operation
    /// always succeeds.
    ///
    /// # Design Notes
    ///
    /// * This is a pure operation that doesn't modify the input value
    /// * For a well-behaved prism, `preview(review(a))` should always return `Some(a)`
    /// * Use this to create a value of the sum type when you know exactly which variant
    ///   you want to create
    /// * Often used in mapping operations and transformations between data types
    ///
    /// # Arguments
    ///
    /// * `a` - The value to construct from
    ///
    /// # Returns
    ///
    /// A value of type S constructed from the given A
    ///
    /// # Examples
    ///
    /// Basic usage:
    ///
    /// ```rust
    /// use rustica::datatypes::prism::Prism;
    ///
    /// #[derive(Debug, Clone, PartialEq)]
    /// enum Message {
    ///     Text(String),
    ///     Binary(Vec<u8>),
    /// }
    ///
    /// let text_prism = Prism::new(
    ///     |m: &Message| match m {
    ///         Message::Text(t) => Some(t.clone()),
    ///         _ => None,
    ///     },
    ///     |t: &String| Message::Text(t.clone()),
    /// );
    ///
    /// let msg = text_prism.review(&"Hello, world!".to_string());
    /// assert!(matches!(msg, Message::Text(t) if t == "Hello, world!"));
    /// ```
    pub fn review(&self, a: &A) -> S {
        (self.review)(a)
    }

    /// Creates a Prism for a specific case of a sum type.
    /// This is a convenience method that is equivalent to calling `new`.
    ///
    /// This method is provided as a more semantically clear alternative to `new`
    /// when working specifically with enum variants. It has identical performance
    /// characteristics to the `new` method.
    ///
    /// # Design Notes
    ///
    /// * This method exists purely for semantic clarity
    /// * Use this when you specifically want to emphasize that you're creating a prism
    ///   for an enum variant
    /// * Functionally identical to `new` but with a more domain-specific name
    /// * The explicit type parameters can help with type inference in complex scenarios
    ///
    /// # Arguments
    ///
    /// * `match_case` - A function that matches and extracts the case we're interested in
    /// * `make_case` - A function that constructs the sum type from our case
    ///
    /// # Type Parameters
    ///
    /// * `P` - The sum type (often inferred)
    /// * `R` - The focus type (often inferred)
    /// * `PreviewFn` - Type of the preview function: `Fn(&S) -> Option<A>`
    /// * `ReviewFn` - Type of the review function: `Fn(&A) -> S`
    ///
    /// # Examples
    ///
    /// Creating prisms for different enum variants:
    ///
    /// ```rust
    /// use rustica::datatypes::prism::Prism;
    ///
    /// #[derive(Debug, Clone, PartialEq)]
    /// enum Shape {
    ///     Circle(f64),  // radius
    ///     Rectangle(f64, f64),  // width, height
    ///     Triangle(f64, f64, f64),  // sides
    /// }
    ///
    /// // Create prisms for each variant
    /// let circle_prism = Prism::for_case::<Shape, f64>(
    ///     |s: &Shape| match s {
    ///         Shape::Circle(r) => Some(*r),
    ///         _ => None,
    ///     },
    ///     |r: &f64| Shape::Circle(*r),
    /// );
    ///
    /// // Test shapes
    /// let circle = Shape::Circle(5.0);
    /// let rect = Shape::Rectangle(4.0, 3.0);
    ///
    /// // Circle prism works only on circles
    /// assert_eq!(circle_prism.preview(&circle), Some(5.0));
    /// assert_eq!(circle_prism.preview(&rect), None);
    /// ```
    pub fn for_case<P, R>(match_case: PreviewFn, make_case: ReviewFn) -> Self {
        Prism::new(match_case, make_case)
    }

    /// Modifies the focused value using a transformation function with structural sharing optimization.
    ///
    /// This method applies a transformation function to the focused value (if it exists) and
    /// returns a new structure. If the transformation doesn't change the value, the original
    /// structure is returned unchanged, providing structural sharing optimization.
    ///
    /// # Structural Sharing Benefits
    ///
    /// This method provides significant performance benefits when:
    /// - The transformation function often returns the same value
    /// - The structure S is large and expensive to clone/construct
    /// - Memory pressure is a concern in your application
    ///
    /// # Design Notes
    ///
    /// * Requires `A: PartialEq` to compare values for structural sharing
    /// * If preview fails, the original structure is returned unchanged
    /// * The transformation function is called only when preview succeeds
    ///
    /// # Arguments
    ///
    /// * `source` - The source structure to modify
    /// * `f` - A transformation function that takes the current value and returns a new value
    ///
    /// # Returns
    ///
    /// * The original structure if preview fails or the value is unchanged after transformation
    /// * A new structure if the value was successfully transformed to a different value
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::prism::Prism;
    ///
    /// #[derive(Debug, Clone, PartialEq)]
    /// enum Counter {
    ///     Value(i32),
    ///     Empty,
    /// }
    ///
    /// let value_prism = Prism::new(
    ///     |c: &Counter| match c {
    ///         Counter::Value(v) => Some(*v),
    ///         _ => None,
    ///     },
    ///     |v: &i32| Counter::Value(*v),
    /// );
    ///
    /// let counter = Counter::Value(5);
    ///
    /// // Increment the value
    /// let incremented = value_prism.modify(counter.clone(), |x| x + 1);
    /// assert_eq!(incremented, Counter::Value(6));
    ///
    /// // No change - structural sharing applied
    /// let unchanged = value_prism.modify(counter.clone(), |x| x);
    /// // unchanged is the original structure returned without reconstruction
    ///
    /// // Preview fails - original structure returned
    /// let empty = Counter::Empty;
    /// let still_empty = value_prism.modify(empty, |x| x + 1);
    /// assert_eq!(still_empty, Counter::Empty);
    /// ```
    pub fn modify<F>(&self, source: S, f: F) -> S
    where
        F: FnOnce(A) -> A,
        A: PartialEq + Clone,
    {
        match self.preview(&source) {
            Some(current_value) => {
                let new_value = f(current_value.clone());
                if new_value == current_value {
                    source // Return original structure (structural sharing)
                } else {
                    self.review(&new_value) // Create new structure
                }
            },
            None => source, // Preview failed, return original structure
        }
    }

    /// Composes two prisms to create a new prism that focuses on nested sum types.
    ///
    /// Given a prism from `S` to `A` and a prism from `A` to `B`, this creates a new
    /// prism from `S` to `B`. This is essential for accessing deeply nested enum
    /// variants in a type-safe and composable way.
    ///
    /// # Type Parameters
    ///
    /// * `B` - The type of the deeply nested focus
    /// * `PreviewFn2` - The type of the inner prism preview function
    /// * `ReviewFn2` - The type of the inner prism review function
    ///
    /// # Arguments
    ///
    /// * `other` - The inner prism that focuses from `A` to `B`
    ///
    /// # Returns
    ///
    /// A new prism that focuses from `S` directly to `B`
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::prism::Prism;
    ///
    /// #[derive(Debug, Clone, PartialEq)]
    /// enum Inner { Value(i32), Empty }
    ///
    /// #[derive(Debug, Clone, PartialEq)]
    /// enum Outer { Nested(Inner), Other(String) }
    ///
    /// let nested_prism = Prism::new(
    ///     |o: &Outer| match o {
    ///         Outer::Nested(inner) => Some(inner.clone()),
    ///         _ => None,
    ///     },
    ///     |i: &Inner| Outer::Nested(i.clone()),
    /// );
    ///
    /// let value_prism = Prism::new(
    ///     |i: &Inner| match i {
    ///         Inner::Value(v) => Some(*v),
    ///         _ => None,
    ///     },
    ///     |v: &i32| Inner::Value(*v),
    /// );
    ///
    /// // Chain to create a prism from Outer to i32
    /// let deep_prism = nested_prism.then(value_prism);
    ///
    /// let data = Outer::Nested(Inner::Value(42));
    /// assert_eq!(deep_prism.preview(&data), Some(42));
    ///
    /// let constructed = deep_prism.review(&100);
    /// assert_eq!(constructed, Outer::Nested(Inner::Value(100)));
    /// ```
    #[inline]
    pub fn then<B, PreviewFn2, ReviewFn2>(
        self, other: Prism<A, B, PreviewFn2, ReviewFn2>,
    ) -> Prism<S, B, impl Fn(&S) -> Option<B>, impl Fn(&B) -> S>
    where
        A: Clone,
        B: Clone,
        PreviewFn2: Fn(&A) -> Option<B>,
        ReviewFn2: Fn(&B) -> A,
    {
        let preview1 = self.preview;
        let review1 = self.review;
        let preview2 = other.preview;
        let review2 = other.review;

        Prism::new(
            move |s: &S| preview1(s).and_then(|a| preview2(&a)),
            move |b: &B| review1(&review2(b)),
        )
    }

    /// Sets the focused value with structural sharing optimization.
    ///
    /// This method sets the focused value to a new value, but only creates a new structure
    /// if the new value is different from the current value. If the values are equal,
    /// the original structure is returned unchanged.
    ///
    /// # Design Notes
    ///
    /// * If preview fails, a new structure is created with the given value
    /// * This behavior ensures that the method always succeeds in "setting" the value
    /// * The method assumes that if preview fails, you want to create the variant
    ///
    /// # Arguments
    ///
    /// * `source` - The source structure to potentially modify
    /// * `new_value` - The new value to set
    ///
    /// # Returns
    ///
    /// * The original structure if the current value equals the new value
    /// * A new structure with the new value if they differ or if preview fails
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::prism::Prism;
    ///
    /// #[derive(Debug, Clone, PartialEq)]
    /// enum Status {
    ///     Active(String),
    ///     Inactive,
    /// }
    ///
    /// let active_prism = Prism::new(
    ///     |s: &Status| match s {
    ///         Status::Active(name) => Some(name.clone()),
    ///         _ => None,
    ///     },
    ///     |name: &String| Status::Active(name.clone()),
    /// );
    ///
    /// let status = Status::Active("Alice".to_string());
    ///
    /// // Set to same value - structural sharing
    /// let same_status = active_prism.set_if_different(status.clone(), "Alice".to_string());
    /// // same_status is the original structure returned without reconstruction
    ///
    /// // Set to different value - new structure created
    /// let new_status = active_prism.set_if_different(status, "Bob".to_string());
    /// assert_eq!(new_status, Status::Active("Bob".to_string()));
    ///
    /// // Preview fails - create new structure
    /// let inactive = Status::Inactive;
    /// let now_active = active_prism.set_if_different(inactive, "Charlie".to_string());
    /// assert_eq!(now_active, Status::Active("Charlie".to_string()));
    /// ```
    pub fn set_if_different(&self, source: S, new_value: A) -> S
    where
        A: PartialEq,
    {
        match self.preview(&source) {
            Some(current_value) => {
                if new_value == current_value {
                    source // Return original structure (structural sharing)
                } else {
                    self.review(&new_value) // Create new structure
                }
            },
            None => self.review(&new_value), // Preview failed, create new structure with the value
        }
    }
}

impl<S, A> Prism<S, A, fn(&S) -> Option<A>, fn(&A) -> S> {
    /// Creates a prism induced by an isomorphism.
    ///
    /// An isomorphism always previews successfully: `forward` becomes
    /// `preview`, while `backward` becomes `review`.
    #[inline]
    pub fn from_iso<I>(iso: I) -> Prism<S, A, impl Fn(&S) -> Option<A>, impl Fn(&A) -> S>
    where
        I: Iso<S, A, From = S, To = A>,
    {
        let iso = std::sync::Arc::new(iso);
        let preview_iso = std::sync::Arc::clone(&iso);
        Prism::new(
            move |source: &S| Some(preview_iso.forward(source)),
            move |focus: &A| iso.backward(focus),
        )
    }
}

#[cfg(test)]
mod unit_tests {
    use super::Prism;
    use crate::datatypes::lens::Lens;
    use std::collections::HashMap;

    #[derive(Clone, Debug, PartialEq)]
    enum Status {
        Active(String),
        Inactive,
        Error { code: u32, message: String },
    }
    type ActivePrism = Prism<
        Status,
        String,
        Box<dyn Fn(&Status) -> Option<String>>,
        Box<dyn Fn(&String) -> Status>,
    >;
    fn active_prism() -> ActivePrism {
        Prism::new(
            Box::new(|s| match s {
                Status::Active(name) => Some(name.clone()),
                _ => None,
            }),
            Box::new(|name| Status::Active(name.clone())),
        )
    }
    type ErrorPrism = Prism<
        Status,
        (u32, String),
        Box<dyn Fn(&Status) -> Option<(u32, String)>>,
        Box<dyn Fn(&(u32, String)) -> Status>,
    >;
    fn error_prism() -> ErrorPrism {
        Prism::new(
            Box::new(|s| match s {
                Status::Error { code, message } => Some((*code, message.clone())),
                _ => None,
            }),
            Box::new(|value| Status::Error {
                code: value.0,
                message: value.1.clone(),
            }),
        )
    }

    #[test]
    fn preview_review_and_modify_obey_prism_contracts() {
        let prism = active_prism();
        let target = Status::Active("Alice".into());
        assert_eq!(prism.preview(&target), Some("Alice".into()));
        assert_eq!(prism.preview(&Status::Inactive), None);
        assert_eq!(prism.review(&"Bob".into()), Status::Active("Bob".into()));
        assert_eq!(
            prism.preview(&prism.review(&"LawCheck".into())),
            Some("LawCheck".into())
        );

        let error = Status::Error {
            code: 500,
            message: "Fail".into(),
        };
        assert_eq!(
            error_prism().modify(error.clone(), |(code, message)| (
                code + 1,
                format!("{message}-fixed")
            )),
            Status::Error {
                code: 501,
                message: "Fail-fixed".into()
            }
        );
        assert_eq!(
            active_prism().modify(Status::Inactive, |_| "ignored".into()),
            Status::Inactive
        );
        assert_eq!(
            error_prism().set_if_different(error, (200, "OK".into())),
            Status::Error {
                code: 200,
                message: "OK".into()
            }
        );
    }

    #[derive(Clone, Copy)]
    struct IdentityIso;

    impl crate::traits::iso::Iso<i32, i32> for IdentityIso {
        type From = i32;
        type To = i32;

        fn forward(&self, from: &Self::From) -> Self::To {
            *from
        }

        fn backward(&self, to: &Self::To) -> Self::From {
            *to
        }
    }

    #[test]
    fn from_iso_induces_a_prism() {
        let prism = Prism::from_iso(IdentityIso);

        assert_eq!(prism.preview(&42), Some(42));
        assert_eq!(prism.review(&7), 7);
    }

    #[test]
    fn complex_extraction_and_composition_work() {
        #[derive(Debug, Clone, PartialEq)]
        enum ConfigValue {
            Integer(i64),
            String(String),
            Dictionary(HashMap<String, ConfigValue>),
        }
        let dict = Prism::new(
            |value: &ConfigValue| match value {
                ConfigValue::Dictionary(map) => Some(map.clone()),
                _ => None,
            },
            |map: &HashMap<String, ConfigValue>| ConfigValue::Dictionary(map.clone()),
        );
        let mut values = HashMap::new();
        values.insert("name".into(), ConfigValue::String("Alice".into()));
        values.insert("age".into(), ConfigValue::Integer(30));
        let mut updated_values = values.clone();
        updated_values.insert("theme".into(), ConfigValue::String("dark".into()));
        let updated = dict.review(&updated_values);
        let new_values = dict.preview(&updated).unwrap();
        assert_eq!(new_values.len(), 3);
        assert!(new_values.contains_key("theme"));

        #[derive(Debug, Clone, PartialEq)]
        enum Inner {
            Val(i32),
            Empty,
        }
        #[derive(Debug, Clone, PartialEq)]
        enum Outer {
            Nested(Inner),
            Other,
        }
        let outer = Prism::new(
            |value: &Outer| match value {
                Outer::Nested(inner) => Some(inner.clone()),
                _ => None,
            },
            |inner: &Inner| Outer::Nested(inner.clone()),
        );
        let inner = Prism::new(
            |value: &Inner| match value {
                Inner::Val(value) => Some(*value),
                Inner::Empty => None,
            },
            |value: &i32| Inner::Val(*value),
        );
        let deep = outer.then(inner);
        assert_eq!(deep.preview(&Outer::Nested(Inner::Val(42))), Some(42));
        assert_eq!(deep.review(&100), Outer::Nested(Inner::Val(100)));
        assert_eq!(deep.preview(&Outer::Nested(Inner::Empty)), None);
        assert_eq!(deep.preview(&Outer::Other), None);

        #[derive(Clone, Debug, PartialEq)]
        struct User {
            id: u64,
            status: Status,
        }
        let status = Lens::new(
            |u: &User| u.status.clone(),
            |u, status| User { status, ..u },
        );
        let user = User {
            id: 1,
            status: Status::Active("online".into()),
        };
        let updated = status.modify(user, |value| {
            active_prism().modify(value, |name| format!("{name}-away"))
        });
        assert_eq!(updated.status, Status::Active("online-away".into()));
    }
}
