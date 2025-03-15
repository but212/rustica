//! Prisms are optics that focus on a specific case of a sum type.
//!
//! A prism provides a way to:
//! - Selectively view a specific variant of an enum (sum type)
//! - Construct a value of the sum type from a value of the specific variant
//!
//! # Key Features
//!
//! - **Partial Focus**: Unlike lenses which always succeed, prisms may fail to extract a value
//! - **Bidirectional**: Can both extract from and construct a sum type
//! - **Composable**: Can be combined with other optics for deeper access
//!
//! # Common Use Cases
//!
//! - Working with specific variants of enums
//! - Safely extracting data from sum types without pattern matching everywhere
//! - Building data transformation pipelines with error handling
//!
//! # Relationship to Lenses
//!
//! While lenses focus on a part of a product type (like a struct field), prisms focus on
//! a case of a sum type (like an enum variant). Lenses always succeed in getting/setting,
//! but prisms may fail to extract a value if the wrong variant is present.
//!
//! # Examples
//!
//! ```rust
//! use rustica::datatypes::prism::Prism;
//! use rustica::datatypes::maybe::Maybe;
//!
//! // Define a sum type
//! #[derive(Debug, PartialEq, Clone)]
//! enum UserStatus {
//!     LoggedIn { username: String, session_id: String },
//!     LoggedOut,
//!     Suspended { reason: String },
//! }
//!
//! // Create a prism for the LoggedIn variant
//! let logged_in_prism = Prism::new(
//!     |status: &UserStatus| match status {
//!         UserStatus::LoggedIn { username, session_id } => Some((username.clone(), session_id.clone())),
//!         _ => None,
//!     },
//!     |&(ref username, ref session_id)| UserStatus::LoggedIn {
//!         username: username.clone(),
//!         session_id: session_id.clone(),
//!     },
//! );
//!
//! // Use the prism to extract data
//! let user = UserStatus::LoggedIn {
//!     username: "alice".to_string(),
//!     session_id: "abc123".to_string(),
//! };
//!
//! let suspended = UserStatus::Suspended {
//!     reason: "Violation of terms".to_string(),
//! };
//!
//! // Preview succeeds for LoggedIn
//! let data = logged_in_prism.preview(&user);
//! assert_eq!(data, Some(("alice".to_string(), "abc123".to_string())));
//!
//! // Preview fails for other variants
//! let no_data = logged_in_prism.preview(&suspended);
//! assert_eq!(no_data, None);
//!
//! // Create a new LoggedIn user
//! let new_user = logged_in_prism.review(&("bob".to_string(), "xyz789".to_string()));
//! assert_eq!(new_user, UserStatus::LoggedIn {
//!     username: "bob".to_string(),
//!     session_id: "xyz789".to_string(),
//! });
//! ```

use std::marker::PhantomData;
use std::sync::Arc;

/// Type alias for a function that previews a value
pub type PreviewFn<S, A> = Arc<dyn Fn(&S) -> Option<A> + 'static>;

/// Type alias for a function that reviews a value
pub type ReviewFn<S, A> = Arc<dyn Fn(&A) -> S + 'static>;

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
/// # Type Parameters
///
/// * `S` - The source type (the sum type)
/// * `A` - The focus type (the case we're interested in)
///
/// # Design Notes
///
/// - Uses `Arc` to make the prism `Clone` and thread-safe
/// - Consists of two functions: `preview` for extraction and `review` for construction
/// - `preview` may fail and returns an `Option<A>`
/// - `review` always succeeds and returns an `S`
///
/// # Examples
///
/// ```rust
/// use rustica::datatypes::prism::Prism;
///
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
#[derive(Clone)]
pub struct Prism<S, A> {
    /// Function that attempts to extract a value of type A from S
    preview: PreviewFn<S, A>,
    /// Function that constructs a value of type S from A
    review: ReviewFn<S, A>,
    phantom: PhantomData<(S, A)>,
}

impl<S, A> Prism<S, A> {
    /// Creates a new Prism with the given preview and review functions.
    ///
    /// The `preview` function attempts to extract a value of type `A` from `S`,
    /// returning `None` if the extraction fails (e.g., if `S` is not the variant
    /// we're interested in).
    ///
    /// The `review` function constructs a value of type `S` from a value of type `A`.
    ///
    /// # Arguments
    ///
    /// * `preview` - A function that attempts to extract a value of type A from S
    /// * `review` - A function that constructs a value of type S from A
    ///
    /// # Type Parameters
    ///
    /// * `P` - Type of the preview function
    /// * `R` - Type of the review function
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::prism::Prism;
    ///
    /// // Define an enum
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
    pub fn new<P, R>(preview: P, review: R) -> Self
    where
        P: Fn(&S) -> Option<A> + 'static,
        R: Fn(&A) -> S + 'static,
    {
        Prism {
            preview: Arc::new(preview),
            review: Arc::new(review),
            phantom: PhantomData,
        }
    }

    /// Attempts to extract a value of type A from S.
    ///
    /// This operation is the "get" part of the prism. It attempts to extract
    /// a value of type `A` from `S`, returning `None` if the extraction fails
    /// (e.g., if `S` is not the variant we're interested in).
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
    /// ```rust
    /// use rustica::datatypes::prism::Prism;
    ///
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
    /// ```rust
    /// use rustica::datatypes::prism::Prism;
    ///
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
    /// when working specifically with enum variants.
    ///
    /// # Arguments
    ///
    /// * `match_case` - A function that matches and extracts the case we're interested in
    /// * `make_case` - A function that constructs the sum type from our case
    ///
    /// # Type Parameters
    ///
    /// * `F` - Type of the match function
    /// * `G` - Type of the make function
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::prism::Prism;
    ///
    /// enum Shape {
    ///     Circle(f64),  // radius
    ///     Rectangle(f64, f64),  // width, height
    ///     Triangle(f64, f64, f64),  // sides
    /// }
    ///
    /// // Create a prism for the Circle variant
    /// let circle_prism = Prism::for_case(
    ///     |s: &Shape| match s {
    ///         Shape::Circle(r) => Some(*r),
    ///         _ => None,
    ///     },
    ///     |r: &f64| Shape::Circle(*r),
    /// );
    ///
    /// let circle = Shape::Circle(5.0);
    /// let rect = Shape::Rectangle(4.0, 3.0);
    ///
    /// assert_eq!(circle_prism.preview(&circle), Some(5.0));
    /// assert_eq!(circle_prism.preview(&rect), None);
    /// ```
    pub fn for_case<F, G>(match_case: F, make_case: G) -> Self
    where
        F: Fn(&S) -> Option<A> + 'static,
        G: Fn(&A) -> S + 'static,
    {
        Prism::new(match_case, make_case)
    }
}
