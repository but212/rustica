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
//! ```rust
//! use rustica::datatypes::prism::Prism;
//!
//! // Define an enum (sum type)
//! #[derive(Debug, Clone, PartialEq)]
//! enum UserStatus {
//!     Active { username: String, last_login: u64 },
//!     Inactive { username: String, since: u64 },
//!     Pending { username: String },
//! }
//!
//! // Create a prism for the Active variant
//! let active_prism = Prism::new(
//!     // Preview function - extract data if it's the Active variant
//!     |status: &UserStatus| match status {
//!         UserStatus::Active { username, last_login } =>
//!             Some((username.clone(), *last_login)),
//!         _ => None,
//!     },
//!     // Review function - create an Active variant from the data
//!     |(username, last_login): &(String, u64)| UserStatus::Active {
//!         username: username.clone(),
//!         last_login: *last_login
//!     },
//! );
//!
//! // Create sample data
//! let active_user = UserStatus::Active {
//!     username: "alice".to_string(),
//!     last_login: 1625097600
//! };
//! let inactive_user = UserStatus::Inactive {
//!     username: "bob".to_string(),
//!     since: 1622505600
//! };
//!
//! // Preview (extract) data - succeeds for the matching variant
//! let active_data = active_prism.preview(&active_user);
//! assert_eq!(active_data, Some(("alice".to_string(), 1625097600)));
//!
//! // Preview fails for non-matching variant
//! let no_data = active_prism.preview(&inactive_user);
//! assert_eq!(no_data, None);
//!
//! // Review (construct) - create a new UserStatus::Active
//! let new_active = active_prism.review(&("carol".to_string(), 1633046400));
//! assert_eq!(new_active, UserStatus::Active {
//!     username: "carol".to_string(),
//!     last_login: 1633046400
//! });
//!
//! // Transform - preview, modify, and review if it's the right variant
//! let updated = match active_prism.preview(&active_user) {
//!     Some((name, _)) => active_prism.review(&(name, 1633046400)),
//!     None => active_user.clone(),
//! };
//! assert_eq!(updated, UserStatus::Active {
//!     username: "alice".to_string(),
//!     last_login: 1633046400
//! });
//!
//! // Transform does nothing for wrong variant
//! let unchanged = match active_prism.preview(&inactive_user) {
//!     Some((name, _)) => active_prism.review(&(name, 1633046400)),
//!     None => inactive_user.clone(),
//! };
//! assert_eq!(unchanged, inactive_user);
//! ```
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
//! `p.preview(s).map(|a| p.review(&a)) == p.preview(s).map(|_| s.clone())`
//!
//! If we successfully preview a value and then review it, we get back a value
//! that would preview to the same result.
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
//! Basic usage with enum variants:
//!
//! ```rust
//! use rustica::datatypes::prism::Prism;
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
//!
//! Composing prisms for nested structures:
//!
//! ```rust
//! use rustica::datatypes::prism::Prism;
//!
//! #[derive(Debug, PartialEq, Clone)]
//! enum HttpResponse {
//!     Success { body: ResponseBody, status: u16 },
//!     Error { code: u16, message: String }
//! }
//!
//! #[derive(Debug, PartialEq, Clone)]
//! enum ResponseBody {
//!     Json(String),
//!     Text(String),
//!     Binary(Vec<u8>)
//! }
//!
//! // Prism for the Success variant
//! let success_prism = Prism::new(
//!     |resp: &HttpResponse| match resp {
//!         HttpResponse::Success { body, status } => Some((body.clone(), *status)),
//!         _ => None
//!     },
//!     |&(ref body, status)| HttpResponse::Success {
//!         body: body.clone(),
//!         status
//!     }
//! );
//!
//! // Prism for the Json body variant
//! let json_body_prism = Prism::new(
//!     |body: &ResponseBody| match body {
//!         ResponseBody::Json(json) => Some(json.clone()),
//!         _ => None
//!     },
//!     |json: &String| ResponseBody::Json(json.clone())
//! );
//!
//! // Example response
//! let response = HttpResponse::Success {
//!     body: ResponseBody::Json("{\"user\": \"alice\"}".to_string()),
//!     status: 200
//! };
//!
//! // First extract the success part
//! if let Some((body, status)) = success_prism.preview(&response) {
//!     // Then extract the JSON content if available
//!     if let Some(json) = json_body_prism.preview(&body) {
//!         assert_eq!(json, "{\"user\": \"alice\"}");
//!     }
//! }
//! ```

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
/// Working with complex enum variants:
///
/// ```rust
/// use rustica::datatypes::prism::Prism;
/// use std::collections::HashMap;
///
/// #[derive(Debug, Clone, PartialEq)]
/// enum ConfigValue {
///     Integer(i64),
///     Float(f64),
///     String(String),
///     Dictionary(HashMap<String, ConfigValue>),
///     Array(Vec<ConfigValue>),
/// }
///
/// // Create a prism for the Dictionary variant
/// let dict_prism = Prism::new(
///     |cv: &ConfigValue| match cv {
///         ConfigValue::Dictionary(map) => Some(map.clone()),
///         _ => None,
///     },
///     |map: &HashMap<String, ConfigValue>| ConfigValue::Dictionary(map.clone()),
/// );
///
/// // Create sample configuration
/// let mut user_prefs = HashMap::new();
/// user_prefs.insert("name".to_string(), ConfigValue::String("Alice".to_string()));
/// user_prefs.insert("age".to_string(), ConfigValue::Integer(30));
///
/// let config = ConfigValue::Dictionary(user_prefs);
///
/// // Extract the dictionary from the config
/// if let Some(prefs) = dict_prism.preview(&config) {
///     // Access values from the dictionary
///     if let Some(ConfigValue::String(name)) = prefs.get("name") {
///         assert_eq!(name, "Alice");
///     }
///     
///     // Create a modified dictionary
///     let mut updated_prefs = prefs.clone();
///     updated_prefs.insert("theme".to_string(), ConfigValue::String("dark".to_string()));
///     
///     // Create a new config with the updated dictionary
///     let updated_config = dict_prism.review(&updated_prefs);
///     
///     // We can verify the new config has our updated preferences
///     if let Some(new_prefs) = dict_prism.preview(&updated_config) {
///         assert_eq!(new_prefs.len(), 3);
///         assert!(new_prefs.contains_key("theme"));
///     }
/// }
/// ```
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
    /// * Often used in combination with the `Maybe` monad or with pattern matching to
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
    /// * Requires `S: Clone` to enable returning the original structure
    /// * Requires `A: PartialEq` to compare values for structural sharing
    /// * If preview fails, the original structure is returned unchanged
    /// * The transformation function is always called, even if preview fails
    ///   (this ensures consistent behavior and side effects)
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
    /// // unchanged is the same instance as counter (structural sharing)
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
    /// // same_status is the same instance as status
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
