//! Lens is a functional programming concept for accessing and modifying parts of immutable data structures.
//! 
//! A lens provides a way to:
//! - View a part of a larger data structure
//! - Update that part while preserving the rest of the structure
//! - Transform the focused part using functions
//! 
//! # Key Features
//! 
//! - **Immutable Updates**: All operations create new instances instead of modifying in place
//! - **Composable**: Lenses can be combined to focus on nested structures
//! - **Type-safe**: The compiler ensures that updates maintain type consistency
//! 
//! # Common Use Cases
//! 
//! - Accessing and updating nested fields in complex data structures
//! - Modifying specific elements in collections
//! - Creating reusable accessors for data structures
//! 
//! # Examples
//! 
//! ```rust
//! use rustica::datatypes::lens::Lens;
//! 
//! // A nested data structure
//! #[derive(Clone)]
//! struct Address {
//!     street: String,
//!     city: String,
//! }
//! 
//! #[derive(Clone)]
//! struct Person {
//!     name: String,
//!     address: Address,
//! }
//! 
//! // Create lenses for accessing nested fields
//! let address_lens = Lens::new(
//!     |p: &Person| p.address.clone(),
//!     |p: Person, addr: Address| Person { address: addr, ..p },
//! );
//! 
//! let street_lens = Lens::new(
//!     |a: &Address| a.street.clone(),
//!     |a: Address, s: String| Address { street: s, ..a },
//! );
//! 
//! // Create initial data
//! let person = Person {
//!     name: "Alice".to_string(),
//!     address: Address {
//!         street: "123 Main St".to_string(),
//!         city: "Springfield".to_string(),
//!     },
//! };
//! 
//! // Update nested field
//! let updated = address_lens.modify(person.clone(), |addr| {
//!     street_lens.set(addr, "456 Oak Ave".to_string())
//! });
//! 
//! assert_eq!(updated.address.street, "456 Oak Ave");
//! assert_eq!(updated.address.city, "Springfield");
//! ```

use std::sync::Arc;

/// A lens is a first-class reference to a subpart of some data type.
/// It provides a way to view, modify and transform a part of a larger structure.
/// 
/// # Type Parameters
/// 
/// * `S` - The type of the whole structure
/// * `A` - The type of the part being focused on
/// 
/// # Design Notes
/// 
/// - Uses `Arc` to make the lens `Clone` and thread-safe
/// - Requires both the structure and focused part to be `Clone`
/// - Functions are stored as trait objects to allow for different implementations
/// 
/// # Examples
/// 
/// ```rust
/// use rustica::datatypes::lens::Lens;
/// 
/// #[derive(Clone)]
/// struct Person {
///     name: String,
///     age: u32,
/// }
/// 
/// // Create a lens focusing on the name field
/// let name_lens = Lens::new(
///     |p: &Person| p.name.clone(),
///     |p: Person, name: String| Person { name, ..p },
/// );
/// 
/// let person = Person {
///     name: "Alice".to_string(),
///     age: 30,
/// };
/// 
/// // Get the name
/// assert_eq!(name_lens.get(&person), "Alice");
/// 
/// // Update the name
/// let updated = name_lens.set(person.clone(), "Bob".to_string());
/// assert_eq!(updated.name, "Bob");
/// assert_eq!(updated.age, 30);
/// 
/// // Modify the name
/// let modified = name_lens.modify(person, |name| format!("Ms. {}", name));
/// assert_eq!(modified.name, "Ms. Alice");
/// ```
#[derive(Clone)]
pub struct Lens<S: Clone + 'static, A: Clone + 'static> {
    get: Arc<dyn Fn(&S) -> A + 'static>,
    set: Arc<dyn Fn(S, A) -> S + 'static>,
}

impl<S: Clone + 'static, A: Clone + 'static> Lens<S, A> {
    /// Creates a new lens from getter and setter functions.
    /// 
    /// # Arguments
    /// 
    /// * `get` - A function that extracts a part from the whole structure
    /// * `set` - A function that updates the whole structure with a new part
    /// 
    /// # Type Parameters
    /// 
    /// * `G` - The type of the getter function
    /// * `F` - The type of the setter function
    /// 
    /// # Examples
    /// 
    /// ```rust
    /// use rustica::datatypes::lens::Lens;
    /// 
    /// #[derive(Clone)]
    /// struct Point {
    ///     x: f64,
    ///     y: f64,
    /// }
    /// 
    /// let x_lens = Lens::new(
    ///     |p: &Point| p.x,
    ///     |p: Point, x: f64| Point { x, ..p },
    /// );
    /// ```
    pub fn new<G, F>(get: G, set: F) -> Self
    where
        G: Fn(&S) -> A + 'static,
        F: Fn(S, A) -> S + 'static,
    {
        Lens {
            get: Arc::new(get),
            set: Arc::new(set),
        }
    }

    /// Gets the focused part from the whole structure.
    /// 
    /// This operation is non-destructive and returns a clone of the focused part.
    /// 
    /// # Arguments
    /// 
    /// * `source` - The whole structure to get the part from
    /// 
    /// # Returns
    /// 
    /// A clone of the focused part
    pub fn get(&self, source: &S) -> A {
        (self.get)(source)
    }

    /// Sets the focused part to a new value, returning a new whole structure.
    /// 
    /// This operation creates a new structure rather than modifying the existing one.
    /// 
    /// # Arguments
    /// 
    /// * `source` - The whole structure to update
    /// * `value` - The new value for the focused part
    /// 
    /// # Returns
    /// 
    /// A new structure with the focused part updated
    pub fn set(&self, source: S, value: A) -> S {
        (self.set)(source, value)
    }

    /// Modifies the focused part using a function, returning a new whole structure.
    /// 
    /// This is a convenience method that combines `get` and `set` operations.
    /// 
    /// # Arguments
    /// 
    /// * `source` - The whole structure to modify
    /// * `f` - A function that transforms the focused part
    /// 
    /// # Returns
    /// 
    /// A new structure with the focused part modified by the function
    pub fn modify<F>(&self, source: S, f: F) -> S
    where
        F: Fn(A) -> A,
    {
        let value = f((self.get)(&source));
        (self.set)(source, value)
    }

    /// Maps a function over the focused part, creating a new lens.
    /// 
    /// This allows for transforming the type of the focused part while maintaining
    /// the lens laws. The transformation must be bidirectional, meaning you need
    /// to provide both forward and backward transformations.
    /// 
    /// # Arguments
    /// 
    /// * `f` - The forward transformation function
    /// * `g` - The backward transformation function
    /// 
    /// # Type Parameters
    /// 
    /// * `B` - The new type of the focused part
    /// 
    /// # Returns
    /// 
    /// A new lens that focuses on the transformed part
    /// 
    /// # Examples
    /// 
    /// ```rust
    /// use rustica::datatypes::lens::Lens;
    /// 
    /// #[derive(Clone)]
    /// struct Person {
    ///     age: u32,
    /// }
    /// 
    /// let age_lens = Lens::new(
    ///     |p: &Person| p.age,
    ///     |p: Person, age: u32| Person { age },
    /// );
    /// 
    /// // Create a lens that views age as a string
    /// let age_string_lens = age_lens.fmap(
    ///     |n| n.to_string(),
    ///     |s| s.parse().unwrap_or(0),
    /// );
    /// ```
    pub fn fmap<B: Clone + 'static>(&self, f: impl Fn(A) -> B + 'static, g: impl Fn(B) -> A + 'static) -> Lens<S, B> {
        let get = Arc::clone(&self.get);
        let set = Arc::clone(&self.set);
        Lens::new(
            move |s| f((get)(s)),
            move |s, b| (set)(s, g(b)),
        )
    }
}