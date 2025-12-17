//! # Lens (`Lens<S, A>`)
//!
//! Lens is a functional programming concept for accessing and modifying parts of immutable data structures.
//!
//! A lens provides a way to:
//! - View a part of a larger data structure
//! - Update that part while preserving the rest of the structure
//! - Transform the focused part using functions
//!
//! ## Quick Start
//!
//! ```rust
//! use rustica::datatypes::lens::Lens;
//!
//! #[derive(Clone, Debug, PartialEq)]
//! struct Person { name: String, age: u32 }
//!
//! // Create lenses for accessing struct fields
//! let name_lens = Lens::new(
//!     |p: &Person| p.name.clone(),
//!     |p: Person, name: String| Person { name, ..p },
//! );
//! let age_lens = Lens::new(
//!     |p: &Person| p.age,
//!     |p: Person, age: u32| Person { age, ..p },
//! );
//!
//! let person = Person { name: "Alice".to_string(), age: 30 };
//!
//! // Get values through lenses
//! assert_eq!(name_lens.get(&person), "Alice");
//! assert_eq!(age_lens.get(&person), 30);
//!
//! // Set values immutably
//! let renamed = name_lens.set(person.clone(), "Bob".to_string());
//! assert_eq!(renamed, Person { name: "Bob".to_string(), age: 30 });
//!
//! // Transform values with modify
//! let older = age_lens.modify(person, |age| age + 1);
//! assert_eq!(older.age, 31);
//! ```
//!
//! ## Core Concepts
//!
//! - **Immutable Updates**: All operations create new instances instead of modifying in place
//! - **Composable**: Lenses can be combined to focus on nested structures
//! - **Type-safe**: The compiler ensures that updates maintain type consistency
//!
//! ## Functional Programming Context
//!
//! In functional programming, lenses are a form of *functional reference* or *optic* that solve the
//! problem of updating immutable nested data structures. The concept originates from category theory
//! and extends the idea of getters and setters to a composable, algebraic structure.
//!
//! Key aspects of lenses in functional programming:
//!
//! - **Bidirectionality**: Unlike simple getter/setter pairs, lenses maintain a bidirectional relationship
//!   between a structure and its components, allowing roundtrip transformations.
//!
//! - **Compositionality**: Lenses can be composed, allowing navigation through deeply nested structures.
//!
//! - **Lawfulness**: Well-behaved lenses adhere to specific laws (GetSet, SetGet, SetSet) ensuring
//!   predictable behavior.
//!
//! - **Referential Transparency**: Lens operations maintain referential transparency, making them
//!   suitable for purely functional programming.
//!
//! Similar concepts in other functional languages:
//!
//! - Haskell's `lens` library by Edward Kmett
//! - Scala's `Monocle` and `Quicklens` libraries
//! - OCaml's `Lenses` and `Optics` modules
//! - PureScript's optics libraries
//!
//! ## Type Class Implementations
//!
//! Lenses implement several functional programming abstractions:
//!
//! - **Getter**: The ability to retrieve a component from a larger structure
//! - **Setter**: The ability to update a component in an immutable structure
//! - **Functor Mapping**: The ability to apply a function over the focused component
//! - **Composable**: Lenses can be composed to access nested structures
//!
//! ## Basic Usage
//!
//! ```rust
//! use rustica::datatypes::lens::Lens;
//!
//! // Define a simple data structure
//! #[derive(Clone, Debug, PartialEq)]
//! struct Person {
//!     name: String,
//!     age: u32,
//! }
//!
//! // Create lenses for each field
//! let name_lens = Lens::new(
//!     |p: &Person| p.name.clone(),
//!     |p: Person, name: String| Person { name, ..p },
//! );
//!
//! let age_lens = Lens::new(
//!     |p: &Person| p.age,
//!     |p: Person, age: u32| Person { age, ..p },
//! );
//!
//! // Use the lenses
//! let person = Person {
//!     name: "Alice".to_string(),
//!     age: 30,
//! };
//!
//! // Get values
//! assert_eq!(name_lens.get(&person), "Alice");
//! assert_eq!(age_lens.get(&person), 30);
//!
//! // Set values
//! let updated = name_lens.set(person.clone(), "Bob".to_string());
//! assert_eq!(updated.name, "Bob");
//! assert_eq!(updated.age, 30); // Original value preserved
//!
//! // Modify values
//! let older = age_lens.modify(person, |age| age + 5);
//! assert_eq!(older.age, 35);
//! ```
//!
//! ## Type Class Laws
//!
//! Lenses follow three fundamental laws that ensure their correct behavior. See the documentation
//! for the specific functions (`get`, `set`) for examples demonstrating these laws.
//!
//! ### GetSet Law
//!
//! For any lens `l` and structure `s`:
//!
//! `l.set(s.clone(), l.get(&s)) == s`
//!
//! "Setting a value to what it already is doesn't change anything"
//!
//! ### SetGet Law
//!
//! For any lens `l`, structure `s`, and value `v`:
//!
//! `l.get(&l.set(s.clone(), v)) == v`
//!
//! "If you set a value, that's what you get back"
//!
//! ### SetSet Law
//!
//! For any lens `l`, structure `s`, and values `v1` and `v2`:
//!
//! `l.set(l.set(s.clone(), v1), v2) == l.set(s, v2)`
//!
//! "Setting a value and then immediately setting another value is the same as just setting the second value"
//!
//! # Examples
//!
//! ```rust
//! use rustica::datatypes::lens::Lens;
//! use std::rc::Rc;
//!
//! // A nested data structure
//! #[derive(Clone, Debug, PartialEq)]
//! struct Address {
//!     street: String,
//!     city: String,
//! }
//!
//! #[derive(Clone, Debug, PartialEq)]
//! struct Person {
//!     name: String,
//!     address: Rc<Address>, // Using Rc for structural sharing
//! }
//!
//! // Create lenses for accessing nested fields
//! let address_lens = Lens::new(
//!     |p: &Person| p.address.as_ref().clone(),
//!     |p: Person, addr: Address| Person {
//!         address: Rc::new(addr),
//!         ..p
//!     },
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
//!     address: Rc::new(Address {
//!         street: "123 Main St".to_string(),
//!         city: "Springfield".to_string(),
//!     }),
//! };
//!
//! // Update nested field - this will create new structures
//! let updated = address_lens.modify(person.clone(), |addr| {
//!     street_lens.set(addr, "456 Oak Ave".to_string())
//! });
//!
//! assert_eq!(updated.address.street, "456 Oak Ave");
//! assert_eq!(updated.address.city, "Springfield");
//!
//! // Demonstrate structural sharing when no actual change is made
//! let unchanged = address_lens.modify(person.clone(), |addr| {
//!     street_lens.set(addr, "123 Main St".to_string()) // Same value as before
//! });
//!
//! // Verify it's the same object (structural sharing)
//! assert!(Rc::ptr_eq(&person.address, &unchanged.address));
//! ```

use std::marker::PhantomData;
use std::sync::Arc;

/// A lens is a first-class reference to a subpart of some data type.
/// It provides a way to view, modify and transform a part of a larger structure.
///
/// Lenses follow a functional approach to accessing and modifying nested data
/// structures, allowing for immutable updates that preserve the original structure.
///
/// # Type Parameters
///
/// * `S` - The type of the whole structure
/// * `A` - The type of the part being focused on
/// * `GetFn` - The type of the getter function
/// * `SetFn` - The type of the setter function
///
/// # Design Notes
///
/// - Requires both the structure and focused part to be `Clone`
/// - Functions are stored directly to avoid boxing overhead and enable better compiler optimizations
/// - Implements structural sharing optimization when `A` implements `PartialEq`
/// - Provides variants without equality checks (`set_always`, `modify_always`) for types without `PartialEq`
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
#[derive(Clone, Debug, PartialEq)]
pub struct Lens<S, A, GetFn, SetFn>
where
    GetFn: Fn(&S) -> A,
    SetFn: Fn(S, A) -> S,
{
    get: GetFn,
    set: SetFn,
    _phantom: PhantomData<(S, A)>,
}

impl<S, A, GetFn, SetFn> Lens<S, A, GetFn, SetFn>
where
    S: Clone,
    A: Clone,
    GetFn: Fn(&S) -> A,
    SetFn: Fn(S, A) -> S,
{
    /// Creates a new lens from getter and setter functions.
    ///
    /// A lens consists of two components:
    /// 1. A getter function that extracts a focus from a structure
    /// 2. A setter function that updates the focus in a structure
    ///
    /// # Arguments
    ///
    /// * `get` - A function that extracts a part from the whole structure
    /// * `set` - A function that updates the whole structure with a new part
    ///
    /// # Type Parameters
    ///
    /// * `GetFn` - The type of the getter function: `Fn(&S) -> A`
    /// * `SetFn` - The type of the setter function: `Fn(S, A) -> S`
    ///
    /// # Examples
    ///
    /// Basic lens for a simple struct:
    ///
    /// ```rust
    /// use rustica::datatypes::lens::Lens;
    ///
    /// #[derive(Clone, Debug, PartialEq)]
    /// struct Point {
    ///     x: f64,
    ///     y: f64,
    /// }
    ///
    /// // Create a lens focusing on the x coordinate
    /// let x_lens = Lens::new(
    ///     |p: &Point| p.x,
    ///     |p: Point, x: f64| Point { x, ..p },
    /// );
    ///
    /// let point = Point { x: 2.0, y: 3.0 };
    ///
    /// // Use the lens to view the focused value
    /// assert_eq!(x_lens.get(&point), 2.0);
    ///
    /// // Use the lens to update the focused value
    /// let updated = x_lens.set(point, 5.0);
    /// assert_eq!(updated, Point { x: 5.0, y: 3.0 });
    /// ```
    #[inline]
    pub fn new(get: GetFn, set: SetFn) -> Self {
        Lens {
            get,
            set,
            _phantom: PhantomData,
        }
    }

    /// Gets the focused part from the whole structure.
    ///
    /// This operation is non-destructive and returns a clone of the focused part.
    /// It's the fundamental operation for viewing a portion of a data structure
    /// through a lens.
    ///
    /// # Arguments
    ///
    /// * `source` - The whole structure to get the part from
    ///
    /// # Returns
    ///
    /// A clone of the focused part
    ///
    /// # Examples
    ///
    /// Basic usage with a simple struct:
    ///
    /// ```rust
    /// use rustica::datatypes::lens::Lens;
    ///
    /// #[derive(Clone, Debug, PartialEq)]
    /// struct User {
    ///     name: String,
    ///     email: String,
    /// }
    ///
    /// let name_lens = Lens::new(
    ///     |u: &User| u.name.clone(),
    ///     |u: User, name: String| User { name, ..u },
    /// );
    ///
    /// let user = User {
    ///     name: "Alice".to_string(),
    ///     email: "alice@example.com".to_string(),
    /// };
    ///
    /// let name = name_lens.get(&user);
    /// assert_eq!(name, "Alice");
    /// ```
    #[inline]
    pub fn get(&self, source: &S) -> A {
        (self.get)(source)
    }

    /// Sets the focused part to a new value, returning a new whole structure.
    ///
    /// This operation creates a new structure rather than modifying the existing one.
    /// If the new value is equal to the current value, the original structure is
    /// returned to enable structural sharing, which is an important optimization for
    /// larger data structures.
    ///
    /// # Requirements
    ///
    /// * The focused type `A` must implement `PartialEq` for equality comparison
    /// * If `A` doesn't implement `PartialEq`, use `set_always` instead
    ///
    /// # Arguments
    ///
    /// * `source` - The whole structure to update
    /// * `value` - The new value for the focused part
    ///
    /// # Returns
    ///
    /// A new structure with the focused part updated, or the original structure
    /// if the new value is equal to the current value
    ///
    /// # Examples
    ///
    /// Basic usage with structural sharing optimization:
    ///
    /// ```rust
    /// use rustica::datatypes::lens::Lens;
    ///
    /// #[derive(Clone, Debug, PartialEq)]
    /// struct User {
    ///     name: String,
    ///     email: String,
    /// }
    ///
    /// let name_lens = Lens::new(
    ///     |u: &User| u.name.clone(),
    ///     |u: User, name: String| User { name, ..u },
    /// );
    ///
    /// let user = User {
    ///     name: "Alice".to_string(),
    ///     email: "alice@example.com".to_string(),
    /// };
    ///
    /// // Setting to a different value creates a new structure
    /// let updated = name_lens.set(user.clone(), "Bob".to_string());
    /// assert_ne!(updated, user);
    /// assert_eq!(updated.name, "Bob");
    /// assert_eq!(updated.email, user.email); // Other fields remain unchanged
    ///
    /// // Setting to the same value returns the original structure
    /// let same = name_lens.set(user.clone(), "Alice".to_string());
    /// assert_eq!(same, user); // Values are equal
    /// ```
    #[inline]
    pub fn set(&self, source: S, value: A) -> S
    where
        A: PartialEq,
    {
        if self.get(&source) == value {
            source
        } else {
            self.set_always(source, value)
        }
    }

    /// Sets the focused part to a new value without checking equality.
    ///
    /// This variant of set always creates a new structure, even if the value
    /// doesn't change. Use this when A doesn't implement PartialEq or when
    /// you know the value will always be different. This method is also useful
    /// when working with types where equality comparison is expensive.
    ///
    /// # Arguments
    ///
    /// * `source` - The whole structure to update
    /// * `value` - The new value for the focused part
    ///
    /// # Returns
    ///
    /// A new structure with the focused part updated
    ///
    /// # Examples
    ///
    /// Basic usage with a type lacking `PartialEq`:
    ///
    /// ```rust
    /// use rustica::datatypes::lens::Lens;
    ///
    /// // A type that doesn't implement PartialEq
    /// #[derive(Clone)]
    /// struct CustomData {
    ///     value: String,
    /// }
    ///
    /// #[derive(Clone)]
    /// struct Container {
    ///     data: CustomData,
    ///     tag: String,
    /// }
    ///
    /// let data_lens = Lens::new(
    ///     |c: &Container| c.data.clone(),
    ///     |c: Container, data: CustomData| Container { data, ..c },
    /// );
    ///
    /// let container = Container {
    ///     data: CustomData { value: "original".to_string() },
    ///     tag: "v1".to_string(),
    /// };
    ///
    /// let new_data = CustomData { value: "updated".to_string() };
    /// let updated = data_lens.set_always(container, new_data);
    /// assert_eq!(updated.data.value, "updated");
    /// ```
    #[inline]
    pub fn set_always(&self, source: S, value: A) -> S {
        (self.set)(source, value)
    }

    /// Modifies the focused part using a function, returning a new whole structure.
    ///
    /// This is a convenience method that combines `get` and `set` operations.
    /// If the modification doesn't change the focused part (as determined by
    /// equality comparison), the original structure is returned to enable
    /// structural sharing.
    ///
    /// # Requirements
    ///
    /// * The focused type `A` must implement `PartialEq` for equality comparison
    /// * If `A` doesn't implement `PartialEq`, use `modify_always` instead
    ///
    /// # Arguments
    ///
    /// * `source` - The whole structure to modify
    /// * `f` - A function that transforms the focused part
    ///
    /// # Returns
    ///
    /// A new structure with the focused part modified by the function, or the
    /// original structure if no change was made
    ///
    /// # Examples
    ///
    /// Basic modification with structural sharing:
    ///
    /// ```rust
    /// use rustica::datatypes::lens::Lens;
    ///
    /// #[derive(Clone, Debug, PartialEq)]
    /// struct User {
    ///     name: String,
    ///     age: i32,
    /// }
    ///
    /// let age_lens = Lens::new(
    ///     |u: &User| u.age,
    ///     |u: User, age: i32| User { age, ..u },
    /// );
    ///
    /// let user = User {
    ///     name: "Alice".to_string(),
    ///     age: 30,
    /// };
    ///
    /// // Increment the age
    /// let older = age_lens.modify(user.clone(), |age| age + 1);
    /// assert_eq!(older.age, 31);
    /// assert_eq!(older.name, "Alice");
    ///
    /// // No change when applying identity function - structural sharing in action
    /// let same = age_lens.modify(user.clone(), |age| age);
    /// assert_eq!(same, user); // Same value due to no change
    /// ```
    #[inline]
    pub fn modify<F>(&self, source: S, f: F) -> S
    where
        F: Fn(A) -> A,
        A: PartialEq,
    {
        let current = self.get(&source);
        let new_value = f(current.clone());
        self.set(source, new_value)
    }

    /// Modifies the focused part using a function without checking equality.
    ///
    /// This variant of modify always creates a new structure, even if the
    /// value doesn't change. Use this when A doesn't implement PartialEq
    /// or when you know the value will always change. This method is also useful
    /// when equality comparison is expensive compared to creating a new structure.
    ///
    /// # Arguments
    ///
    /// * `source` - The whole structure to modify
    /// * `f` - A function that transforms the focused part
    ///
    /// # Returns
    ///
    /// A new structure with the focused part modified by the function
    ///
    /// # Examples
    ///
    /// Basic usage with a type lacking `PartialEq`:
    ///
    /// ```rust
    /// use rustica::datatypes::lens::Lens;
    ///
    /// // A type that doesn't implement PartialEq
    /// #[derive(Clone)]
    /// struct CustomVector {
    ///     data: Vec<f64>,
    /// }
    ///
    /// #[derive(Clone)]
    /// struct Analysis {
    ///     values: CustomVector,
    ///     description: String,
    /// }
    ///
    /// let values_lens = Lens::new(
    ///     |a: &Analysis| a.values.clone(),
    ///     |a: Analysis, values: CustomVector| Analysis { values, ..a },
    /// );
    ///
    /// let analysis = Analysis {
    ///     values: CustomVector { data: vec![1.0, 2.0, 3.0] },
    ///     description: "Initial data".to_string(),
    /// };
    ///
    /// // Transform the vector data
    /// let normalized = values_lens.modify_always(analysis, |mut values| {
    ///     // Normalize the vector
    ///     let sum: f64 = values.data.iter().sum();
    ///     for val in &mut values.data {
    ///         *val /= sum;
    ///     }
    ///     values
    /// });
    ///
    /// // Verify the transformation worked
    /// let expected_sum = 1.0;
    /// let actual_sum: f64 = normalized.values.data.iter().sum();
    /// assert!((actual_sum - expected_sum).abs() < 1e-10);
    /// ```
    #[inline]
    pub fn modify_always<F>(&self, source: S, f: F) -> S
    where
        F: Fn(A) -> A,
    {
        let current = self.get(&source);
        let new_value = f(current);
        self.set_always(source, new_value)
    }

    /// Maps a function over the focused part, creating a new lens.
    ///
    /// This allows for transforming the type of the focused part while maintaining
    /// the lens laws. The transformation must be bidirectional, meaning you need
    /// to provide both forward and backward transformations. This operation enables
    /// lens composition with type transformation.
    ///
    /// # Implementation Notes
    ///
    /// * The transformations must be consistent with each other to maintain lens laws
    /// * For all values x: g(f(x)) should be approximately equal to x (within reasonable bounds)
    /// * The resulting lens is a proper lens if the transformation functions maintain the lens laws
    ///
    /// # Arguments
    ///
    /// * `f` - The forward transformation function from A to B
    /// * `g` - The backward transformation function from B to A
    ///
    /// # Type Parameters
    ///
    /// * `B` - The new type of the focused part
    /// * `F` - The type of the forward transformation function: `Fn(A) -> B`
    /// * `G` - The type of the backward transformation function: `Fn(B) -> A`
    ///
    /// # Returns
    ///
    /// A new lens that focuses on the transformed part
    ///
    /// # Examples
    ///
    /// Basic type conversion example:
    ///
    /// ```rust
    /// use rustica::datatypes::lens::Lens;
    ///
    /// #[derive(Clone, Debug, PartialEq)]
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
    ///
    /// let person = Person { age: 30 };
    ///
    /// // Use the transformed lens to get a string representation
    /// assert_eq!(age_string_lens.get(&person), "30");
    ///
    /// // Use the transformed lens to set from a string
    /// let updated = age_string_lens.set(person, "42".to_string());
    /// assert_eq!(updated.age, 42);
    /// ```
    #[inline]
    pub fn fmap<B, F, G>(self, f: F, g: G) -> Lens<S, B, impl Fn(&S) -> B, impl Fn(S, B) -> S>
    where
        B: Clone,
        F: Fn(A) -> B,
        G: Fn(B) -> A,
    {
        // Use self's get and set directly without attempting to clone
        Lens::new(move |s| f((self.get)(s)), move |s, b| (self.set)(s, g(b)))
    }

    /// Composes two lenses to create a new lens that focuses on a nested structure.
    ///
    /// Given a lens from `S` to `A` and a lens from `A` to `B`, this creates a new
    /// lens from `S` to `B`. This is essential for accessing deeply nested data
    /// structures in a type-safe and composable way.
    ///
    /// # Type Parameters
    ///
    /// * `B` - The type of the deeply nested focus
    /// * `GetFn2` - The type of the inner lens getter
    /// * `SetFn2` - The type of the inner lens setter
    ///
    /// # Arguments
    ///
    /// * `other` - The inner lens that focuses from `A` to `B`
    ///
    /// # Returns
    ///
    /// A new lens that focuses from `S` directly to `B`
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::lens::Lens;
    ///
    /// #[derive(Clone, Debug, PartialEq)]
    /// struct Address { street: String, city: String }
    ///
    /// #[derive(Clone, Debug, PartialEq)]
    /// struct Person { name: String, address: Address }
    ///
    /// let address_lens = Lens::new(
    ///     |p: &Person| p.address.clone(),
    ///     |p: Person, addr: Address| Person { address: addr, ..p },
    /// );
    ///
    /// let street_lens = Lens::new(
    ///     |a: &Address| a.street.clone(),
    ///     |a: Address, street: String| Address { street, ..a },
    /// );
    ///
    /// // Compose to create a lens from Person to street
    /// let person_street_lens = address_lens.compose(street_lens);
    ///
    /// let person = Person {
    ///     name: "Alice".to_string(),
    ///     address: Address {
    ///         street: "123 Main St".to_string(),
    ///         city: "Springfield".to_string(),
    ///     },
    /// };
    ///
    /// // Get nested value directly
    /// assert_eq!(person_street_lens.get(&person), "123 Main St");
    ///
    /// // Set nested value directly
    /// let updated = person_street_lens.set(person, "456 Oak Ave".to_string());
    /// assert_eq!(updated.address.street, "456 Oak Ave");
    /// assert_eq!(updated.address.city, "Springfield"); // Other fields preserved
    /// ```
    #[inline]
    pub fn compose<B, GetFn2, SetFn2>(
        self, other: Lens<A, B, GetFn2, SetFn2>,
    ) -> Lens<S, B, impl Fn(&S) -> B, impl Fn(S, B) -> S>
    where
        B: Clone,
        GetFn2: Fn(&A) -> B,
        SetFn2: Fn(A, B) -> A,
    {
        let get1 = Arc::new(self.get);
        let set1 = self.set;
        let get2 = other.get;
        let set2 = other.set;

        let get1_for_set = get1.clone();

        Lens::new(
            move |s: &S| get2(&get1(s)),
            move |s: S, b: B| {
                let a = get1_for_set(&s);
                let new_a = set2(a, b);
                set1(s, new_a)
            },
        )
    }

    /// Alias for `compose` - chains two lenses together.
    ///
    /// This method is provided as a more fluent alternative to `compose`,
    /// allowing for a natural left-to-right reading order when chaining
    /// multiple lenses.
    ///
    /// # Type Parameters
    ///
    /// * `B` - The type of the deeply nested focus
    /// * `GetFn2` - The type of the inner lens getter
    /// * `SetFn2` - The type of the inner lens setter
    ///
    /// # Arguments
    ///
    /// * `other` - The inner lens that focuses from `A` to `B`
    ///
    /// # Returns
    ///
    /// A new lens that focuses from `S` directly to `B`
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::lens::Lens;
    ///
    /// #[derive(Clone, Debug, PartialEq)]
    /// struct Inner { value: i32 }
    ///
    /// #[derive(Clone, Debug, PartialEq)]
    /// struct Middle { inner: Inner }
    ///
    /// #[derive(Clone, Debug, PartialEq)]
    /// struct Outer { middle: Middle }
    ///
    /// let outer_middle = Lens::new(
    ///     |o: &Outer| o.middle.clone(),
    ///     |o: Outer, m: Middle| Outer { middle: m },
    /// );
    ///
    /// let middle_inner = Lens::new(
    ///     |m: &Middle| m.inner.clone(),
    ///     |m: Middle, i: Inner| Middle { inner: i },
    /// );
    ///
    /// let inner_value = Lens::new(
    ///     |i: &Inner| i.value,
    ///     |i: Inner, v: i32| Inner { value: v },
    /// );
    ///
    /// // Chain multiple lenses with `then` for readable composition
    /// let deep_lens = outer_middle.then(middle_inner).then(inner_value);
    ///
    /// let data = Outer { middle: Middle { inner: Inner { value: 42 } } };
    ///
    /// assert_eq!(deep_lens.get(&data), 42);
    ///
    /// let updated = deep_lens.set(data, 100);
    /// assert_eq!(updated.middle.inner.value, 100);
    /// ```
    #[inline]
    pub fn then<B, GetFn2, SetFn2>(
        self, other: Lens<A, B, GetFn2, SetFn2>,
    ) -> Lens<S, B, impl Fn(&S) -> B, impl Fn(S, B) -> S>
    where
        B: Clone,
        GetFn2: Fn(&A) -> B,
        SetFn2: Fn(A, B) -> A,
    {
        self.compose(other)
    }
}
