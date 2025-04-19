//! # IsoLens: Iso-based Lens Optic
//!
//! This module provides an optic (IsoLens) that generalizes the concept of a Lens using the Iso abstraction.
//!
//! ## Core Idea
//!
//! - An IsoLens is a lens built from an isomorphism (Iso) between a structure and a pair of (focused part, structure).
//! - All getter/setter logic is expressed using Iso's `forward` and `backward` methods, ensuring bidirectional, type-safe, and immutable updates.
//!
//! ## Use Cases
//!
//! - Accessing and updating nested fields in complex immutable data structures
//! - Building composable and reusable accessors for deeply nested types
//! - Adapting optics to types where you have a natural isomorphism (e.g., tuple wrappers, newtypes)
//!
//! ## Example
//!
//! ```rust
//! use rustica::datatypes::iso_lens::IsoLens;
//! use rustica::traits::iso::Iso;
//!
//! #[derive(Clone, Debug, PartialEq)]
//! struct Address { street: String, city: String }
//! #[derive(Clone, Debug, PartialEq)]
//! struct Person { name: String, address: Address }
//!
//! struct AddressIso;
//! impl Iso<Person, (Address, Person)> for AddressIso {
//!     type From = Person;
//!     type To = (Address, Person);
//!     fn forward(&self, from: &Person) -> (Address, Person) {
//!         (from.address.clone(), from.clone())
//!     }
//!     fn backward(&self, to: &(Address, Person)) -> Person {
//!         let mut p = to.1.clone();
//!         p.address = to.0.clone();
//!         p
//!     }
//! }
//!
//! let lens = IsoLens::new(AddressIso);
//! let p = Person {
//!     name: "Alice".to_string(),
//!     address: Address { street: "Main St".to_string(), city: "Springfield".to_string() },
//! };
//! // Get the address
//! let addr = lens.get(&p);
//! assert_eq!(addr.street, "Main St");
//! // Update the address
//! let updated = lens.set(&p, &Address { street: "Oak Ave".to_string(), city: "Springfield".to_string() });
//! assert_eq!(updated.address.street, "Oak Ave");
//! ```
//!
//! ## Notes
//!
//! - IsoLens is especially useful for newtypes, tuple structs, and cases where you want to abstract over structural transformations.
//! - For most everyday lens use-cases, the classic `Lens` may be simpler; use IsoLens when you want to leverage isomorphisms or need advanced optics composition.
//!
//! See also: [`crate::datatypes::lens`], [`crate::traits::iso::Iso`]

//! # Iso-based Lens
//!
//! This module provides a Lens optic based on the Iso abstraction.
//! A Lens is an optic that allows safe and functional access/modification of a field within a structure.
//!
//! ## Core Idea
//!
//! - A Lens can be generalized as an Iso of the form S <-> (A, S)
//! - getter/setter functions are wrapped as Iso's forward/backward operations

use crate::traits::iso::Iso;
use std::marker::PhantomData;

/// Iso-based Lens optic.
///
/// This struct represents a Lens built on top of an Iso abstraction.
/// It allows safe and functional access to, and modification of, a field within an immutable data structure.
///
/// # Type Parameters
/// * `S` - The type of the whole structure.
/// * `A` - The type of the focused part.
/// * `L` - The Iso implementation from `S` to `(A, S)`.
///
/// # Examples
///
/// ```rust
/// use rustica::datatypes::iso_lens::IsoLens;
/// use rustica::traits::iso::Iso;
///
/// // Define a simple data structure
/// #[derive(Clone, Debug, PartialEq)]
/// struct Person { name: String, age: u32 }
///
/// // Create an Iso implementation for the name field
/// struct NameIso;
/// impl Iso<Person, (String, Person)> for NameIso {
///     type From = Person;
///     type To = (String, Person);
///     
///     fn forward(&self, from: &Person) -> (String, Person) {
///         (from.name.clone(), from.clone())
///     }
///     
///     fn backward(&self, to: &(String, Person)) -> Person {
///         let mut p = to.1.clone();
///         p.name = to.0.clone();
///         p
///     }
/// }
///
/// // Create and use the lens
/// let lens = IsoLens::new(NameIso);
/// let alice = Person { name: "Alice".to_string(), age: 30 };
///
/// // Get the name
/// assert_eq!(lens.get(&alice), "Alice");
///
/// // Update the name
/// let bob = lens.set(&alice, &"Bob".to_string());
/// assert_eq!(bob.name, "Bob");
/// assert_eq!(bob.age, 30);  // Other fields unchanged
/// ```
pub struct IsoLens<S, A, L: Iso<S, (A, S), From = S, To = (A, S)>> {
    iso: L,
    phantom: PhantomData<(S, A)>,
}

impl<S, A, L> IsoLens<S, A, L>
where
    L: Iso<S, (A, S), From = S, To = (A, S)>,
{
    /// Creates a new IsoLens from an Iso implementation.
    ///
    /// # Arguments
    /// * `iso` - An Iso instance that defines a bidirectional mapping between the structure and its focused part.
    ///
    /// # Returns
    /// A new IsoLens instance.
    ///
    /// # Examples
    /// ```rust
    /// use rustica::datatypes::iso_lens::IsoLens;
    /// use rustica::traits::iso::Iso;
    ///
    /// #[derive(Clone, Debug, PartialEq)]
    /// struct Person { name: String, age: u32 }
    ///
    /// struct NameIsoLens;
    /// impl Iso<Person, (String, Person)> for NameIsoLens {
    ///     type From = Person;
    ///     type To = (String, Person);
    ///     fn forward(&self, from: &Person) -> (String, Person) {
    ///         (from.name.clone(), from.clone())
    ///     }
    ///     fn backward(&self, to: &(String, Person)) -> Person {
    ///         let mut p = to.1.clone();
    ///         p.name = to.0.clone();
    ///         p
    ///     }
    /// }
    ///
    /// let lens = IsoLens::new(NameIsoLens);
    /// let p = Person { name: "Alice".into(), age: 30 };
    /// assert_eq!(lens.get(&p), "Alice");
    /// let updated = lens.set(&p, &"Bob".to_string());
    /// assert_eq!(updated.name, "Bob");
    /// let modified = lens.modify(&p, |n| n.to_uppercase());
    /// assert_eq!(modified.name, "ALICE");
    /// ```
    pub fn new(iso: L) -> Self {
        Self {
            iso,
            phantom: PhantomData,
        }
    }

    /// Extracts the focused part from the structure.
    ///
    /// This method uses the Iso's `forward` mapping to access the field of interest.
    ///
    /// # Arguments
    /// * `s` - A reference to the structure.
    ///
    /// # Returns
    /// A clone of the focused part.
    ///
    /// # Examples
    /// ```rust
    /// # use rustica::datatypes::iso_lens::IsoLens;
    /// # use rustica::traits::iso::Iso;
    /// # #[derive(Clone, Debug, PartialEq)]
    /// # struct Person { name: String, age: u32 }
    /// # struct NameIsoLens;
    /// # impl Iso<Person, (String, Person)> for NameIsoLens {
    /// #     type From = Person;
    /// #     type To = (String, Person);
    /// #     fn forward(&self, from: &Person) -> (String, Person) {
    /// #         (from.name.clone(), from.clone())
    /// #     }
    /// #     fn backward(&self, to: &(String, Person)) -> Person {
    /// #         let mut p = to.1.clone();
    /// #         p.name = to.0.clone();
    /// #         p
    /// #     }
    /// # }
    /// let lens = IsoLens::new(NameIsoLens);
    /// let p = Person { name: "Alice".into(), age: 30 };
    /// assert_eq!(lens.get(&p), "Alice");
    /// ```
    pub fn get(&self, s: &S) -> A
    where
        A: Clone,
    {
        let (a, _) = self.iso.forward(s);
        a
    }

    /// Creates a new structure with the focused part replaced by a new value.
    ///
    /// This method uses the Iso's `backward` mapping to update the field of interest in an immutable way.
    ///
    /// # Arguments
    /// * `s` - A reference to the original structure.
    /// * `a` - A reference to the new value for the focused part.
    ///
    /// # Returns
    /// A new structure with the updated value.
    ///
    /// # Examples
    /// ```rust
    /// # use rustica::datatypes::iso_lens::IsoLens;
    /// # use rustica::traits::iso::Iso;
    /// # #[derive(Clone, Debug, PartialEq)]
    /// # struct Person { name: String, age: u32 }
    /// # struct NameIsoLens;
    /// # impl Iso<Person, (String, Person)> for NameIsoLens {
    /// #     type From = Person;
    /// #     type To = (String, Person);
    /// #     fn forward(&self, from: &Person) -> (String, Person) {
    /// #         (from.name.clone(), from.clone())
    /// #     }
    /// #     fn backward(&self, to: &(String, Person)) -> Person {
    /// #         let mut p = to.1.clone();
    /// #         p.name = to.0.clone();
    /// #         p
    /// #     }
    /// # }
    /// let lens = IsoLens::new(NameIsoLens);
    /// let p = Person { name: "Alice".into(), age: 30 };
    /// let updated = lens.set(&p, &"Bob".to_string());
    /// assert_eq!(updated.name, "Bob");
    /// ```
    pub fn set(&self, s: &S, a: &A) -> S
    where
        S: Clone,
        A: Clone,
    {
        self.iso.backward(&(a.clone(), s.clone()))
    }

    /// Applies a function to the focused part and returns a new structure with the modified value.
    ///
    /// This is a composition of `get` and `set`, allowing transformation of the field in a functional style.
    ///
    /// # Arguments
    /// * `s` - A reference to the original structure.
    /// * `f` - A function to transform the focused part.
    ///
    /// # Returns
    /// A new structure with the transformed value.
    ///
    /// # Examples
    /// ```rust
    /// # use rustica::datatypes::iso_lens::IsoLens;
    /// # use rustica::traits::iso::Iso;
    /// # #[derive(Clone, Debug, PartialEq)]
    /// # struct Person { name: String, age: u32 }
    /// # struct NameIsoLens;
    /// # impl Iso<Person, (String, Person)> for NameIsoLens {
    /// #     type From = Person;
    /// #     type To = (String, Person);
    /// #     fn forward(&self, from: &Person) -> (String, Person) {
    /// #         (from.name.clone(), from.clone())
    /// #     }
    /// #     fn backward(&self, to: &(String, Person)) -> Person {
    /// #         let mut p = to.1.clone();
    /// #         p.name = to.0.clone();
    /// #         p
    /// #     }
    /// # }
    /// let lens = IsoLens::new(NameIsoLens);
    /// let p = Person { name: "Alice".into(), age: 30 };
    /// let modified = lens.modify(&p, |n| n.to_uppercase());
    /// assert_eq!(modified.name, "ALICE");
    /// ```
    pub fn modify<F>(&self, s: &S, f: F) -> S
    where
        S: Clone,
        A: Clone,
        F: FnOnce(A) -> A,
    {
        let current = self.get(s);
        let updated = f(current);
        self.set(s, &updated)
    }
}
