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
//! assert_eq!(addr.0.street, "Main St");
//! // Update the address
//! let updated = lens.set(&p, &(Address { street: "Oak Ave".to_string(), city: "Springfield".to_string() }, p.clone()));
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

use crate::traits::iso::{ComposedIso, Iso};
use std::marker::PhantomData;

/// Type alias for composed lens type
pub type ComposedIsoLens<S, A, B, L, L2> =
    IsoLens<S, (B, S), ComposedIso<L, PairIso<L2, A, B, S>, S, A, (B, S)>>;

/// Iso-based Lens optic.
///
/// This struct represents a Lens built on top of an Iso abstraction.
/// It allows safe and functional access to, and modification of, a field within an immutable data structure.
///
/// # Type Parameters
/// * `S` - The type of the whole structure.
/// * `A` - The type of the focused part.
/// * `L` - The Iso implementation from `S` to `A`.
///
/// # Examples
///
/// ```rust
/// use rustica::datatypes::iso_lens::IsoLens;
/// use rustica::traits::iso::Iso;
///
/// // Define structure and iso implementation
/// #[derive(Clone, Debug, PartialEq)]
/// struct Person { name: String, age: u32 }
///
/// struct NameIso;
/// impl Iso<Person, (String, Person)> for NameIso {
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
/// // Create and use the lens
/// let lens = IsoLens::new(NameIso);
/// let person = Person { name: "Alice".to_string(), age: 30 };
///
/// assert_eq!(lens.get(&person), ("Alice".to_string(), person.clone()));
/// let updated = lens.set(&person, &("Bob".to_string(), person.clone()));
/// assert_eq!(updated.name, "Bob");
/// assert_eq!(updated.age, 30); // Original value preserved
///
pub struct IsoLens<S, A, L>
where
    L: Iso<S, A, From = S, To = A>,
{
    pub iso: L,
    pub _phantom: std::marker::PhantomData<(S, A)>,
}

impl<S, A, L> IsoLens<S, A, L>
where
    L: Iso<S, A, From = S, To = A>,
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
    /// assert_eq!(lens.get(&p), ("Alice".to_string(), p.clone()));
    /// let updated = lens.set(&p, &("Bob".to_string(), p.clone()));
    /// assert_eq!(updated.name, "Bob");
    /// assert_eq!(updated.age, 30); // Original value preserved
    /// ```
    pub fn new(iso: L) -> Self {
        Self {
            iso,
            _phantom: PhantomData,
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
    /// assert_eq!(lens.get(&p), ("Alice".to_string(), p.clone()));
    /// ```
    pub fn get(&self, s: &S) -> A
    where
        A: Clone,
    {
        self.iso.forward(s)
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
    /// let updated = lens.set(&p, &("Bob".to_string(), p.clone()));
    /// assert_eq!(updated.name, "Bob");
    /// ```
    pub fn set(&self, _s: &S, a: &A) -> S
    where
        S: Clone,
        A: Clone,
    {
        self.iso.backward(a)
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
    /// let modified = lens.modify(&p, |n| (n.0.to_uppercase(), n.1.clone()));
    /// assert_eq!(modified.name, "ALICE");
    /// ```
    pub fn modify<F>(&self, s: &S, f: F) -> S
    where
        F: FnOnce(&A) -> A,
        S: Clone,
        A: Clone,
    {
        let a = self.get(s);
        self.set(s, &f(&a))
    }

    /// Composes this IsoLens with another IsoLens to focus deeper into a nested structure.
    ///
    /// # Type Parameters
    /// * `B` - The type of the deeper focused part
    /// * `L2` - The Iso implementation from `A` to `(B, S)`
    ///
    /// # Arguments
    /// * `other` - The IsoLens to compose with (must focus from `A` to `(B, S)`)
    ///
    /// # Returns
    /// A new IsoLens that focuses from `S` to `(B, S)`.
    ///
    /// # Examples
    /// ```rust
    /// use rustica::datatypes::iso_lens::IsoLens;
    /// use rustica::traits::iso::Iso;
    /// #[derive(Clone, Debug, PartialEq)]
    /// struct Inner { value: i32 }
    /// #[derive(Clone, Debug, PartialEq)]
    /// struct Outer { inner: Inner }
    /// struct InnerIso;
    /// impl Iso<Outer, Inner> for InnerIso {
    ///     type From = Outer;
    ///     type To = Inner;
    ///     fn forward(&self, from: &Outer) -> Inner {
    ///         from.inner.clone()
    ///     }
    ///     fn backward(&self, to: &Inner) -> Outer {
    ///         Outer { inner: to.clone() }
    ///     }
    /// }
    /// struct ValuePairIso;
    /// impl Iso<Inner, (i32, Outer)> for ValuePairIso {
    ///     type From = Inner;
    ///     type To = (i32, Outer);
    ///     fn forward(&self, from: &Inner) -> (i32, Outer) {
    ///         (from.value, Outer { inner: from.clone() })
    ///     }
    ///     fn backward(&self, to: &(i32, Outer)) -> Inner {
    ///         Inner { value: to.0 }
    ///     }
    /// }
    /// let outer_lens = IsoLens::new(InnerIso);
    /// let value_pair_lens = IsoLens::new(ValuePairIso);
    /// let composed = outer_lens.compose(value_pair_lens);
    /// let o = Outer { inner: Inner { value: 42 } };
    /// assert_eq!(composed.get(&o).0, 42);
    /// let updated = composed.set(&o, &(100, Outer { inner: Inner { value: 100 } }));
    /// assert_eq!(updated.inner.value, 100);
    /// ```
    pub fn compose<B, L2>(self, other: IsoLens<A, (B, S), L2>) -> ComposedIsoLens<S, A, B, L, L2>
    where
        L2: Iso<A, (B, S), From = A, To = (B, S)>,
        A: Clone,
        B: Clone,
        S: Clone,
    {
        let pair_iso = PairIso {
            inner: other.iso,
            phantom: std::marker::PhantomData,
        };
        let composed_iso = ComposedIso {
            first: self.iso,
            second: pair_iso,
            phantom: std::marker::PhantomData,
        };
        IsoLens::new(composed_iso)
    }
}

/// Helper Iso that converts between A <-> (B, S)
pub struct PairIso<L2, A, B, S>
where
    L2: Iso<A, (B, S), From = A, To = (B, S)>,
{
    pub inner: L2,
    pub phantom: std::marker::PhantomData<(A, B, S)>,
}

impl<L2, A, B, S> Iso<A, (B, S)> for PairIso<L2, A, B, S>
where
    L2: Iso<A, (B, S), From = A, To = (B, S)>,
    A: Clone,
    B: Clone,
    S: Clone,
{
    type From = A;
    type To = (B, S);

    fn forward(&self, from: &A) -> (B, S) {
        self.inner.forward(from)
    }

    fn backward(&self, to: &(B, S)) -> A {
        self.inner.backward(to)
    }
}
