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
//! let updated = lens.set(&(Address { street: "Oak Ave".to_string(), city: "Springfield".to_string() }, p.clone()));
//! assert_eq!(updated.address.street, "Oak Ave");
//! ```
//!
//! ## Advanced Example: Nested and Collection Structures
//!
//! This example demonstrates how IsoLens can be used for nested structures and collections.
//!
//! ```rust
//! use rustica::datatypes::iso_lens::IsoLens;
//! use rustica::traits::iso::Iso;
//!
//! #[derive(Clone, Debug, PartialEq)]
//! struct Address { street: String, city: String }
//! #[derive(Clone, Debug, PartialEq)]
//! struct Person { name: String, address: Address, tags: Vec<String> }
//! #[derive(Clone, Debug, PartialEq)]
//! struct Team { name: String, members: Vec<Person> }
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
//! struct MembersIso;
//! impl Iso<Team, (Vec<Person>, Team)> for MembersIso {
//!     type From = Team;
//!     type To = (Vec<Person>, Team);
//!     fn forward(&self, from: &Team) -> (Vec<Person>, Team) {
//!         (from.members.clone(), from.clone())
//!     }
//!     fn backward(&self, to: &(Vec<Person>, Team)) -> Team {
//!         let mut t = to.1.clone();
//!         t.members = to.0.clone();
//!         t
//!     }
//! }
//!
//! let team = Team {
//!     name: "Alpha".to_string(),
//!     members: vec![Person {
//!         name: "Alice".to_string(),
//!         address: Address { street: "Main".to_string(), city: "Spring".to_string() },
//!         tags: vec!["dev".to_string()]
//!     }]
//! };
//! let members_lens = IsoLens::new(MembersIso);
//! let first_member = members_lens.get(&team).0[0].clone();
//! assert_eq!(first_member.name, "Alice");
//! ```
//!
//! ## Notes
//!
//! - IsoLens is especially useful for newtypes, tuple structs, and cases where you want to abstract over structural transformations.
//! - For most everyday lens use-cases, the classic `Lens` may be simpler; use IsoLens when you want to leverage isomorphisms or need advanced optics composition.
//!
//! See also: [`crate::datatypes::lens`], [`crate::traits::iso::Iso`]
//!
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
/// # Semantic Note
///
/// While the `set` method of `IsoLens` takes only the new target value `a: &A`,
/// to achieve traditional lens behavior (updating a part of `S` while preserving the rest),
/// the type `A` (i.e., `L::To`) is typically structured as a pair: `(FocusType, S_Context)`.
/// Here, `FocusType` is the actual type of the field being focused on, and `S_Context`
/// is usually a clone of the original `S` structure. This allows the `Iso::backward`
/// method to use `S_Context` to reconstruct the full `S` with only `FocusType` changed.
///
/// # Lens Laws
///
/// An `IsoLens` derived from a valid `Iso` will satisfy the standard lens laws:
///
/// 1.  **Get-Set Law**: If you get a value `a` from a structure `s` and then set `a` back into `s`,
///     you get the original `s` back.
///     `lens.set(&lens.get(s)) == s`
///     (This holds if `iso.backward(&iso.forward(s)) == s`, which is a law for valid `Iso`s.)
///
/// 2.  **Set-Get Law**: If you set a value `a` into a structure `s` (producing `s'`), and then get
///     the value from `s'`, you get `a` back.
///     `lens.get(&lens.set(&a)) == a`
///     (This holds if `iso.forward(&iso.backward(a)) == a`, which is a law for valid `Iso`s,
///     assuming `a` is a valid target for `backward`.)
///
/// 3.  **Set-Set Law**: If you set a value `a1` into `s` (producing `s'`), and then set `a2` into `s'`,
///     the result is the same as just setting `a2` into the original `s`.
///     `lens.set(&lens.set(&a1), &a2) == lens.set(&a2)`
///     (The `set` operation is idempotent in its effect on the focused part based on the new value `a`.)
///
/// These laws ensure that the lens behaves predictably and doesn't cause unexpected side effects
/// or loss of information, assuming the underlying `Iso` is correctly implemented.
/// For `IsoLens` where `A` is `(FocusType, S_Context)`, the laws apply similarly to `set_focus` and `modify_focus`.
///
/// For example (conceptual, full verification in tests):
/// ```rust
/// # use rustica::datatypes::iso_lens::IsoLens;
/// # use rustica::traits::iso::Iso;
/// # #[derive(Clone, Debug, PartialEq)]
/// # struct Person { name: String, age: u32 }
/// # struct NameIso;
/// # impl Iso<Person, (String, Person)> for NameIso {
/// #     type From = Person; type To = (String, Person);
/// #     fn forward(&self, from: &Person) -> (String, Person) { (from.name.clone(), from.clone()) }
/// #     fn backward(&self, to: &(String, Person)) -> Person {
/// #         let mut p = to.1.clone(); p.name = to.0.clone(); p
/// #     }
/// # }
/// # let lens = IsoLens::new(NameIso);
/// # let person = Person { name: "Alice".to_string(), age: 30 };
/// # let new_name = "Bob".to_string();
/// # let new_name_tuple = (new_name.clone(), person.clone());
/// // Get-Set (simplified for A = (FocusType, S_Context))
/// let original_a_from_s = lens.get(&person); // A = (String, Person)
/// assert_eq!(lens.set(&original_a_from_s), person);
///
/// // Set-Get
/// let person_after_set = lens.set(&new_name_tuple);
/// // We need to create a new tuple with updated context for comparison
/// let expected_tuple = (new_name, person_after_set.clone());
/// assert_eq!(lens.get(&person_after_set), expected_tuple);
/// ```
///
/// Below are runnable examples verifying these laws, particularly with `set_focus`:
///
/// ```rust
/// # use rustica::datatypes::iso_lens::IsoLens;
/// # use rustica::traits::iso::Iso;
/// #
/// #[derive(Clone, Debug, PartialEq)]
/// struct Person { name: String, age: u32, city: String }
///
/// struct NameFocusIso;
/// impl Iso<Person, (String, Person)> for NameFocusIso {
///     type From = Person;
///     type To = (String, Person);
///     fn forward(&self, from: &Person) -> (String, Person) {
///         (from.name.clone(), from.clone()) // Focus on name, keep Person as context
///     }
///     fn backward(&self, to: &(String, Person)) -> Person {
///         let (new_name, original_person_context) = to;
///         Person { name: new_name.clone(), ..original_person_context.clone() }
///     }
/// }
///
/// let lens = IsoLens::new(NameFocusIso);
/// let person = Person { name: "Alice".to_string(), age: 30, city: "New York".to_string() };
///
/// // 1. Get-Set Law (using set_focus)
/// // lens.set_focus(s, lens.get(s).0) == s
/// let original_name_focus = lens.get(&person).0; // Get the (FocusType, S_Context).0 -> FocusType
/// assert_eq!(lens.set_focus(&person, &original_name_focus), person, "Get-Set Law failed for set_focus");
///
/// // 2. Set-Get Law (using set_focus)
/// // lens.get(lens.set_focus(s, new_focus)).0 == new_focus
/// let new_name = "Bob".to_string();
/// let person_after_set_focus = lens.set_focus(&person, &new_name);
/// assert_eq!(lens.get(&person_after_set_focus).0, new_name, "Set-Get Law failed for set_focus");
///
/// // 3. Set-Set Law (using set_focus)
/// // lens.set_focus(lens.set_focus(s, name1), name2) == lens.set_focus(s, name2)
/// let name1 = "Charlie".to_string();
/// let name2 = "David".to_string();
/// let s_prime = lens.set_focus(&person, &name1);
/// assert_eq!(lens.set_focus(&s_prime, &name2), lens.set_focus(&person, &name2), "Set-Set Law failed for set_focus");
///
/// // Verification with modify_focus (example: Modify-Get)
/// // If f is identity, modify_focus(s, id).name == s.name
/// let person_modified_id = lens.modify_focus(&person, |name| name); // Identity function
/// assert_eq!(person_modified_id, person, "Modify-Get (identity) Law failed for modify_focus");
///
/// // Another modify_focus check: Get-Modify-Get
/// // lens.get(lens.modify_focus(s, f)).0 == f(lens.get(s).0)
/// let s_modified = lens.modify_focus(&person, |name| name.to_uppercase());
/// assert_eq!(lens.get(&s_modified).0, person.name.to_uppercase(), "Get-Modify-Get Law failed for modify_focus");
/// ```
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
/// let updated = lens.set(&("Bob".to_string(), person.clone()));
/// assert_eq!(updated.name, "Bob");
/// assert_eq!(updated.age, 30); // Original value preserved
///```
#[derive(Clone, Debug, PartialEq)]
pub struct IsoLens<S, A, L>
where
    L: Iso<S, A, From = S, To = A>,
{
    pub iso: L,
    pub phantom: std::marker::PhantomData<(S, A)>,
}

impl<S, A, L> IsoLens<S, A, L>
where
    L: Iso<S, A, From = S, To = A>,
    S: Clone,
    A: Clone,
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
    /// let updated = lens.set(&("Bob".to_string(), p.clone()));
    /// assert_eq!(updated.name, "Bob");
    /// assert_eq!(updated.age, 30); // Original value preserved
    /// ```
    ///
    /// # Performance
    /// This method is O(1) as it only involves struct initialization.
    #[inline]
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
    /// assert_eq!(lens.get(&p), ("Alice".to_string(), p.clone()));
    /// ```
    ///
    /// # Performance
    /// Performance depends on the underlying `Iso::forward` implementation and the cost of cloning `A`.
    /// Typically, this involves cloning the focused part and potentially the context.
    #[inline]
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
    /// let updated = lens.set(&("Bob".to_string(), p.clone()));
    /// assert_eq!(updated.name, "Bob");
    /// ```
    #[inline]
    pub fn set(&self, a: &A) -> S
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
    #[inline]
    pub fn modify<F>(&self, s: &S, f: F) -> S
    where
        F: FnOnce(A) -> A,
        S: Clone,
        A: Clone,
    {
        let a = self.get(s);
        self.set(&f(a))
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
    /// let updated = composed.set(&(100, Outer { inner: Inner { value: 100 } }));
    /// assert_eq!(updated.inner.value, 100);
    /// ```
    ///
    /// # Performance
    /// This method is O(1) as it only involves creating a new `IsoLens` struct with a composed `Iso`.
    /// The performance of the *resulting* lens's methods (`get`, `set`, etc.) will depend on the
    /// combined complexities of the composed `Iso`s.
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

    /// Returns a reference to the underlying Iso.
    ///
    /// # Examples
    /// ```rust
    /// use rustica::datatypes::iso_lens::IsoLens;
    /// use rustica::traits::iso::Iso;
    /// #[derive(Clone, Debug, PartialEq)]
    /// struct Person { name: String, age: u32 }
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
    /// let lens = IsoLens::new(NameIso);
    /// let iso = lens.iso_ref();
    /// let p = Person { name: "Alice".to_string(), age: 30 };
    /// let (name, _) = iso.forward(&p);
    /// assert_eq!(name, "Alice");
    /// ```
    ///
    /// # Performance
    /// This method is O(1) as it simply returns a reference.
    #[inline]
    pub fn iso_ref(&self) -> &L {
        &self.iso
    }
}

impl<S, FocusType, L> IsoLens<S, (FocusType, S), L>
where
    L: Iso<S, (FocusType, S), From = S, To = (FocusType, S)>,
    S: Clone,
    FocusType: Clone,
{
    /// Sets the focused part of the structure `s` to `new_focus_value`,
    /// preserving other parts of `s`.
    ///
    /// This is a convenience method for `IsoLens` instances where the target
    /// type `A` of the Iso (i.e., `L::To`) is a pair `(FocusType, S)`.
    /// It simplifies the call to `set` by constructing the required tuple internally,
    /// which is then used by `Iso::backward`.
    ///
    /// # Arguments
    /// * `s` - A reference to the original structure.
    /// * `new_focus_value` - A reference to the new value for the focused part.
    ///
    /// # Returns
    /// A new structure `S` with the focused part updated.
    ///
    /// # Examples
    /// ```rust
    /// # use rustica::datatypes::iso_lens::IsoLens;
    /// # use rustica::traits::iso::Iso;
    /// #
    /// # #[derive(Clone, Debug, PartialEq)]
    /// # struct Person { name: String, age: u32 }
    /// #
    /// # struct NameIso;
    /// # impl Iso<Person, (String, Person)> for NameIso {
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
    /// #
    /// let lens = IsoLens::new(NameIso);
    /// let person = Person { name: "Alice".to_string(), age: 30 };
    /// let new_name = "Bob".to_string();
    ///
    /// // Using the set_focus method:
    /// let updated = lens.set_focus(&person, &new_name);
    ///
    /// // This is equivalent to manually constructing the tuple for `set`:
    /// // let updated_manual = lens.set(&(new_name.clone(), person.clone()));
    /// // assert_eq!(updated, updated_manual);
    ///
    /// assert_eq!(updated.name, "Bob");
    /// assert_eq!(updated.age, 30); // Original age preserved
    /// ```
    pub fn set_focus(&self, s: &S, new_focus_value: &FocusType) -> S {
        let a_tuple = (new_focus_value.clone(), s.clone());
        self.iso.backward(&a_tuple)
    }

    /// Applies a function to the focused part of the structure `s` and returns a new structure.
    ///
    /// This is a convenience method for `IsoLens` instances where the target
    /// type `A` of the Iso (i.e., `L::To`) is a pair `(FocusType, S)`.
    /// It allows direct transformation of the `FocusType`.
    ///
    /// The function `f` takes the current `FocusType` by value and should return
    /// the modified `FocusType`.
    ///
    /// # Arguments
    /// * `s` - A reference to the original structure.
    /// * `f` - A function `FnOnce(FocusType) -> FocusType` to transform the focused part.
    ///
    /// # Returns
    /// A new structure `S` with the focused part transformed.
    ///
    /// # Examples
    /// ```rust
    /// # use rustica::datatypes::iso_lens::IsoLens;
    /// # use rustica::traits::iso::Iso;
    /// #
    /// # #[derive(Clone, Debug, PartialEq)]
    /// # struct Person { name: String, age: u32 }
    /// #
    /// # struct NameIso;
    /// # impl Iso<Person, (String, Person)> for NameIso {
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
    /// #
    /// let lens = IsoLens::new(NameIso);
    /// let person = Person { name: "Alice".to_string(), age: 30 };
    ///
    /// let updated_person = lens.modify_focus(&person, |name_focus| name_focus.to_uppercase());
    ///
    /// assert_eq!(updated_person.name, "ALICE");
    /// assert_eq!(updated_person.age, 30); // Original age preserved
    /// ```
    pub fn modify_focus<F>(&self, s: &S, f: F) -> S
    where
        F: FnOnce(FocusType) -> FocusType,
    {
        let (current_focus_value, s_context) = self.iso.forward(s);
        let new_focus_value = f(current_focus_value);
        self.iso.backward(&(new_focus_value, s_context))
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

    #[inline]
    fn forward(&self, from: &A) -> (B, S) {
        self.inner.forward(from)
    }

    #[inline]
    fn backward(&self, to: &(B, S)) -> A {
        self.inner.backward(to)
    }
}
