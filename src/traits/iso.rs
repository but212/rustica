//! # Isomorphism
//!
//! This module provides the `Iso` trait which represents isomorphisms between types.
//! An isomorphism is a pair of functions that convert between two types while preserving
//! their structure, with the property that converting from A to B and back to A gives
//! you the original value (and similarly for B to A and back to B).
//!
//! ## Examples
//!
//! ```rust
//! use rustica::traits::iso::Iso;
//!
//! // An isomorphism between String and Vec<char>
//! struct StringVecIso;
//!
//! impl Iso<String, Vec<char>> for StringVecIso {
//!     type From = String;
//!     type To = Vec<char>;
//!
//!     fn forward(&self, from: &Self::From) -> Self::To {
//!         from.chars().collect()
//!     }
//!
//!     fn backward(&self, to: &Self::To) -> Self::From {
//!         to.iter().collect()
//!     }
//! }
//!
//! // Using the isomorphism
//! let s = String::from("hello");
//! let vec = StringVecIso.forward(&s);
//! assert_eq!(vec, vec!['h', 'e', 'l', 'l', 'o']);
//! let s2 = StringVecIso.backward(&vec);
//! assert_eq!(s, s2);
//! ```
//!
//! ## Laws
//!
//! A valid isomorphism must satisfy these laws:
//!
//! 1. **Round-trip from A to B to A**: `backward(forward(a)) == a`
//! 2. **Round-trip from B to A to B**: `forward(backward(b)) == b`
//!
//! ## Common Use Cases
//!
//! Isomorphisms are useful for:
//!
//! 1. **Data Conversion** - When you need to seamlessly convert between equivalent representations
//! 2. **Lens and Optics** - Building blocks for lenses, prisms, and other optics
//! 3. **Domain Modeling** - Creating type-safe abstractions that map between domain concepts

use crate::prelude::Validated;
use std::marker::PhantomData;

/// A trait representing an isomorphism between two types.
///
/// An isomorphism defines a bidirectional mapping between types where converting
/// from one type to the other and back yields the original value. This preserves
/// all information during conversion.
///
/// # Type Parameters
///
/// * `A`: The first type in the isomorphism
/// * `B`: The second type in the isomorphism
///
/// Note: this trait also defines associated types `From` and `To` which are the types actually
/// used by `forward` and `backward`. Implementations in this crate typically set `From = A` and
/// `To = B`.
///
pub trait Iso<A, B> {
    /// The source type of the isomorphism.
    type From;

    /// The target type of the isomorphism.
    type To;

    /// Converts from the source type to the target type.
    ///
    /// # Arguments
    ///
    /// * `from` - A reference to a value of the source type
    ///
    /// # Returns
    ///
    /// A value of the target type
    ///
    fn forward(&self, from: &Self::From) -> Self::To;

    /// Converts from the target type back to the source type.
    ///
    /// # Arguments
    ///
    /// * `to` - A reference to a value of the target type
    ///
    /// # Returns
    ///
    /// A value of the source type
    ///
    fn backward(&self, to: &Self::To) -> Self::From;

    /// Converts a function that operates on the target type to a function
    /// that operates on the source type.
    ///
    /// # Type Parameters
    ///
    /// * `F` - The type of the function that operates on target values
    ///
    /// # Arguments
    ///
    /// * `f` - A function that takes a reference to a target value and returns some result
    ///
    /// # Returns
    ///
    /// A function that takes a reference to a source value and returns the same result type
    #[inline]
    fn map_from_target<F, R>(&self, f: F) -> impl Fn(&Self::From) -> R
    where
        F: Fn(&Self::To) -> R,
    {
        move |from| f(&self.forward(from))
    }

    /// Converts a function that operates on the source type to a function
    /// that operates on the target type.
    ///
    /// # Type Parameters
    ///
    /// * `F` - The type of the function that operates on source values
    ///
    /// # Arguments
    ///
    /// * `f` - A function that takes a reference to a source value and returns some result
    ///
    /// # Returns
    ///
    /// A function that takes a reference to a target value and returns the same result type
    #[inline]
    fn map_from_source<F, R>(&self, f: F) -> impl Fn(&Self::To) -> R
    where
        F: Fn(&Self::From) -> R,
    {
        move |to| f(&self.backward(to))
    }

    /// Creates a new isomorphism by composing this isomorphism with another.
    ///
    /// Composition allows chaining conversions between multiple types.
    /// For example, if you have `A -> B` and `B -> C`, you can compose them to get `A -> C`.
    ///
    /// # Type Parameters
    ///
    /// * `C` - The target type of the second isomorphism
    /// * `ISO2` - The type of the second isomorphism
    ///
    /// # Arguments
    ///
    /// * `other` - The second isomorphism to compose with
    ///
    /// # Returns
    ///
    /// A new isomorphism that represents the composition of the two isomorphisms
    ///
    fn iso_compose<C, ISO2>(&self, other: ISO2) -> ComposedIso<Self, ISO2, A, B, C>
    where
        Self: Iso<A, B> + Sized + Clone,
        Self::From: Clone,
        Self::To: Clone,
        B: Clone,
        ISO2: Iso<B, C, From = B, To = C>,
        ISO2::From: Clone,
        ISO2::To: Clone,
        C: Clone,
    {
        ComposedIso {
            first: self.clone(),
            second: other,
            _phantom: PhantomData,
        }
    }

    /// Creates an inverse isomorphism that swaps the source and target types.
    ///
    /// # Type Parameters
    ///
    /// * `A` - The source type of the original isomorphism
    /// * `B` - The target type of the original isomorphism
    ///
    /// # Returns
    ///
    /// A new isomorphism with the same types but with source and target swapped
    ///
    fn inverse(&self) -> InverseIso<Self, A, B>
    where
        Self: Sized + Clone,
    {
        InverseIso {
            original: self.clone(),
            _phantom: PhantomData,
        }
    }
}

/// An isomorphism created by composing two other isomorphisms.
///
/// This type allows chaining two isomorphisms together to create a new isomorphism
/// that transforms from type `A` to type `C` via an intermediate type `B`.
///
/// # Type Parameters
///
/// * `ISO1`: An isomorphism from `A` to `B`
/// * `ISO2`: An isomorphism from `B` to `C`
/// * `A`: The source type of the composed isomorphism
/// * `B`: The intermediate type
/// * `C`: The target type of the composed isomorphism
///
pub struct ComposedIso<ISO1, ISO2, A, B, C>
where
    ISO1: Iso<A, B>,
    ISO2: Iso<B, C>,
{
    pub first: ISO1,
    pub second: ISO2,
    pub _phantom: PhantomData<(A, B, C)>,
}

impl<ISO1, ISO2, A, B, C> Iso<A, C> for ComposedIso<ISO1, ISO2, A, B, C>
where
    ISO1: Iso<A, B, From = A, To = B>,
    ISO2: Iso<B, C, From = B, To = C>,
    A: Clone,
    B: Clone,
    C: Clone,
{
    type From = A;
    type To = C;

    fn forward(&self, from: &Self::From) -> Self::To {
        // Since we've constrained the types to be equal, we can use them directly
        let b = self.first.forward(from);
        self.second.forward(&b)
    }

    fn backward(&self, to: &Self::To) -> Self::From {
        // Since we've constrained the types to be equal, we can use them directly
        let b = self.second.backward(to);
        self.first.backward(&b)
    }
}

/// An isomorphism that inverts the direction of another isomorphism.
///
/// This struct allows you to flip the direction of an existing isomorphism,
/// effectively swapping the `forward` and `backward` operations.
///
/// # Type Parameters
///
/// * `ISO` - The original isomorphism type
/// * `A` - The source type of the original isomorphism
/// * `B` - The target type of the original isomorphism
///
pub struct InverseIso<ISO, A, B>
where
    ISO: Iso<A, B>,
{
    original: ISO,
    _phantom: PhantomData<(A, B)>,
}

impl<ISO, A, B> Iso<B, A> for InverseIso<ISO, A, B>
where
    ISO: Iso<A, B, From = A, To = B>,
    A: Clone,
    B: Clone,
{
    type From = B;
    type To = A;

    fn forward(&self, from: &Self::From) -> Self::To {
        // Since we've constrained the types to be equal, we can use them directly
        self.original.backward(from)
    }

    fn backward(&self, to: &Self::To) -> Self::From {
        // Since we've constrained the types to be equal, we can use them directly
        self.original.forward(to)
    }
}

/// Extension methods for types that implement `Iso`.
pub trait IsoExt<A, B>: Iso<A, B> {
    /// Applies this isomorphism to convert a value of the source type into the target type.
    ///
    /// # Arguments
    ///
    /// * `value` - A value of the source type
    ///
    /// # Returns
    ///
    /// The converted value in the target type
    fn convert_forward(&self, value: &Self::From) -> Self::To {
        self.forward(value)
    }

    /// Applies this isomorphism to convert a value of the target type back to the source type.
    ///
    /// # Arguments
    ///
    /// * `value` - A value of the target type
    ///
    /// # Returns
    ///
    /// The converted value in the source type
    fn convert_backward(&self, value: &Self::To) -> Self::From {
        self.backward(value)
    }

    /// Modifies a value of the source type by applying a function to its representation
    /// in the target type.
    ///
    /// # Type Parameters
    ///
    /// * `F` - The type of the function that modifies target values
    ///
    /// # Arguments
    ///
    /// * `from` - A value of the source type
    /// * `f` - A function that transforms a target value into another target value
    ///
    /// # Returns
    ///
    /// The modified value in the source type
    fn modify<F>(&self, from: &Self::From, f: F) -> Self::From
    where
        F: FnOnce(Self::To) -> Self::To,
    {
        self.backward(&f(self.forward(from)))
    }

    /// Verifies that this isomorphism satisfies the isomorphism laws for the given values.
    ///
    /// # Arguments
    ///
    /// * `from` - A value of the source type
    /// * `to` - A value of the target type
    ///
    /// # Returns
    ///
    /// `true` if the isomorphism laws are satisfied for the given values,
    /// `false` otherwise
    fn verify_laws(&self, from: &Self::From, to: &Self::To) -> bool
    where
        Self::From: PartialEq,
        Self::To: PartialEq,
    {
        let round_trip_from = self.backward(&self.forward(from));
        let round_trip_to = self.forward(&self.backward(to));

        &round_trip_from == from && &round_trip_to == to
    }
}

// Implement IsoExt for all types that implement Iso
impl<T, A, B> IsoExt<A, B> for T where T: Iso<A, B> {}

/// An isomorphism between Result<A, E> and Validated<E, A>.
///
/// # Example
/// ```rust
/// use rustica::traits::iso::{Iso, ResultValidatedIso};
/// use rustica::datatypes::validated::Validated;
/// let iso = ResultValidatedIso;
/// let res: Result<i32, &str> = Ok(42);
/// let validated = iso.forward(&res);
/// assert_eq!(validated, Validated::valid(42));
/// let res2 = iso.backward(&validated);
/// assert_eq!(res2, Ok(42));
/// let err: Result<i32, &str> = Err("fail");
/// let validated2 = iso.forward(&err);
/// assert!(validated2.is_invalid());
/// let res3 = iso.backward(&validated2);
/// assert_eq!(res3, Err("fail"));
/// ```
pub struct ResultValidatedIso;

impl<A: Clone, E: Clone> Iso<Result<A, E>, Validated<E, A>> for ResultValidatedIso {
    type From = Result<A, E>;
    type To = Validated<E, A>;

    fn forward(&self, from: &Self::From) -> Self::To {
        Validated::from(from)
    }

    fn backward(&self, to: &Self::To) -> Self::From {
        to.clone().into_result_first_error()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[derive(Clone)]
    struct StringVecIso;

    impl Iso<String, Vec<char>> for StringVecIso {
        type From = String;
        type To = Vec<char>;

        fn forward(&self, from: &Self::From) -> Self::To {
            from.chars().collect()
        }

        fn backward(&self, to: &Self::To) -> Self::From {
            to.iter().collect()
        }
    }

    #[derive(Clone)]
    struct VecLenIso;

    impl Iso<Vec<char>, usize> for VecLenIso {
        type From = Vec<char>;
        type To = usize;

        fn forward(&self, from: &Self::From) -> Self::To {
            from.len()
        }

        fn backward(&self, to: &Self::To) -> Self::From {
            vec!['x'; *to]
        }
    }

    #[test]
    fn iso_round_trips_and_maps_functions() {
        let iso = StringVecIso;
        let text = "hello".to_owned();
        let chars = iso.forward(&text);
        assert_eq!(chars, vec!['h', 'e', 'l', 'l', 'o']);
        assert_eq!(iso.backward(&chars), text);
        assert_eq!(
            iso.map_from_target(|value: &Vec<char>| value.len())(&text),
            5
        );
        assert!(iso.map_from_source(|value: &String| value == "hello")(
            &chars
        ));
        assert!(!iso.map_from_source(|value: &String| value == "hello")(
            &vec!['w', 'o', 'r', 'l', 'd']
        ));
    }

    #[test]
    fn iso_composition_and_inverse_preserve_direction() {
        let composed = StringVecIso.iso_compose(VecLenIso);
        assert_eq!(composed.forward(&"hello".to_owned()), 5);
        assert_eq!(composed.backward(&3), "xxx");

        let inverse = StringVecIso.inverse();
        let chars = vec!['h', 'e', 'l', 'l', 'o'];
        let text = inverse.forward(&chars);
        assert_eq!(text, "hello");
        assert_eq!(inverse.backward(&text), chars);
    }

    #[test]
    fn result_validated_iso_round_trips_success_and_error() {
        let iso = ResultValidatedIso;
        let result: Result<i32, &str> = Ok(42);
        let validated = iso.forward(&result);
        assert_eq!(validated, Validated::valid(42));
        assert_eq!(iso.backward(&validated), Ok(42));

        let error: Result<i32, &str> = Err("fail");
        let invalid = iso.forward(&error);
        assert!(invalid.is_invalid());
        assert_eq!(iso.backward(&invalid), Err("fail"));
    }
}
