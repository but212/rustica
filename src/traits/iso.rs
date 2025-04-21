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

use crate::prelude::{Either, Validated};
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
/// # Examples
///
/// Creating an isomorphism between a newtype and its inner value:
///
/// ```rust
/// use rustica::traits::iso::Iso;
///
/// // A newtype wrapper
/// struct UserId(u64);
///
/// // Isomorphism between UserId and u64
/// struct UserIdIso;
///
/// impl Iso<UserId, u64> for UserIdIso {
///     type From = UserId;
///     type To = u64;
///
///     fn forward(&self, from: &Self::From) -> Self::To {
///         from.0
///     }
///
///     fn backward(&self, to: &Self::To) -> Self::From {
///         UserId(*to)
///     }
/// }
///
/// let iso = UserIdIso;
/// let user_id = UserId(123);
/// let id_num = iso.forward(&user_id);
/// assert_eq!(id_num, 123);
///
/// let user_id2 = iso.backward(&id_num);
/// assert_eq!(user_id2.0, user_id.0);
/// ```
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
    /// # Examples
    ///
    /// ```rust
    /// use rustica::traits::iso::Iso;
    ///
    /// struct StringVecIso;
    ///
    /// impl Iso<String, Vec<char>> for StringVecIso {
    ///     type From = String;
    ///     type To = Vec<char>;
    ///
    ///     fn forward(&self, from: &Self::From) -> Self::To {
    ///         from.chars().collect()
    ///     }
    ///
    ///     fn backward(&self, to: &Self::To) -> Self::From {
    ///         to.iter().collect()
    ///     }
    /// }
    ///
    /// let text = String::from("hello");
    /// let chars = StringVecIso.forward(&text);
    /// assert_eq!(chars, vec!['h', 'e', 'l', 'l', 'o']);
    /// ```
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
    /// # Examples
    ///
    /// ```rust
    /// use rustica::traits::iso::Iso;
    ///
    /// struct StringVecIso;
    ///
    /// impl Iso<String, Vec<char>> for StringVecIso {
    ///     type From = String;
    ///     type To = Vec<char>;
    ///
    ///     fn forward(&self, from: &Self::From) -> Self::To {
    ///         from.chars().collect()
    ///     }
    ///
    ///     fn backward(&self, to: &Self::To) -> Self::From {
    ///         to.iter().collect()
    ///     }
    /// }
    ///
    /// let chars = vec!['h', 'e', 'l', 'l', 'o'];
    /// let text = StringVecIso.backward(&chars);
    /// assert_eq!(text, "hello");
    /// ```
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
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::traits::iso::Iso;
    ///
    /// struct StringVecIso;
    ///
    /// impl Iso<String, Vec<char>> for StringVecIso {
    ///     type From = String;
    ///     type To = Vec<char>;
    ///
    ///     fn forward(&self, from: &Self::From) -> Self::To {
    ///         from.chars().collect()
    ///     }
    ///
    ///     fn backward(&self, to: &Self::To) -> Self::From {
    ///         to.iter().collect()
    ///     }
    /// }
    ///
    /// // Create a function that counts elements in the target type (Vec<char>)
    /// let count_chars = |chars: &Vec<char>| chars.len();
    ///
    /// // Convert it to operate on the source type (String)
    /// let count_string_chars = StringVecIso.map_from_target(count_chars);
    ///
    /// // Use the converted function
    /// assert_eq!(count_string_chars(&"hello".to_string()), 5);
    /// ```
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
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::traits::iso::Iso;
    ///
    /// struct StringVecIso;
    ///
    /// impl Iso<String, Vec<char>> for StringVecIso {
    ///     type From = String;
    ///     type To = Vec<char>;
    ///
    ///     fn forward(&self, from: &Self::From) -> Self::To {
    ///         from.chars().collect()
    ///     }
    ///
    ///     fn backward(&self, to: &Self::To) -> Self::From {
    ///         to.iter().collect()
    ///     }
    /// }
    ///
    /// // Create a function that operates on the source type (String)
    /// let is_hello = |s: &String| s == "hello";
    ///
    /// // Convert it to operate on the target type (Vec<char>)
    /// let is_hello_vec = StringVecIso.map_from_source(is_hello);
    ///
    /// // Use the converted function
    /// assert!(is_hello_vec(&vec!['h', 'e', 'l', 'l', 'o']));
    /// assert!(!is_hello_vec(&vec!['w', 'o', 'r', 'l', 'd']));
    /// ```
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
    /// # Examples
    ///
    /// ```rust
    /// use rustica::traits::iso::Iso;
    ///
    /// // Isomorphism between String and Vec<char>
    /// #[derive(Clone)]
    /// struct StringVecIso;
    /// impl Iso<String, Vec<char>> for StringVecIso {
    ///     type From = String;
    ///     type To = Vec<char>;
    ///
    ///     fn forward(&self, from: &Self::From) -> Self::To {
    ///         from.chars().collect()
    ///     }
    ///
    ///     fn backward(&self, to: &Self::To) -> Self::From {
    ///         to.iter().collect()
    ///     }
    /// }
    ///
    /// // Isomorphism between Vec<char> and String length
    /// #[derive(Clone)]
    /// struct VecLenIso;
    /// impl Iso<Vec<char>, usize> for VecLenIso {
    ///     type From = Vec<char>;
    ///     type To = usize;
    ///
    ///     fn forward(&self, from: &Self::From) -> Self::To {
    ///         from.len()
    ///     }
    ///
    ///     fn backward(&self, to: &Self::To) -> Self::From {
    ///         vec!['x'; *to]
    ///     }
    /// }
    ///
    /// // Compose the two isomorphisms
    /// let string_to_len = StringVecIso.iso_compose(VecLenIso);
    ///
    /// let s = String::from("hello");
    /// assert_eq!(string_to_len.forward(&s), 5);
    ///
    /// let len = 3;
    /// assert_eq!(string_to_len.backward(&len), "xxx");
    /// ```
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
            phantom: PhantomData,
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
    /// # Examples
    ///
    /// ```rust
    /// use rustica::traits::iso::Iso;
    ///
    /// // A newtype wrapper
    /// #[derive(Clone)]
    /// struct UserId(u64);
    ///
    /// // Isomorphism between UserId and u64
    /// #[derive(Clone)]
    /// struct UserIdIso;
    ///
    /// impl Iso<UserId, u64> for UserIdIso {
    ///     type From = UserId;
    ///     type To = u64;
    ///
    ///     fn forward(&self, from: &Self::From) -> Self::To {
    ///         from.0
    ///     }
    ///
    ///     fn backward(&self, to: &Self::To) -> Self::From {
    ///         UserId(*to)
    ///     }
    /// }
    ///
    /// let iso = UserIdIso;
    /// let inverse = iso.inverse();
    ///
    /// let num = 42u64;
    /// let user_id = inverse.forward(&num);  // Converts u64 to UserId
    /// assert_eq!(user_id.0, 42);
    ///
    /// let original = inverse.backward(&user_id);  // Converts UserId back to u64
    /// assert_eq!(original, 42);
    /// ```
    fn inverse(&self) -> InverseIso<Self, A, B>
    where
        Self: Sized + Clone,
    {
        InverseIso {
            original: self.clone(),
            phantom: PhantomData,
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
/// # Examples
///
/// ```rust
/// use rustica::traits::iso::Iso;
///
/// // Define isomorphisms for string <-> chars and chars <-> bytes
/// #[derive(Clone)]
/// struct StringCharsIso;
/// #[derive(Clone)]
/// struct CharsBytesIso;
///
/// impl Iso<String, Vec<char>> for StringCharsIso {
///     type From = String;
///     type To = Vec<char>;
///
///     fn forward(&self, from: &String) -> Vec<char> {
///         from.chars().collect()
///     }
///
///     fn backward(&self, to: &Vec<char>) -> String {
///         to.iter().collect()
///     }
/// }
///
/// impl Iso<Vec<char>, Vec<u8>> for CharsBytesIso {
///     type From = Vec<char>;
///     type To = Vec<u8>;
///
///     fn forward(&self, from: &Vec<char>) -> Vec<u8> {
///         from.iter().map(|&c| c as u8).collect()
///     }
///
///     fn backward(&self, to: &Vec<u8>) -> Vec<char> {
///         to.iter().map(|&b| b as char).collect()
///     }
/// }
///
/// // Compose the isomorphisms
/// let string_iso = StringCharsIso;
/// let bytes_iso = CharsBytesIso;
/// let composed = string_iso.iso_compose(bytes_iso);
///
/// // Use the composed isomorphism
/// let s = "Hello".to_string();
/// let bytes = composed.forward(&s);
/// let original = composed.backward(&bytes);
/// assert_eq!(original, s);
/// ```
pub struct ComposedIso<ISO1, ISO2, A, B, C>
where
    ISO1: Iso<A, B>,
    ISO2: Iso<B, C>,
{
    pub first: ISO1,
    pub second: ISO2,
    pub phantom: PhantomData<(A, B, C)>,
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
/// # Examples
///
/// ```rust
/// use rustica::traits::iso::Iso;
/// use std::marker::PhantomData;
///
/// // Define an isomorphism between String and Vec<char>
/// #[derive(Clone)]
/// struct StringVecIso;
///
/// impl Iso<String, Vec<char>> for StringVecIso {
///     type From = String;
///     type To = Vec<char>;
///
///     fn forward(&self, from: &Self::From) -> Self::To {
///         from.chars().collect()
///     }
///
///     fn backward(&self, to: &Self::To) -> Self::From {
///         to.iter().collect()
///     }
/// }
///
/// // Create and use the inverse isomorphism
/// let iso = StringVecIso;
/// let inverse = iso.inverse();
///
/// let chars = vec!['h', 'e', 'l', 'l', 'o'];
/// let string = inverse.forward(&chars);
/// assert_eq!(string, "hello");
///
/// let chars2 = inverse.backward(&string);
/// assert_eq!(chars, chars2);
/// ```
pub struct InverseIso<ISO, A, B>
where
    ISO: Iso<A, B>,
{
    original: ISO,
    phantom: PhantomData<(A, B)>,
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

/// An isomorphism between Result<R, L> and Either<L, R>.
///
/// # Example
/// ```rust
/// use rustica::traits::iso::{Iso, ResultEitherIso};
/// use rustica::prelude::Either;
/// let iso = ResultEitherIso;
/// let res: Result<i32, &str> = Ok(7);
/// let either = iso.forward(&res);
/// assert_eq!(either, Either::right(7));
/// let res2 = iso.backward(&either);
/// assert_eq!(res2, Ok(7));
/// let err: Result<i32, &str> = Err("fail");
/// let either2 = iso.forward(&err);
/// assert_eq!(either2, Either::left("fail"));
/// let res3 = iso.backward(&either2);
/// assert_eq!(res3, Err("fail"));
/// ```
pub struct ResultEitherIso;

impl<R: Clone, L: Clone> Iso<Result<R, L>, Either<L, R>> for ResultEitherIso {
    type From = Result<R, L>;
    type To = Either<L, R>;

    fn forward(&self, from: &Self::From) -> Self::To {
        Either::from_result(from.clone())
    }

    fn backward(&self, to: &Self::To) -> Self::From {
        to.clone().to_result()
    }
}

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
        Validated::from_result(from)
    }

    fn backward(&self, to: &Self::To) -> Self::From {
        to.to_result()
    }
}
