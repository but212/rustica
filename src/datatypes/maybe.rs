//! The Maybe monad represents computations which may fail or return a value.
//! 
//! `Maybe<T>` is an enum that can be either `Just(T)` containing a value, or `Nothing` 
//! representing the absence of a value. This is similar to Rust's built-in `Option<T>` type,
//! but with additional monadic operations.
//! 
//! # Key Features
//! 
//! - **Failure Handling**: Represents computations that might not return a value
//! - **Short-circuiting**: Operations on `Nothing` propagate the `Nothing` value
//! - **Composition**: Chain operations together without explicit null checks
//! 
//! # Common Use Cases
//! 
//! - Representing optional values without using `null`
//! - Chaining operations that might fail
//! - Transforming optional values without unwrapping
//! 
//! # Relationship to Rust's Option
//! 
//! `Maybe<T>` is functionally equivalent to Rust's `Option<T>`, but provides
//! additional monadic operations. Conversion methods are provided to interoperate
//! with `Option<T>`.
//! 
//! # Examples
//! 
//! ```rust
//! use rustica::datatypes::maybe::Maybe;
//! use rustica::traits::functor::Functor;
//! use rustica::traits::monad::Monad;
//! 
//! // Creating Maybe values
//! let just_value = Maybe::Just(42);
//! let nothing_value: Maybe<i32> = Maybe::Nothing;
//! 
//! // Using fmap to transform the value
//! let doubled = just_value.fmap(&|x| x * 2);  // Maybe::Just(84)
//! let doubled_nothing = nothing_value.fmap(&|x| x * 2);  // Maybe::Nothing
//! 
//! // Chaining operations with bind
//! let result = just_value.bind(&|x| {
//!     if *x > 0 {
//!         Maybe::Just(x * 10)
//!     } else {
//!         Maybe::Nothing
//!     }
//! });  // Maybe::Just(420)
//! ```

use crate::traits::hkt::HKT;
use crate::traits::functor::Functor;
use crate::traits::applicative::Applicative;
use crate::traits::monad::Monad;
use crate::traits::pure::Pure;
use crate::traits::composable::Composable;
use crate::traits::identity::Identity;

/// A type that represents an optional value.
///
/// `Maybe<T>` is an enum that can be either `Just(T)` containing a value, or `Nothing` 
/// representing the absence of a value.
///
/// # Type Parameters
///
/// * `T` - The type of the value that might be contained
///
/// # Examples
///
/// ```rust
/// use rustica::datatypes::maybe::Maybe;
///
/// let just_five = Maybe::Just(5);
/// let nothing: Maybe<i32> = Maybe::Nothing;
///
/// // Pattern matching
/// match just_five {
///     Maybe::Just(x) => println!("Got a value: {}", x),
///     Maybe::Nothing => println!("Got nothing"),
/// }
/// ```
#[derive(Clone)]
pub enum Maybe<T> {
    /// Contains a value of type `T`
    Just(T),
    /// Represents the absence of a value
    Nothing,
}

impl<T> Maybe<T> {
    /// Returns `true` if the maybe value is a `Just` value.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::maybe::Maybe;
    ///
    /// let x: Maybe<u32> = Maybe::Just(2);
    /// assert_eq!(x.is_just(), true);
    ///
    /// let y: Maybe<u32> = Maybe::Nothing;
    /// assert_eq!(y.is_just(), false);
    /// ```
    pub fn is_just(&self) -> bool {
        matches!(self, Maybe::Just(_))
    }

    /// Returns `true` if the maybe value is a `Nothing` value.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::maybe::Maybe;
    ///
    /// let x: Maybe<u32> = Maybe::Just(2);
    /// assert_eq!(x.is_nothing(), false);
    ///
    /// let y: Maybe<u32> = Maybe::Nothing;
    /// assert_eq!(y.is_nothing(), true);
    /// ```
    pub fn is_nothing(&self) -> bool {
        matches!(self, Maybe::Nothing)
    }

    /// Converts from `Option<T>` to `Maybe<T>`.
    ///
    /// `Some(x)` is converted to `Just(x)`, and `None` is converted to `Nothing`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::maybe::Maybe;
    ///
    /// let opt_some = Some(42);
    /// let opt_none: Option<i32> = None;
    ///
    /// let maybe_just = Maybe::from_option(opt_some);
    /// let maybe_nothing = Maybe::from_option(opt_none);
    ///
    /// assert!(maybe_just.is_just());
    /// assert!(maybe_nothing.is_nothing());
    /// ```
    pub fn from_option(opt: Option<T>) -> Self {
        match opt {
            Some(x) => Maybe::Just(x),
            None => Maybe::Nothing,
        }
    }

    /// Converts from `Maybe<T>` to `Option<T>`.
    ///
    /// `Just(x)` is converted to `Some(x)`, and `Nothing` is converted to `None`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::maybe::Maybe;
    ///
    /// let maybe_just = Maybe::Just(42);
    /// let maybe_nothing: Maybe<i32> = Maybe::Nothing;
    ///
    /// let opt_some = maybe_just.to_option();
    /// let opt_none = maybe_nothing.to_option();
    ///
    /// assert_eq!(opt_some, Some(42));
    /// assert_eq!(opt_none, None);
    /// ```
    pub fn to_option(self) -> Option<T> {
        match self {
            Maybe::Just(x) => Some(x),
            Maybe::Nothing => None,
        }
    }

    /// Unwraps a maybe, yielding the content of a `Just`.
    ///
    /// # Panics
    ///
    /// Panics if the value is a `Nothing` with a custom panic message.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::maybe::Maybe;
    ///
    /// let x = Maybe::Just("air");
    /// assert_eq!(x.unwrap(), "air");
    /// ```
    ///
    /// ```rust,should_panic
    /// use rustica::datatypes::maybe::Maybe;
    ///
    /// let x: Maybe<&str> = Maybe::Nothing;
    /// x.unwrap(); // This will panic
    /// ```
    pub fn unwrap(self) -> T {
        match self {
            Maybe::Just(x) => x,
            Maybe::Nothing => panic!("Tried to unwrap a Nothing value!"),
        }
    }
}

/// Implementation of Higher-Kinded Type trait for Maybe
impl<T> HKT for Maybe<T> {
    type Source = T;
    type Output<U> = Maybe<U>;
}

/// Implementation of Pure trait for Maybe
///
/// The `pure` function lifts a value into the Maybe context.
impl<T> Pure for Maybe<T> {
    /// Wraps a value in a `Just` constructor.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::maybe::Maybe;
    /// use rustica::traits::pure::Pure;
    ///
    /// let just_int = Maybe::<i32>::pure(42);
    /// assert!(just_int.is_just());
    /// ```
    fn pure<U>(value: U) -> Self::Output<U> {
        Maybe::Just(value)
    }
}

/// Implementation of Functor trait for Maybe
///
/// The functor instance for Maybe allows mapping a function over a Maybe value.
/// If the Maybe is `Just(x)`, it applies the function to `x` and returns `Just(f(x))`.
/// If the Maybe is `Nothing`, it returns `Nothing`.
impl<T> Functor for Maybe<T> {
    /// Maps a function over the contained value.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::maybe::Maybe;
    /// use rustica::traits::functor::Functor;
    ///
    /// let just_five = Maybe::Just(5);
    /// let nothing: Maybe<i32> = Maybe::Nothing;
    ///
    /// let just_six = just_five.fmap(&|x| x + 1);
    /// let still_nothing = nothing.fmap(&|x| x + 1);
    ///
    /// match just_six {
    ///     Maybe::Just(x) => assert_eq!(x, 6),
    ///     Maybe::Nothing => panic!("Expected Just, got Nothing"),
    /// }
    ///
    /// assert!(still_nothing.is_nothing());
    /// ```
    fn fmap<U>(&self, f: &dyn Fn(&Self::Source) -> U) -> Self::Output<U> {
        match self {
            Maybe::Just(x) => Maybe::Just(f(x)),
            Maybe::Nothing => Maybe::Nothing,
        }
    }
}

/// Implementation of Applicative trait for Maybe
///
/// The applicative instance for Maybe allows applying a function wrapped in a Maybe
/// to a value wrapped in a Maybe.
impl<T> Applicative for Maybe<T> {
    /// Applies a function in a Maybe context to a value in a Maybe context.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::maybe::Maybe;
    /// use rustica::traits::applicative::Applicative;
    ///
    /// let just_five = Maybe::Just(5);
    /// let add_one = Maybe::Just(|x: &i32| x + 1);
    ///
    /// let result = just_five.apply(&add_one);
    /// match result {
    ///     Maybe::Just(x) => assert_eq!(x, 6),
    ///     Maybe::Nothing => panic!("Expected Just, got Nothing"),
    /// }
    /// ```
    fn apply<B, F>(&self, f: &Self::Output<F>) -> Self::Output<B>
        where
            F: Fn(&Self::Source) -> B {
        match (self, f) {
            (Maybe::Just(x), Maybe::Just(f)) => Maybe::Just(f(x)),
            _ => Maybe::Nothing,
        }
    }

    /// Applies a binary function to two Maybe values.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::maybe::Maybe;
    /// use rustica::traits::applicative::Applicative;
    ///
    /// let just_five = Maybe::Just(5);
    /// let just_ten = Maybe::Just(10);
    ///
    /// let result = just_five.lift2(&just_ten, &|x, y| x + y);
    /// match result {
    ///     Maybe::Just(x) => assert_eq!(x, 15),
    ///     Maybe::Nothing => panic!("Expected Just, got Nothing"),
    /// }
    /// ```
    fn lift2<B, C>(&self, b: &Self::Output<B>, f: &dyn Fn(&Self::Source, &B) -> C) -> Self::Output<C> {
        match (self, b) {
            (Maybe::Just(x), Maybe::Just(b)) => Maybe::Just(f(x, b)),
            _ => Maybe::Nothing,
        }
    }

    /// Applies a ternary function to three Maybe values.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::maybe::Maybe;
    /// use rustica::traits::applicative::Applicative;
    ///
    /// let just_five = Maybe::Just(5);
    /// let just_ten = Maybe::Just(10);
    /// let just_two = Maybe::Just(2);
    ///
    /// let result = just_five.lift3(&just_ten, &just_two, &|x, y, z| x * y + z);
    /// match result {
    ///     Maybe::Just(x) => assert_eq!(x, 52),  // 5 * 10 + 2 = 52
    ///     Maybe::Nothing => panic!("Expected Just, got Nothing"),
    /// }
    /// ```
    fn lift3<B, C, D>(&self, b: &Self::Output<B>, c: &Self::Output<C>, f: &dyn Fn(&Self::Source, &B, &C) -> D) -> Self::Output<D> {
        match (self, b, c) {
            (Maybe::Just(x), Maybe::Just(b), Maybe::Just(c)) => Maybe::Just(f(x, b, c)),
            _ => Maybe::Nothing,
        }
    }
}

/// Implementation of Monad trait for Maybe
///
/// The monad instance for Maybe allows sequencing operations that might fail.
impl<T> Monad for Maybe<T> {
    /// Applies a function that returns a Maybe to the contained value.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::maybe::Maybe;
    /// use rustica::traits::monad::Monad;
    ///
    /// let just_five = Maybe::Just(5);
    ///
    /// // A function that returns Maybe
    /// let safe_div = |x: &i32| {
    ///     if *x == 0 {
    ///         Maybe::Nothing
    ///     } else {
    ///         Maybe::Just(10 / x)
    ///     }
    /// };
    ///
    /// let result = just_five.bind(&safe_div);
    /// match result {
    ///     Maybe::Just(x) => assert_eq!(x, 2),  // 10 / 5 = 2
    ///     Maybe::Nothing => panic!("Expected Just, got Nothing"),
    /// }
    /// ```
    fn bind<U>(&self, f: &dyn Fn(&Self::Source) -> Self::Output<U>) -> Self::Output<U> {
        match self {
            Maybe::Just(x) => f(x),
            Maybe::Nothing => Maybe::Nothing,
        }
    }

    /// Flattens a nested Maybe.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::maybe::Maybe;
    /// use rustica::traits::monad::Monad;
    ///
    /// let nested = Maybe::Just(Maybe::Just(5));
    /// let flattened = nested.join();
    ///
    /// match flattened {
    ///     Maybe::Just(x) => assert_eq!(x, 5),
    ///     Maybe::Nothing => panic!("Expected Just, got Nothing"),
    /// }
    /// ```
    fn join<U>(&self) -> Self::Output<U>
        where
            T: Clone + Into<Self::Output<U>> {
        match self {
            Maybe::Just(x) => x.clone().into(),
            Maybe::Nothing => Maybe::Nothing,
        }
    }
}

/// Implementation of FromIterator trait for Maybe
///
/// This allows collecting an iterator into a Maybe value.
impl<T> FromIterator<T> for Maybe<T> {
    /// Creates a Maybe from an iterator.
    ///
    /// Returns `Just` with the first element, or `Nothing` if the iterator is empty.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::maybe::Maybe;
    ///
    /// let v = vec![1, 2, 3];
    /// let maybe: Maybe<i32> = v.into_iter().collect();
    /// assert!(maybe.is_just());
    ///
    /// let empty: Vec<i32> = vec![];
    /// let maybe_empty: Maybe<i32> = empty.into_iter().collect();
    /// assert!(maybe_empty.is_nothing());
    /// ```
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        let mut iter = iter.into_iter();
        iter.next().map_or(Maybe::Nothing, Maybe::Just)
    }
}

/// Implementation of From trait for converting from Option to Maybe
impl<T> From<Option<T>> for Maybe<T> {
    /// Converts an Option into a Maybe.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::maybe::Maybe;
    ///
    /// let opt_some = Some(42);
    /// let maybe_just = Maybe::from(opt_some);
    /// assert!(maybe_just.is_just());
    ///
    /// let opt_none: Option<i32> = None;
    /// let maybe_nothing = Maybe::from(opt_none);
    /// assert!(maybe_nothing.is_nothing());
    /// ```
    fn from(opt: Option<T>) -> Self {
        match opt {
            Some(value) => Maybe::Just(value),
            None => Maybe::Nothing,
        }
    }
}

/// Implementation of Identity trait for Maybe
impl<T> Identity for Maybe<T> {
    /// Gets a reference to the contained value.
    ///
    /// # Panics
    ///
    /// Panics if the value is `Nothing`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::maybe::Maybe;
    /// use rustica::traits::identity::Identity;
    ///
    /// let just_five = Maybe::Just(5);
    /// assert_eq!(*just_five.value(), 5);
    /// ```
    fn value(&self) -> &Self::Source {
        match self {
            Maybe::Just(x) => x,
            Maybe::Nothing => panic!("Tried to get value from Nothing!"),
        }
    }
}

/// Implementation of Composable trait for Maybe
impl<T> Composable for Maybe<T> {
    /// Composes two functions.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::maybe::Maybe;
    /// use rustica::prelude::*;
    ///
    /// let add_one = |x: i32| x + 1;
    /// let double = |x: i32| x * 2;
    /// let composed = Maybe::<i32>::compose(&add_one, &double);
    ///
    /// let result = Maybe::Just(5).fmap(&|x| composed(*x));
    /// assert!(result.is_just());
    /// assert_eq!(result.unwrap(), 12);  // (5 + 1) * 2 = 12
    /// ```
    fn compose<U, V>(f: &dyn Fn(Self::Source) -> U, g: &dyn Fn(U) -> V) -> impl Fn(Self::Source) -> V {
        move |x| g(f(x))
    }
}