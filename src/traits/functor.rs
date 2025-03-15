//! # Functor
//!
//! The `Functor` module provides trait definitions for implementing functors
//! in Rust, a fundamental abstraction in functional programming.
//!
//! A functor is a type constructor that supports a mapping operation which preserves
//! the structure of the functor while transforming its contents.
//!
//! # TODO: Improvements
//! - Add full set of ownership-aware methods to optimize performance
//! - Add #[inline] attributes to all methods for better performance
//! - Improve documentation examples with explicit type annotations
//! - Add PhantomData support for zero-cost abstractions
//! - Add blanket implementations for relevant trait combinations
//! - Ensure proper trait bounds on type parameters
//! - Optimize trait bounds for better compile-time type inference
//! - Update all FunctorExt methods to use owned values instead of references when appropriate
//! - Add comprehensive test cases for all implementations
//! - Create benchmarks to evaluate performance of ownership-based vs reference-based approaches
//!
//! # Relationship to other traits
//!
//! Functors are the foundation of many higher-level abstractions in functional programming:
//!
//! ``` Text
//! Functor -> Applicative -> Monad
//! ```
//!
//! Each level adds more capabilities:
//! - Functors: Transforming values in a context (`fmap`)
//! - Applicatives: Applying functions in a context to values in a context (`apply`)
//! - Monads: Sequencing operations that return values in a context (`bind`)
//!
//! # Components
//!
//! The module contains:
//!
//! - The core `Functor` trait that defines mapping operations
//! - Extension methods in `FunctorExt` for additional utility
//! - Implementations for standard Rust types like `Option`, `Result`, and `Vec`
//! - Zero-cost implementations using `PhantomData`
//!
//! # Functor Laws
//!
//! A proper functor should satisfy the following laws:
//!
//! ```rust
//! // 1. Identity: mapping with the identity function should return an identical value
//! // f.map(x => x) ≡ f
//! let x: Option<i32> = Some(42);
//! assert_eq!(x.clone().map(|x: i32| x), x);
//!
//! // 2. Composition: mapping with f and then g should be the same as mapping with g(f(x))
//! // f.map(g).map(h) ≡ f.map(x => h(g(x)))
//! let f = |x: i32| x + 1;
//! let g = |x: i32| x * 2;
//! let x: Option<i32> = Some(1);
//!
//! let result1: Option<i32> = x.clone().map(|x| g(f(x)));
//! let result2: Option<i32> = x.clone().map(|x| g(f(x)));
//! assert_eq!(result1, result2);
//! ```

use crate::prelude::*;

/// A trait for functors, which are type constructors that support mapping over values.
///
/// In category theory, a functor is a mapping between categories that preserves
/// structure. In Rust terms, it's a type constructor that provides a way to apply
/// a function to values while preserving their structure.
///
/// # Functor Laws
///
/// Any implementation of `Functor` should satisfy these laws:
///
/// 1. Identity: `functor.fmap(|x| x) == functor`
///    Mapping the identity function over a functor should return an equivalent functor.
///
/// 2. Composition: `functor.fmap(|x| g(f(x))) == functor.fmap(f).fmap(g)`
///    Mapping a composition of functions should be the same as mapping each function in sequence.
///
/// # Examples
///
/// ```rust
/// use rustica::traits::functor::Functor;
/// use rustica::traits::hkt::HKT;
/// use rustica::traits::identity::Identity;
/// use rustica::datatypes::maybe::Maybe;
///
/// // Using the Functor implementation for Maybe
/// let maybe_int = Maybe::Just(42);
///
/// // Transform i32 to String
/// let maybe_string = maybe_int.fmap(|x: &i32| x.to_string());
/// assert_eq!(*maybe_string.value(), "42".to_string());
///
/// // Using replace to substitute values
/// let replaced = maybe_int.replace(&String::from("hello"));
/// assert_eq!(*replaced.value(), "hello");
///
/// // Using void to discard values
/// let voided = maybe_int.void();
/// assert!(matches!(voided, Maybe::Just(())));
///
/// // With empty values
/// let maybe_none = Maybe::<i32>::Nothing;
/// let mapped_none = maybe_none.fmap(|x: &i32| x.to_string());
/// assert!(mapped_none.is_nothing());
/// ```
pub trait Functor: Identity {
    /// Maps a function over the values in a functor without consuming it.
    ///
    /// This is a reference-based version of `fmap` that doesn't consume the functor.
    ///
    /// # Arguments
    ///
    /// * `f` - A function that transforms values of type `Self::Source` into type `B`
    ///
    /// # Returns
    ///
    /// A new functor containing the transformed values
    fn fmap<B, F>(&self, f: F) -> Self::Output<B>
    where
        F: Fn(&Self::Source) -> B,
        B: Clone;

    /// Maps a function over the values in a functor.
    ///
    /// This operation applies the given function to each value inside the
    /// functor, preserving the structure while transforming the contents.
    ///
    /// # Arguments
    ///
    /// * `f` - A function that transforms values of type `Self::Source` into type `B`
    ///
    /// # Returns
    ///
    /// A new functor containing the transformed value.
    fn fmap_owned<B, F>(self, f: F) -> Self::Output<B>
    where
        F: Fn(Self::Source) -> B,
        B: Clone,
        Self: Sized;

    /// Replaces all values in the functor with a constant value, without consuming it.
    ///
    /// # Arguments
    ///
    /// * `value` - A reference to the value to replace all elements with
    ///
    /// # Returns
    ///
    /// A new functor with all elements replaced by a clone of the given value
    ///
    /// # Default Implementation
    ///
    /// Uses `map` to replace all values.
    #[inline]
    fn replace<B>(&self, value: &B) -> Self::Output<B>
    where
        B: Clone,
    {
        self.fmap(|_| value.clone())
    }

    /// Replaces all values in the functor with a constant value.
    ///
    /// # Arguments
    ///
    /// * `value` - The value to replace all elements with
    ///
    /// # Returns
    ///
    /// A new functor with all elements replaced by the given value
    ///
    /// # Default Implementation
    ///
    /// Uses `map_owned` to replace all values.
    #[inline]
    fn replace_owned<B>(&self, value: B) -> Self::Output<B>
    where
        B: Clone,
        Self: Sized,
    {
        self.fmap(|_| value.clone())
    }

    /// Void functor - discards the values and replaces them with unit, without consuming the functor.
    ///
    /// # Returns
    ///
    /// A new functor with all elements replaced by ()
    ///
    /// # Default Implementation
    ///
    /// Uses `map` to replace all values with unit.
    #[inline]
    fn void(&self) -> Self::Output<()> {
        self.fmap(|_| ())
    }

    /// Void functor - discards the values and replaces them with unit.
    ///
    /// # Returns
    ///
    /// A new functor with all elements replaced by ()
    ///
    /// # Default Implementation
    ///
    /// Uses `map_owned` to replace all values with unit.
    #[inline]
    fn void_owned(self) -> Self::Output<()>
    where
        Self: Sized,
    {
        self.fmap_owned(|_| ())
    }
}

/// Extension trait for functors providing additional utility methods.
///
/// This trait extends the basic `Functor` trait with additional operations that
/// are common in functional programming but not essential to the functor concept.
///
/// # Examples
///
/// ```rust
/// use rustica::traits::functor::{Functor, FunctorExt};
/// use rustica::traits::hkt::HKT;
///
/// // Using FunctorExt methods with Option
/// let some_value: Option<i32> = Some(42);
///
/// // Using inspect to perform side effects without changing the value
/// let logged: Option<i32> = some_value.inspect(|x| {
///     println!("Value: {}", x);
/// });
/// assert_eq!(logged, Some(42));
///
/// // Using inspect_err on Result (should do nothing for Ok variant)
/// let ok_value: Result<i32, &str> = Ok(42);
/// let result = ok_value.inspect_err(|e| panic!("Should not be called for Ok: {}", e));
/// assert_eq!(result, Ok(42));
///
/// // Using filter_map to transform and potentially filter out values
/// let filter_mapped: Option<String> = some_value.filter_map(|x| {
///     if *x > 40 {
///         Some(x.to_string())
///     } else {
///         None
///     }
/// });
/// assert_eq!(filter_mapped, Some("42".to_string()));
///
/// // Working with vectors
/// let numbers: Vec<i32> = vec![1, 2, 3, 4, 5];
/// let even_squared: Vec<i32> = numbers.filter_map(|x| {
///     if x % 2 == 0 {
///         Some(x * x)
///     } else {
///         None
///     }
/// });
/// assert_eq!(even_squared, vec![4, 16]);
/// ```
pub trait FunctorExt: Functor {
    /// Transforms values with a fallible function, handling errors by providing a default value.
    ///
    /// # Arguments
    ///
    /// * `f` - A function that may fail
    /// * `default` - A default value to use in case of failure
    ///
    /// # Returns
    ///
    /// A new functor with transformed values or defaults in case of errors
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::traits::functor::{Functor, FunctorExt};
    /// use rustica::traits::hkt::HKT;
    ///
    /// let some_value: Option<i32> = Some(42);
    ///
    /// // Using try_map_or with a fallible function
    /// let result: Option<String> = some_value.try_map_or(
    ///     "default".to_string(),
    ///     |x| -> Result<String, &str> {
    ///         if *x > 0 {
    ///             Ok(x.to_string())
    ///         } else {
    ///             Err("negative number")
    ///         }
    ///     }
    /// );
    /// assert_eq!(result, Some("42".to_string()));
    ///
    /// // With a value that causes an error
    /// let negative: Option<i32> = Some(-10);
    /// let result_with_default: Option<String> = negative.try_map_or(
    ///     "default".to_string(),
    ///     |x| -> Result<String, &str> {
    ///         if *x > 0 {
    ///             Ok(x.to_string())
    ///         } else {
    ///             Err("negative number")
    ///         }
    ///     }
    /// );
    /// assert_eq!(result_with_default, Some("default".to_string()));
    /// ```
    #[inline]
    fn try_map_or<B, E, F>(&self, default: B, f: F) -> Self::Output<B>
    where
        F: Fn(&Self::Source) -> Result<B, E>,
        B: Clone,
    {
        self.fmap(|a| match f(a) {
            Ok(b) => b,
            Err(_) => default.clone(),
        })
    }

    /// Transforms values with a fallible function, handling errors with a provided function.
    ///
    /// # Arguments
    ///
    /// * `f` - A function that may fail
    /// * `default_fn` - A function that provides a default value from the error
    ///
    /// # Returns
    ///
    /// A new functor with transformed values or computed defaults in case of errors
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::traits::functor::{Functor, FunctorExt};
    /// use rustica::traits::hkt::HKT;
    ///
    /// let some_value: Option<i32> = Some(42);
    ///
    /// // Using try_map_or_else with a fallible function and error handler
    /// let result: Option<String> = some_value.try_map_or_else(
    ///     |err: &String| format!("Error: {}", err),
    ///     |x| -> Result<String, String> {
    ///         if *x > 0 {
    ///             Ok(x.to_string())
    ///         } else {
    ///             Err("negative number".to_string())
    ///         }
    ///     }
    /// );
    /// assert_eq!(result, Some("42".to_string()));
    ///
    /// // With a value that causes an error
    /// let negative: Option<i32> = Some(-10);
    /// let result_with_error_handler: Option<String> = negative.try_map_or_else(
    ///     |err: &String| format!("Error: {}", err),
    ///     |x| -> Result<String, String> {
    ///         if *x > 0 {
    ///             Ok(x.to_string())
    ///         } else {
    ///             Err("negative number".to_string())
    ///         }
    ///     }
    /// );
    /// assert_eq!(result_with_error_handler, Some("Error: negative number".to_string()));
    /// ```
    #[inline]
    fn try_map_or_else<B, E, D, F>(&self, default_fn: D, f: F) -> Self::Output<B>
    where
        F: Fn(&Self::Source) -> Result<B, E>,
        B: Clone,
        D: Fn(&E) -> B,
    {
        self.fmap(|a| match f(a) {
            Ok(b) => b,
            Err(e) => default_fn(&e),
        })
    }

    /// Transforms values with a function that might return None, filtering out None results.
    ///
    /// This combines mapping and filtering into a single operation.
    ///
    /// # Arguments
    ///
    /// * `f` - A function that returns an Option
    ///
    /// # Returns
    ///
    /// A new functor containing only the values for which the function returned Some
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::traits::functor::{Functor, FunctorExt};
    /// use rustica::traits::hkt::HKT;
    ///
    /// let some_value: Option<i32> = Some(42);
    ///
    /// // Keep only values that pass a predicate and transform them
    /// let filter_mapped: Option<String> = some_value.filter_map(|x| {
    ///     if *x > 40 {
    ///         Some(x.to_string())
    ///     } else {
    ///         None
    ///     }
    /// });
    /// assert_eq!(filter_mapped, Some("42".to_string()));
    ///
    /// // Value filtered out
    /// let filtered_out: Option<String> = some_value.filter_map(|x| {
    ///     if *x > 100 {
    ///         Some(x.to_string())
    ///     } else {
    ///         None
    ///     }
    /// });
    /// assert_eq!(filtered_out, None);
    /// ```
    fn filter_map<B, F>(&self, f: F) -> Self::Output<B>
    where
        F: Fn(&Self::Source) -> Option<B>;
}

impl<T> Functor for Vec<T> {
    #[inline]
    fn fmap<B, F>(&self, f: F) -> Self::Output<B>
    where
        F: Fn(&Self::Source) -> B,
        B: Clone,
    {
        self.iter().map(f).collect()
    }

    #[inline]
    fn fmap_owned<B, F>(self, f: F) -> Self::Output<B>
    where
        F: Fn(Self::Source) -> B,
        B: Clone,
        Self: Sized,
    {
        self.into_iter().map(f).collect()
    }
}

impl<T> FunctorExt for Vec<T> {
    #[inline]
    fn filter_map<B, F>(&self, f: F) -> Self::Output<B>
    where
        F: FnMut(&Self::Source) -> Option<B>,
    {
        self.iter().filter_map(f).collect()
    }

    #[inline]
    fn try_map_or<B, E, F>(&self, default: B, f: F) -> Self::Output<B>
    where
        F: Fn(&Self::Source) -> Result<B, E>,
        B: Clone,
    {
        self.iter()
            .map(|x| match f(x) {
                Ok(b) => b,
                Err(_) => default.clone(),
            })
            .collect()
    }

    #[inline]
    fn try_map_or_else<B, E, D, F>(&self, default_fn: D, f: F) -> Self::Output<B>
    where
        F: Fn(&Self::Source) -> Result<B, E>,
        D: Fn(&E) -> B,
    {
        self.iter()
            .map(|x| match f(x) {
                Ok(b) => b,
                Err(e) => default_fn(&e),
            })
            .collect()
    }
}

impl<T> FunctorExt for Option<T> {
    #[inline]
    fn filter_map<B, F>(&self, f: F) -> Self::Output<B>
    where
        F: FnOnce(&Self::Source) -> Option<B>,
    {
        self.as_ref().and_then(f)
    }

    #[inline]
    fn try_map_or<B, E, F>(&self, default: B, f: F) -> Self::Output<B>
    where
        F: FnOnce(&Self::Source) -> Result<B, E>,
        B: Clone,
    {
        match self {
            Some(value) => match f(value) {
                Ok(b) => Some(b),
                Err(_) => Some(default.clone()),
            },
            None => None,
        }
    }

    #[inline]
    fn try_map_or_else<B, E, D, F>(&self, default_fn: D, f: F) -> Self::Output<B>
    where
        F: FnOnce(&Self::Source) -> Result<B, E>,
        D: Fn(&E) -> B,
    {
        match self {
            Some(value) => match f(value) {
                Ok(b) => Some(b),
                Err(e) => Some(default_fn(&e)),
            },
            None => None,
        }
    }
}

impl<T, E: Debug> FunctorExt for Result<T, E>
where
    E: Clone + Default,
{
    #[inline]
    fn filter_map<B, F>(&self, f: F) -> Self::Output<B>
    where
        F: FnOnce(&Self::Source) -> Option<B>,
    {
        match self {
            Ok(value) => match f(value) {
                Some(b) => Ok(b),
                None => Err(E::default()),
            },
            Err(e) => Err(e.clone()),
        }
    }

    #[inline]
    fn try_map_or<B, E2, F>(&self, default: B, f: F) -> Self::Output<B>
    where
        F: FnOnce(&Self::Source) -> Result<B, E2>,
        B: Clone,
    {
        match self {
            Ok(value) => match f(value) {
                Ok(b) => Ok(b),
                Err(_) => Ok(default.clone()),
            },
            Err(e) => Err(e.clone()),
        }
    }

    #[inline]
    fn try_map_or_else<B, E2, D, F>(&self, default_fn: D, f: F) -> Self::Output<B>
    where
        F: FnOnce(&Self::Source) -> Result<B, E2>,
        D: Fn(&E2) -> B,
    {
        match self {
            Ok(value) => match f(value) {
                Ok(b) => Ok(b),
                Err(e) => Ok(default_fn(&e)),
            },
            Err(e) => Err(e.clone()),
        }
    }
}

use std::{fmt::Debug, marker::PhantomData};

/// PhantomData implementation of Functor, does nothing but satisfies trait bounds for Zero-cost abstractions
impl<T> Functor for PhantomData<T> {
    /// does nothing but satisfies trait bounds
    #[inline]
    fn fmap<B, F>(&self, _f: F) -> Self::Output<B>
    where
        F: Fn(&Self::Source) -> B,
        B: Clone,
    {
        PhantomData
    }

    /// does nothing but satisfies trait bounds
    #[inline]
    fn fmap_owned<B, F>(self, _f: F) -> Self::Output<B>
    where
        F: Fn(Self::Source) -> B,
        B: Clone,
        Self: Sized,
    {
        PhantomData
    }
}

/// PhantomData implementation of FunctorExt, does nothing but satisfies trait bounds for Zero-cost abstractions
impl<T> FunctorExt for PhantomData<T> {
    /// does nothing but satisfies trait bounds
    #[inline]
    fn filter_map<B, F>(&self, _f: F) -> Self::Output<B>
    where
        F: FnOnce(&Self::Source) -> Option<B>,
    {
        PhantomData
    }

    /// does nothing but satisfies trait bounds
    #[inline]
    fn try_map_or<B, E, F>(&self, _default: B, _f: F) -> Self::Output<B>
    where
        F: FnOnce(&Self::Source) -> Result<B, E>,
        B: Clone,
    {
        PhantomData
    }

    /// does nothing but satisfies trait bounds
    #[inline]
    fn try_map_or_else<B, E, D, F>(&self, _default_fn: D, _f: F) -> Self::Output<B>
    where
        F: FnOnce(&Self::Source) -> Result<B, E>,
        D: Fn(&E) -> B,
    {
        PhantomData
    }
}

impl<T> Functor for Option<T> {
    #[inline]
    fn fmap<B, F>(&self, f: F) -> Self::Output<B>
    where
        F: Fn(&Self::Source) -> B,
        B: Clone,
    {
        self.as_ref().map(f)
    }

    #[inline]
    fn fmap_owned<B, F>(self, f: F) -> Self::Output<B>
    where
        F: Fn(Self::Source) -> B,
        B: Clone,
        Self: Sized,
    {
        self.map(f)
    }
}

impl<A, E: Debug + Clone> Functor for Result<A, E> {
    #[inline]
    fn fmap<B, F>(&self, f: F) -> Self::Output<B>
    where
        F: Fn(&Self::Source) -> B,
        B: Clone,
    {
        match self {
            Ok(value) => Ok(f(value)),
            Err(e) => Err(e.clone()),
        }
    }

    #[inline]
    fn fmap_owned<B, F>(self, f: F) -> Self::Output<B>
    where
        F: Fn(Self::Source) -> B,
        B: Clone,
        Self: Sized,
    {
        match self {
            Ok(value) => Ok(f(value)),
            Err(e) => Err(e.clone()),
        }
    }
}
