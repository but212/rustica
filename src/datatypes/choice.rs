//! # Choice (`Choice<T>`)
//!
//! The `Choice<T>` datatype represents a primary value along with a list of alternative values,
//! all of type `T`. It's designed for scenarios where you need to manage a preferred option
//! while keeping other possibilities available. `Choice` is particularly useful in contexts like
//! configuration management, user preference handling, or any situation involving fallback mechanisms.
//!
//! ## Quick Start
//!
//! Manage preferences with fallback options:
//!
//! ```rust
//! use rustica::datatypes::choice::Choice;
//! use rustica::traits::functor::Functor;
//! use rustica::traits::monad::Monad;
//!
//! // Create a choice with primary value and alternatives
//! let servers = Choice::new("primary.example.com".to_string(),
//!     vec!["backup1.example.com".to_string(), "backup2.example.com".to_string()]);
//!
//! // Access the primary value
//! assert_eq!(servers.first(), Some(&"primary.example.com".to_string()));
//!
//! // Get all alternatives
//! assert_eq!(servers.alternatives().len(), 2);
//!
//! // Transform all values with fmap
//! let urls = servers.fmap(|host| format!("https://{}/api", host));
//! assert_eq!(urls.first(), Some(&"https://primary.example.com/api".to_string()));
//!
//! // Use bind to chain dependent choices
//! let ports = Choice::new(443, vec![8443]);
//! let connections = servers.bind(|host| ports.fmap(|port| format!("{}:{}", host, port)));
//!
//! assert_eq!(connections.first(), Some(&"primary.example.com:443".to_string()));
//! assert!(connections.alternatives().contains(&"primary.example.com:8443".to_string()));
//! ```
//!
//! ## Functional Programming Context
//!
//! In functional programming, `Choice<T>` represents a non-deterministic computation with a preferred result.
//! Key functional programming aspects include:
//!
//! - **Non-determinism**: Encapsulates multiple potential values, making it useful for representing
//!   computations with several possible outcomes.
//! - **Preference Hierarchy**: Unlike the more common `List` type, `Choice` distinguishes a primary value,
//!   establishing a clear preference order among the possibilities.
//! - **Monadic Sequencing**: Allows chaining of operations where subsequent computations depend on
//!   the result of earlier ones, with alternative values propagating through the computation chain.
//!
//! Similar structures in other functional languages include:
//!
//! - `NonEmptyList` in Haskell and Scala (though with less emphasis on preference)
//! - `OneOf` types in various FP libraries
//! - `Alt` in some JavaScript FP libraries like Sanctuary or Folktale
//! - Stream processing libraries that prioritize certain values
//!
//! ## Core Concepts
//!
//! - **Primary Value**: The main, preferred value. Accessed via `first()`.
//! - **Alternatives**: A sequence of secondary values. Accessed via `alternatives()`.
//! - **Immutability and Value Semantics**: `Choice` instances use value semantics. Operations that modify
//!   a `Choice` (e.g., adding alternatives, filtering) return a new `Choice` instance.
//!   Internally, `Choice` uses `SmallVec<[T; 8]>` to store values efficiently.
//!   For small collections (≤8 items), values are stored inline on the stack,
//!   avoiding heap allocations and providing excellent cache locality.
//! - **Type Class Implementations**: `Choice` implements standard functional typeclasses like
//!   `Functor`, `Applicative`, and `Monad`, allowing for powerful and expressive data transformations.
//!
//! ## Basic Usage
//!
//! ```rust
//! use rustica::prelude::*;
//! use rustica::datatypes::choice::Choice;
//!
//! // Create a Choice with a primary value and alternatives
//! let choice = Choice::new(10, vec![20, 30, 40]);
//!
//! // Access the primary value
//! assert_eq!(choice.first(), Some(&10));
//!
//! // Access all values (primary followed by alternatives)
//! let all_values: Vec<&i32> = choice.iter().collect();
//! assert_eq!(all_values, vec![&10, &20, &30, &40]);
//!
//! // Transform values using fmap (Functor implementation)
//! let doubled = choice.fmap(|x| x * 2);
//! assert_eq!(doubled.first(), Some(&20));
//!
//! // Add more alternatives
//! let extended = choice.clone().add_alternatives(vec![50, 60]);
//! assert_eq!(extended.alternatives().len(), 5); // Now has 5 alternatives
//!
//! // Filter values
//! // Filter values (alternatives only)
//! let filtered_alts = choice.clone().filter(|&x| x < 35);
//! assert_eq!(filtered_alts.first(), Some(&10)); // Primary is preserved
//! assert_eq!(filtered_alts.alternatives(), &[20, 30]);
//!
//! // Filter all values (primary and alternatives)
//! let filtered_all = choice.filter_values(|&x| x > 25);
//! assert_eq!(filtered_all.first(), Some(&30)); // First value that passes the predicate
//! ```
//!
//! ## Advanced Usage Patterns
//!
//! ### Monadic Chaining
//! `Choice` can be used in monadic sequences. For example, to safely extract and transform data:
//!
//! ```rust
//! use rustica::prelude::*;
//! use rustica::datatypes::choice::Choice;
//!
//! // Create a Choice with user data
//! let user = Choice::new("user123".to_string(), vec!["user456".to_string(), "user789".to_string()]);
//!
//! // Chain operations that might fail
//! let processed = user
//!     .bind(|name| {
//!         // Verify username is valid
//!         if name.len() >= 5 {
//!             Choice::new(name.clone(), vec![])
//!         } else {
//!             // If primary fails, alternatives will be tried
//!             Choice::new_empty()
//!         }
//!     })
//!     .bind(|name| {
//!         // Add prefix to username
//!         Choice::new(format!("verified_{name}", ), vec![])
//!     });
//!
//! assert_eq!(*processed.first().unwrap(), "verified_user123");
//! ```
//!
//! ## Type Class Implementations
//!
//! `Choice<T>` implements several important functional programming type classes:
//!
//! - **Functor**: Transforms the values inside the `Choice` container with `fmap`
//! - **Applicative**: Allows applying functions wrapped in a `Choice` to values in another `Choice`
//! - **Monad**: Enables sequencing operations where each depends on the result of the previous one
//! - **Semigroup** and **Monoid**: When `T` implements these type classes, `Choice<T>` does too
//!
//! ## Type Class Laws
//!
//! `Choice` adheres to standard functional programming laws:
//!
//! ### Functor Laws
//! - Identity: `fmap id = id` (mapping identity function preserves the original value)
//! - Composition: `fmap (f . g) = fmap f . fmap g` (mapping composed functions equals sequential mapping)
//!
//! ### Applicative Laws
//! - Identity: `pure id <*> v = v` (applying pure identity function preserves the value)
//! - Homomorphism: `pure f <*> pure x = pure (f x)` (applying pure function to pure value equals pure result)
//! - Interchange: `u <*> pure y = pure ($ y) <*> u` (applying functions to pure values can be reordered)
//! - Composition: `pure (.) <*> u <*> v <*> w = u <*> (v <*> w)` (composition of function application is associative)
//!
//! ### Monad Laws
//! - Left Identity: `pure a >>= f = f a` (binding pure value with function equals direct function application)
//! - Right Identity: `m >>= pure = m` (binding with pure preserves the original value)
//! - Associativity: `(m >>= f) >>= g = m >>= (\x -> f x >>= g)` (nested bindings can be flattened)
//!
//! See individual function documentation (e.g., `fmap`, `apply`, `bind`) for specific examples demonstrating these laws.
//! The `Choice` type provides several advanced operations such as:
//! - Filtering alternatives based on predicates
//! - Flattening nested choices
//! - Converting between collections and choices
//! - Monadic operations for sequencing computations
use quickcheck::{Arbitrary, Gen};
use std::fmt::{Debug, Display, Formatter};
use std::hash::Hash;
use std::iter::FromIterator;

use smallvec::SmallVec;

use crate::prelude::traits::*;

/// A type representing a value with multiple alternatives.
///
/// `Choice<T>` encapsulates a collection of values of type `T`. This structure is useful
/// in scenarios where multiple options or choices need to be represented and manipulated.
///
/// # Type Parameters
///
/// * `T`: The type of the values stored in this `Choice`.
///
/// # Fields
///
/// * `values`: An internal collection containing all the values of type `T`.
///   The first element represents the primary value, and the rest are alternatives.
#[repr(transparent)]
#[cfg_attr(feature = "serde", derive(serde::Serialize, serde::Deserialize))]
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Choice<T> {
    values: SmallVec<[T; 8]>,
}

impl<T> Choice<T> {
    /// Creates a new empty `Choice`.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::datatypes::choice::Choice;
    ///
    /// let empty: Choice<i32> = Choice::new_empty();
    /// assert!(empty.is_empty());
    /// ```
    #[inline]
    pub fn new_empty() -> Self {
        Self {
            values: SmallVec::new(),
        }
    }

    /// Creates a new `Choice` with a primary value and alternatives.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::datatypes::choice::Choice;
    ///
    /// // Create with a primary value and alternatives
    /// let choice = Choice::new(1, vec![2, 3, 4]);
    /// assert_eq!(choice.first(), Some(&1));
    /// assert_eq!(choice.alternatives(), &[2, 3, 4]);
    /// assert_eq!(choice.len(), 4);
    ///
    /// // Create with empty alternatives
    /// let single: Choice<&str> = Choice::new("primary", Vec::<&str>::new());
    /// assert_eq!(single.first(), Some(&"primary"));
    /// assert!(single.alternatives().is_empty());
    ///
    /// // Create with a different type
    /// let string_choice = Choice::new("hello".to_string(), vec!["world".to_string()]);
    /// assert_eq!(string_choice.first(), Some(&"hello".to_string()));
    /// ```
    #[inline]
    pub fn new<I>(item: T, alternatives: I) -> Self
    where
        I: IntoIterator<Item = T>,
        I::IntoIter: Iterator,
    {
        let alternatives_iter = alternatives.into_iter();
        let (lower, upper) = alternatives_iter.size_hint();

        // Optimize capacity based on size hints
        let capacity = match upper {
            Some(exact) if exact == lower => exact + 1, // Exact size known
            Some(upper_bound) if upper_bound <= 8 => upper_bound + 1, // Fits in SmallVec inline
            _ => std::cmp::max(lower + 1, 8),           // Use lower bound or SmallVec capacity
        };

        let mut values = SmallVec::<[T; 8]>::with_capacity(capacity);
        values.push(item);
        values.extend(alternatives_iter);

        Self { values }
    }

    /// Returns a reference to the primary value of the `Choice`.
    ///
    /// The primary value is the first item provided when the `Choice` was created
    /// or the first item remaining after operations like `filter_values`.
    ///
    /// # Returns
    ///
    /// An `Option<&T>`:
    /// - `Some(&T)` containing a reference to the primary value if the `Choice` is not empty.
    /// - `None` if the `Choice` is empty (e.g., created with `Choice::new_empty()`).
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::datatypes::choice::Choice;
    ///
    /// let choice = Choice::new(10, vec![20, 30]);
    /// assert_eq!(choice.first(), Some(&10));
    ///
    /// let single_choice: Choice<i32> = Choice::new(100, Vec::<i32>::new());
    /// assert_eq!(single_choice.first(), Some(&100));
    ///
    /// let empty_choice: Choice<i32> = Choice::new_empty();
    /// assert_eq!(empty_choice.first(), None);
    /// ```
    ///
    /// # See Also
    /// - [`alternatives`](Self::alternatives) - To get the non-primary values.
    /// - [`is_empty`](Self::is_empty) - To check if the `Choice` has any values.
    #[inline]
    pub fn first(&self) -> Option<&T> {
        self.values.first()
    }

    /// Returns a slice containing all alternative values of the `Choice`.
    ///
    /// Alternatives are all items in the `Choice` except for the primary value.
    /// They are returned in their stored order.
    ///
    /// # Returns
    ///
    /// A slice `&[T]`:
    /// - Contains all alternative values if any exist.
    /// - An empty slice if the `Choice` has no alternatives (i.e., only a primary value) or is empty.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::datatypes::choice::Choice;
    ///
    /// let choice = Choice::new(10, vec![20, 30, 40]);
    /// assert_eq!(choice.alternatives(), &[20, 30, 40]);
    ///
    /// let choice_with_one_alt = Choice::new(100, vec![200]);
    /// assert_eq!(choice_with_one_alt.alternatives(), &[200]);
    ///
    /// let choice_no_alts = Choice::new(100, Vec::<i32>::new());
    /// assert_eq!(choice_no_alts.alternatives(), &[]);
    ///
    /// let empty_choice: Choice<i32> = Choice::new_empty();
    /// assert_eq!(empty_choice.alternatives(), &[]);
    /// ```
    ///
    /// # See Also
    /// - [`first`](Self::first) - To get the primary value.
    /// - [`len`](Self::len) - To get the total count of items.
    /// - [`is_empty`](Self::is_empty) - To check if the Choice is empty.
    #[inline]
    pub fn alternatives(&self) -> &[T] {
        // Return empty slice if no alternatives exist
        if self.values.len() <= 1 {
            &[]
        } else {
            &self.values[1..]
        }
    }

    /// Checks if the `Choice` has any alternative values.
    #[deprecated(
        since = "0.11.0",
        note = "Use `alternatives().is_empty()` instead. Will be removed in v0.12.0"
    )]
    pub fn has_alternatives(&self) -> bool {
        self.values.len() > 1
    }

    /// Returns the total number of values in the `Choice`, including the primary value and all alternatives.
    ///
    /// # Returns
    ///
    /// The count of all values (primary + alternatives) as `usize`.
    /// Returns `0` for an empty `Choice`.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::datatypes::choice::Choice;
    ///
    /// let choice = Choice::new(10, vec![20, 30, 40]);
    /// assert_eq!(choice.len(), 4); // 1 primary + 3 alternatives
    ///
    /// let single_choice = Choice::new(100, Vec::<i32>::new());
    /// assert_eq!(single_choice.len(), 1); // 1 primary + 0 alternatives
    ///
    /// let empty_choice: Choice<i32> = Choice::new_empty();
    /// assert_eq!(empty_choice.len(), 0);
    /// ```
    ///
    /// # See Also
    /// - [`is_empty`](Self::is_empty) - To check if length is zero.
    /// - [`has_alternatives`](Self::has_alternatives) - To check if there are more than just the primary value.
    #[inline]
    pub fn len(&self) -> usize {
        self.values.len()
    }

    /// Checks if the `Choice` is empty (contains no values).
    ///
    /// An empty `Choice` has no primary value and no alternatives.
    /// This can occur if `Choice::new_empty()` is used or if all values
    /// are filtered out.
    ///
    /// # Returns
    ///
    /// `true` if the `Choice` contains no values, `false` otherwise.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::datatypes::choice::Choice;
    ///
    /// let empty_choice: Choice<i32> = Choice::new_empty();
    /// assert!(empty_choice.is_empty());
    ///
    /// let non_empty_choice = Choice::new(1, vec![2, 3]);
    /// assert!(!non_empty_choice.is_empty());
    ///
    /// let single_value_choice = Choice::new(42, Vec::<i32>::new());
    /// assert!(!single_value_choice.is_empty());
    /// ```
    ///
    /// # See Also
    /// - [`len`](Self::len) - To get the total number of items.
    /// - [`new_empty`](Self::new_empty) - To create an empty `Choice`.
    /// - [`first`](Self::first) - Which returns `None` for an empty `Choice`.
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.values.is_empty()
    }

    /// Converts the `Choice` into a `Vec<T>` containing all its values.
    #[inline]
    #[deprecated(
        since = "0.11.0",
        note = "Use `Into::<Vec<T>>::into()` or `.iter().cloned().collect()` instead. Will be removed in v0.12.0"
    )]
    pub fn to_vec(&self) -> Vec<T>
    where
        T: Clone,
    {
        self.values.to_vec()
    }

    /// Finds the first value that satisfies a predicate.
    #[deprecated(
        since = "0.11.0",
        note = "Use `iter().find()` instead. Will be removed in v0.12.0"
    )]
    pub fn find_first<'a, P>(&'a self, predicate: P) -> Option<&'a T>
    where
        P: Fn(&&'a T) -> bool,
    {
        self.iter().find(predicate)
    }

    /// Returns a new `Choice` with duplicate elements removed.
    #[deprecated(
        since = "0.11.0",
        note = "Deduplication is not a core categorical operation. Use external iteration patterns instead. Will be removed in v0.12.0"
    )]
    pub fn dedup(&self) -> Self
    where
        T: Hash + Eq + Clone,
    {
        if self.is_empty() {
            return self.clone();
        }

        let mut result = SmallVec::new();
        let mut seen = std::collections::HashSet::new();

        for value in self.iter() {
            if seen.insert(value) {
                result.push(value.clone());
            }
        }

        Self { values: result }
    }

    /// Returns a new `Choice` with duplicate elements removed based on a key extraction function.
    #[deprecated(
        since = "0.11.0",
        note = "Deduplication is not a core categorical operation. Use external iteration patterns instead. Will be removed in v0.12.0"
    )]
    pub fn dedup_by_key<K, F>(&self, key_fn: F) -> Self
    where
        F: Fn(&T) -> K,
        K: Hash + Eq,
        T: Clone,
    {
        if self.is_empty() {
            return self.clone();
        }

        let mut result = SmallVec::new();
        let mut seen = std::collections::HashSet::new();

        for value in self.iter() {
            let key = key_fn(value);
            if seen.insert(key) {
                result.push(value.clone());
            }
        }

        Self { values: result }
    }

    /// Folds the values in the `Choice` into a single value.
    #[deprecated(
        since = "0.11.0",
        note = "Use the Foldable trait's fold_left/fold_right instead. Will be removed in v0.12.0"
    )]
    pub fn fold<B, F>(&self, initial: B, f: F) -> B
    where
        F: Fn(B, &T) -> B,
    {
        self.values.iter().fold(initial, f)
    }

    /// Converts the `Choice` into a `HashMap` using a provided key-extraction function.
    #[deprecated(
        since = "0.11.0",
        note = "Specialized conversion methods should be external. Use `iter().map().collect()` patterns instead. Will be removed in v0.12.0"
    )]
    pub fn to_map_with_key<K, F>(&self, mut f: F) -> std::collections::HashMap<K, T>
    where
        T: Clone,
        K: std::hash::Hash + Eq,
        F: FnMut(&T) -> K,
    {
        let mut map = std::collections::HashMap::with_capacity(self.len());
        for value in self.iter() {
            map.entry(f(value)).or_insert_with(|| value.clone());
        }
        map
    }

    /// Adds multiple new alternatives to the `Choice`, consuming the original.
    #[inline]
    #[deprecated(
        since = "0.11.0",
        note = "Use Semigroup::combine() or Monoid operations instead. Will be removed in v0.12.0"
    )]
    pub fn add_alternatives<I>(self, items: I) -> Self
    where
        T: Clone,
        I: IntoIterator<Item = T>,
    {
        let mut new_values = self.values;
        new_values.extend(items);
        Self { values: new_values }
    }

    /// Removes an alternative at the specified index and returns a new `Choice`.
    ///
    /// The `index` is 0-based and relative to the list of alternatives (excluding the primary value).
    /// This method creates a new `Choice` instance by cloning the current values
    /// and removing the specified alternative.
    ///
    /// # Arguments
    ///
    /// * `index` - The 0-based index of the alternative to remove.
    ///
    /// # Returns
    ///
    /// A new `Choice<T>` with the alternative at the specified index removed.
    ///
    /// # Panics
    ///
    /// Panics if:
    /// - The `Choice` has no alternatives (i.e., it only contains a primary value or is empty).
    /// - The `index` is out of bounds for the list of alternatives.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::datatypes::choice::Choice;
    ///
    /// // Basic removal
    /// let choice = Choice::new(10, vec![20, 30, 40]); // alternatives are [20, 30, 40]
    /// let new_choice = choice.remove_alternative(1); // Removes alternative at index 1 (value 30)
    ///
    /// assert_eq!(new_choice.first(), Some(&10));
    /// assert_eq!(new_choice.alternatives(), &[20, 40]);
    /// assert_eq!(new_choice.len(), 3);
    ///
    /// // Remove first alternative
    /// let choice2 = Choice::new(10, vec![20, 30]);
    /// let after_remove_first = choice2.remove_alternative(0); // Removes 20
    /// assert_eq!(after_remove_first.first(), Some(&10));
    /// assert_eq!(after_remove_first.alternatives(), &[30]);
    ///
    /// // Remove last alternative
    /// let choice3 = Choice::new(100, vec![200, 300, 400]);
    /// let after_remove_last = choice3.remove_alternative(2); // Removes 400
    /// assert_eq!(after_remove_last.first(), Some(&100));
    /// assert_eq!(after_remove_last.alternatives(), &[200, 300]);
    /// ```
    ///
    /// ### Panics - Index out of bounds
    /// ```should_panic
    /// use rustica::datatypes::choice::Choice;
    ///
    /// let choice = Choice::new(1, vec![2, 3]); // alternatives: [2, 3] (len 2)
    /// // Panics because index 2 is out of bounds for alternatives.
    /// let _ = choice.remove_alternative(2);
    /// ```
    ///
    /// ### Panics - No alternatives to remove
    /// ```should_panic
    /// use rustica::datatypes::choice::Choice;
    ///
    /// let choice_only_primary = Choice::new(1, Vec::<i32>::new());
    /// // Panics because there are no alternatives to remove.
    /// let _ = choice_only_primary.remove_alternative(0);
    /// ```
    ///
    /// ```should_panic
    /// use rustica::datatypes::choice::Choice;
    ///
    /// let empty_choice: Choice<i32> = Choice::new_empty();
    /// // Panics because an empty choice has no alternatives.
    /// let _ = empty_choice.remove_alternative(0);
    /// ```
    #[inline]
    /// # See Also
    /// - [`filter()`](Self::filter) - To remove multiple alternatives based on a predicate.
    /// - [`add_alternatives()`](Self::add_alternatives) - To add new alternatives.
    /// - [`try_remove_alternative()`](Self::try_remove_alternative) - Safe version that returns Result.
    pub fn remove_alternative(self, index: usize) -> Self
    where
        T: Clone,
    {
        if self.values.len() <= 1 {
            panic!("Cannot remove alternative from Choice with no alternatives");
        }
        if index >= self.alternatives().len() {
            panic!(
                "Index out of bounds: the len is {} but the index is {}",
                self.alternatives().len(),
                index
            );
        }

        let mut new_values = self.values;
        new_values.remove(index + 1); // +1 because alternatives start at index 1
        Self { values: new_values }
    }

    /// Safely removes an alternative at the specified index, returning a Result.
    #[deprecated(
        since = "0.11.0",
        note = "Index-based manipulation is not a core categorical operation. Use filter_values() instead. Will be removed in v0.12.0"
    )]
    pub fn try_remove_alternative(self, index: usize) -> Result<Self, &'static str>
    where
        T: Clone,
    {
        if self.values.len() <= 1 {
            return Err("Cannot remove alternative from Choice with no alternatives");
        }
        if index >= self.alternatives().len() {
            return Err("Index out of bounds for alternatives");
        }

        let mut new_values = self.values;
        new_values.remove(index + 1); // +1 because alternatives start at index 1
        Ok(Self { values: new_values })
    }

    /// Filters the alternatives of the `Choice` based on a predicate.
    #[inline]
    #[deprecated(
        since = "0.11.0",
        note = "Semantically unclear (preserves primary unconditionally). Use filter_values() instead. Will be removed in v0.12.0"
    )]
    pub fn filter<P>(&self, predicate: P) -> Self
    where
        P: Fn(&T) -> bool,
        T: Clone,
    {
        if self.is_empty() {
            return Self::new_empty();
        }

        let mut filtered = SmallVec::<[T; 8]>::with_capacity(self.values.len());
        filtered.push(self.values[0].clone());
        filtered.extend(self.values.iter().skip(1).filter(|v| predicate(v)).cloned());

        Self { values: filtered }
    }

    /// Applies a function to each alternative value in the `Choice`.
    #[inline]
    #[deprecated(
        since = "0.11.0",
        note = "Too specialized. Use fmap() with conditional logic or external iteration instead. Will be removed in v0.12.0"
    )]
    pub fn fmap_alternatives<F>(&self, mut f: F) -> Choice<T>
    where
        F: FnMut(&T) -> T,
        T: Clone,
    {
        if self.is_empty() {
            return Self::new_empty();
        }

        let primary_value = self.values[0].clone();

        let mut new_alternatives = SmallVec::<[T; 8]>::new();
        if self.values.len() > 1 {
            for alt_value in &self.values[1..] {
                new_alternatives.push(f(alt_value));
            }
        }

        let mut final_values = SmallVec::with_capacity(1 + new_alternatives.len());
        final_values.push(primary_value);
        final_values.extend(new_alternatives);

        Self {
            values: final_values,
        }
    }

    /// Flattens a `Choice` of iterable items into a `Choice` of individual items.
    ///
    /// This method transforms a `Choice<T>` where `T` implements `IntoIterator` into a
    /// `Choice<T::Item>`. The first item from the primary value's iterator becomes the new primary
    /// value for the resulting `Choice`. All remaining items from the primary value's iterator,
    /// followed by all items from all alternatives' iterators (in their original order),
    /// become the new alternatives.
    ///
    /// # Type Parameters
    ///
    /// * `T`: The original type held by the `Choice`, which must be `Clone` and implement `IntoIterator`.
    /// * `I`: The item type produced by `T`'s iterator (i.e., `T::Item`), which must be `Clone`.
    ///
    /// # Panics
    ///
    /// Panics if the `Choice` is not empty but its primary value is an empty iterator (e.g., `Choice::new(vec![], ...)`).
    /// If the `Choice` itself is empty (`Choice::new_empty()`), this method will return an empty `Choice` without panicking.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::datatypes::choice::Choice;
    /// use rustica::traits::functor::Functor;
    ///
    /// // Basic flattening with Vec<i32>
    /// let nested_numbers: Choice<Vec<i32>> = Choice::new(vec![1, 2], vec![vec![3, 4], vec![5]]);
    /// let flattened_numbers: Choice<i32> = nested_numbers.flatten();
    /// assert_eq!(*flattened_numbers.first().unwrap(), 1);
    /// // Order of alternatives: rest of primary ([2]), then items from alternatives ([3, 4], then [5])
    /// assert_eq!(flattened_numbers.alternatives(), &[2, 3, 4, 5]);
    ///
    /// // Flattening with strings, demonstrating fmap to prepare for flatten
    /// let words: Choice<&str> = Choice::new("hello", vec!["world", "rust"]);
    /// // First, map &str to an iterable collection of chars, like Vec<char>
    /// let choice_of_vec_char: Choice<Vec<char>> = words.fmap(|s: &&str| s.chars().collect::<Vec<_>>());
    /// let flattened_chars: Choice<char> = choice_of_vec_char.flatten();
    /// assert_eq!(*flattened_chars.first().unwrap(), 'h');
    /// // Order: rest of primary ("hello"), then chars from alternatives ("world", then "rust")
    /// assert_eq!(flattened_chars.alternatives(), &['e', 'l', 'l', 'o', 'w', 'o', 'r', 'l', 'd', 'r', 'u', 's', 't']);
    ///
    /// // Flattening a Choice where alternatives are empty Vecs
    /// let single_nested_list: Choice<Vec<i32>> = Choice::new(vec![10, 20, 30], vec![Vec::<i32>::new(), vec![40]]);
    /// let flat_from_single_list: Choice<i32> = single_nested_list.flatten();
    /// assert_eq!(*flat_from_single_list.first().unwrap(), 10);
    /// // Order: items from alternatives (empty, then [40]), then rest of primary ([20, 30])
    /// assert_eq!(flat_from_single_list.alternatives(), &[20, 30, 40]);
    ///
    /// // Flattening an empty Choice
    /// let empty_nested: Choice<Vec<i32>> = Choice::new_empty();
    /// let empty_flattened: Choice<i32> = empty_nested.flatten();
    /// assert!(empty_flattened.is_empty());
    ///
    /// // Flattening a Choice with a primary that's an empty iterator (will panic)
    /// // let primary_empty_iter: Choice<Vec<i32>> = Choice::new(Vec::<i32>::new(), vec![vec![1]]);
    /// // Uncommenting the line below would cause a panic:
    /// // let _ = primary_empty_iter.flatten();
    /// ```
    ///
    /// # See Also
    /// - [`flatten_sorted`](Self::flatten_sorted) - Similar, but sorts the resulting alternatives.
    /// - [`join`](crate::traits::monad::Monad::join) - The Monad trait's equivalent operation for `Choice<Choice<T>>`.
    /// - [`bind`](crate::traits::monad::Monad::bind) - For more general monadic sequencing which can achieve flattening.
    /// - [`try_flatten`](Self::try_flatten) - Safe version that returns Result.
    pub fn flatten<I>(&self) -> Choice<I>
    where
        T: IntoIterator<Item = I> + Clone,
        I: Clone,
    {
        if self.values.is_empty() {
            return Choice::new_empty();
        }

        let primary = self.first().unwrap().clone();
        let mut primary_iter = primary.into_iter();

        match primary_iter.next() {
            Some(first_item) => {
                // The rest of the primary's iterator comes first.
                let alternatives = primary_iter
                    // Then chain the flattened alternatives.
                    .chain(
                        self.values
                            .iter()
                            .skip(1) // Skip the primary value
                            .flat_map(|val| val.clone().into_iter()),
                    )
                    .collect::<SmallVec<[I; 8]>>();

                Choice::new(first_item, alternatives)
            },
            None => panic!("Primary value was an empty iterator in Choice::flatten"),
        }
    }

    /// Safely flattens a `Choice` of iterable items into a `Choice` of individual items, returning a Result.
    ///
    /// This is the safe version of `flatten` that returns an error instead of panicking.
    ///
    /// # Returns
    ///
    /// * `Ok(Choice<I>)` - A flattened Choice if successful.
    /// * `Err(&'static str)` - An error message if the primary value is an empty iterator.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::datatypes::choice::Choice;
    ///
    /// let nested = Choice::new(vec![1, 2], vec![vec![3, 4]]);
    /// let result = nested.try_flatten();
    /// assert!(result.is_ok());
    /// let flattened = result.unwrap();
    /// assert_eq!(*flattened.first().unwrap(), 1);
    /// assert_eq!(flattened.alternatives(), &[2, 3, 4]);
    ///
    /// // Safe error handling
    /// let empty_primary = Choice::new(Vec::<i32>::new(), vec![vec![1, 2]]);
    /// let result = empty_primary.try_flatten();
    /// assert!(result.is_err());
    /// ```
    pub fn try_flatten<I>(&self) -> Result<Choice<I>, &'static str>
    where
        T: IntoIterator<Item = I> + Clone,
        I: Clone,
    {
        if self.values.is_empty() {
            return Ok(Choice::new_empty());
        }

        let primary = self.first().unwrap().clone();
        let mut primary_iter = primary.into_iter();

        match primary_iter.next() {
            Some(first_item) => {
                let alternatives = primary_iter
                    .chain(
                        self.values
                            .iter()
                            .skip(1)
                            .flat_map(|val| val.clone().into_iter()),
                    )
                    .collect::<SmallVec<[I; 8]>>();

                Ok(Choice::new(first_item, alternatives))
            },
            None => Err("Primary value was an empty iterator in Choice::try_flatten"),
        }
    }

    /// Flattens a `Choice` of iterable items into a sorted `Choice` of individual items.
    #[deprecated(
        since = "0.11.0",
        note = "Mixing categorical operations (flatten) with ordering breaks FP philosophy. Use flatten() then sort externally. Will be removed in v0.12.0"
    )]
    pub fn flatten_sorted<I>(&self) -> Choice<I>
    where
        T: IntoIterator<Item = I> + Clone,
        I: Clone + Ord,
    {
        if self.values.is_empty() {
            return Choice::new_empty();
        }

        let primary = self.first().unwrap().clone();
        let mut primary_iter = primary.into_iter();

        match primary_iter.next() {
            Some(first_item) => {
                // Collect all remaining items from primary and all alternatives
                let mut alternatives = self
                    .values
                    .iter()
                    .skip(1) // Skip the primary value
                    .flat_map(|val| val.clone().into_iter())
                    .chain(primary_iter) // Add remaining items from primary
                    .collect::<SmallVec<[I; 8]>>();

                // Sort the alternatives
                alternatives.sort();

                Choice::new(first_item, alternatives)
            },
            None => panic!("Primary value was an empty iterator in Choice::flatten_sorted"),
        }
    }

    /// Creates a new `Choice` from an iterable collection of items.
    ///
    /// The first item yielded by the iterator `many` becomes the primary value of the
    /// new `Choice`. All subsequent items from the iterator become the alternatives,
    /// preserving their order.
    ///
    /// If the `many` iterator is empty, an empty `Choice` (via [`Choice::new_empty()`]) is returned.
    /// If the `many` iterator yields only one item, the resulting `Choice` will have that
    /// item as its primary value and no alternatives.
    ///
    /// # Arguments
    ///
    /// * `many` - An iterable `I: IntoIterator<Item = T>` whose items will populate the `Choice`.
    ///
    /// # Returns
    ///
    /// A new `Choice<T>` instance. Returns an empty `Choice` if `many` is empty.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::datatypes::choice::Choice;
    ///
    /// // From a Vec with multiple items
    /// let choice_from_vec = Choice::of_many(vec![10, 20, 30, 40]);
    /// assert_eq!(*choice_from_vec.first().unwrap(), 10);
    /// assert_eq!(choice_from_vec.alternatives(), &[20, 30, 40]);
    ///
    /// // From an array slice
    /// let data = [1, 2, 3];
    /// let choice_from_slice = Choice::of_many(&data); // Iterates over references, so Choice<&i32>
    /// assert_eq!(*choice_from_slice.first().unwrap(), &1);
    /// assert_eq!(choice_from_slice.alternatives(), &[&2, &3]);
    /// // To get Choice<i32>, clone or map:
    /// let choice_from_slice_cloned: Choice<i32> = Choice::of_many(data.iter().cloned());
    /// assert_eq!(*choice_from_slice_cloned.first().unwrap(), 1);
    /// assert_eq!(choice_from_slice_cloned.alternatives(), &[2, 3]);
    ///
    /// // From an iterator with a single item
    /// let single_item_choice = Choice::of_many(std::iter::once(100));
    /// assert_eq!(*single_item_choice.first().unwrap(), 100);
    /// assert!(single_item_choice.alternatives().is_empty());
    ///
    /// // From an empty iterator
    /// let empty_vec: Vec<i32> = Vec::new();
    /// let empty_choice = Choice::of_many(empty_vec);
    /// assert!(empty_choice.is_empty());
    /// assert_eq!(empty_choice.first(), None);
    /// ```
    ///
    /// # See Also
    /// - [`Choice::new()`](Self::new) - For creating a `Choice` with an explicit primary value and a separate collection of alternatives.
    /// - [`Choice::new_empty()`](Self::new_empty) - For creating an empty `Choice`.
    /// - [`FromIterator`] - While `Choice` doesn't directly implement `FromIterator`
    ///   due to the special role of the first element, `of_many` provides similar ergonomics.
    #[inline]
    pub fn of_many<I>(many: I) -> Self
    where
        I: IntoIterator<Item = T>,
        T: Clone,
    {
        let values: SmallVec<[T; 8]> = many.into_iter().collect();

        if values.is_empty() {
            Self::new_empty()
        } else {
            Self { values }
        }
    }

    /// Filters all values (primary and alternatives) of the `Choice` based on a predicate.
    ///
    /// This method applies the `predicate` to every value in the `Choice`.
    /// A new `Choice` is constructed with only the values that satisfy the predicate.
    ///
    /// - If the original primary value satisfies the predicate, it remains the primary value
    ///   in the new `Choice`.
    /// - If the original primary value does *not* satisfy the predicate, then the *first*
    ///   alternative (in its original order) that *does* satisfy the predicate becomes
    ///   the new primary value.
    /// - All other values that satisfy the predicate become the alternatives in the new `Choice`,
    ///   maintaining their relative order.
    /// - If no values in the `Choice` satisfy the predicate, or if the original `Choice`
    ///   is empty, an empty `Choice` (via [`Choice::new_empty()`]) is returned.
    ///
    /// This method uses copy-on-write semantics for the underlying `SmallVec`.
    ///
    /// # Arguments
    ///
    /// * `predicate` - A closure `F: FnMut(&T) -> bool` that takes a reference to a
    ///   value and returns `true` if it should be kept, or `false` otherwise.
    ///
    /// # Returns
    ///
    /// A new `Choice<T>` containing only the values that satisfied the `predicate`.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::datatypes::choice::Choice;
    ///
    /// let choice = Choice::new(1, vec![2, 3, 4, 5, 6]);
    ///
    /// // Filter for even numbers. Primary (1) is odd, so it's removed.
    /// // First even alternative (2) becomes the new primary.
    /// let evens = choice.filter_values(|&x| x % 2 == 0);
    /// assert_eq!(*evens.first().unwrap(), 2);
    /// assert_eq!(evens.alternatives(), &[4, 6]);
    ///
    /// // Filter for numbers greater than 3. Primary (1) is removed.
    /// // First alternative > 3 is 4, which becomes primary.
    /// let greater_than_3 = choice.filter_values(|&x| x > 3);
    /// assert_eq!(*greater_than_3.first().unwrap(), 4);
    /// assert_eq!(greater_than_3.alternatives(), &[5, 6]);
    ///
    /// // Filter where primary satisfies the predicate.
    /// let choice_primary_ok = Choice::new(10, vec![1, 12, 3, 14]);
    /// let primary_kept = choice_primary_ok.filter_values(|&x| x % 2 == 0);
    /// assert_eq!(*primary_kept.first().unwrap(), 10); // Primary 10 is even
    /// assert_eq!(primary_kept.alternatives(), &[12, 14]);
    ///
    /// // Filter that removes all values
    /// let no_matches = choice.filter_values(|&x| x > 100);
    /// assert!(no_matches.is_empty());
    /// assert_eq!(no_matches.first(), None);
    ///
    /// // Filter on an empty choice
    /// let empty_choice: Choice<i32> = Choice::new_empty();
    /// let filtered_empty = empty_choice.filter_values(|&x| x > 0);
    /// assert!(filtered_empty.is_empty());
    ///
    /// // Filter that keeps all values
    /// let all_kept = choice.filter_values(|_| true);
    /// assert_eq!(*all_kept.first().unwrap(), 1);
    /// assert_eq!(all_kept.alternatives(), &[2, 3, 4, 5, 6]);
    /// ```
    ///
    /// # See Also
    /// - [`filter()`](Self::filter) - To filter only alternatives, always preserving the primary value.
    /// - [`Choice::new()`](Self::new) - For creating a `Choice`.
    /// - [`Choice::remove_alternative()`](Self::remove_alternative) - To remove a specific alternative by index.
    #[inline]
    pub fn filter_values<F>(&self, predicate: F) -> Self
    where
        T: Clone,
        F: Fn(&T) -> bool,
    {
        let filtered: SmallVec<[T; 8]> = self
            .values
            .iter()
            .filter(|v| predicate(v))
            .cloned()
            .collect();

        match filtered.len() {
            0 => Self::new_empty(),
            _ => Self { values: filtered },
        }
    }

    /// Returns an iterator over all values in the `Choice`, including the primary value and all alternatives.
    ///
    /// The iterator yields items in their stored order: primary value first, then alternatives.
    ///
    /// # Returns
    ///
    /// An iterator yielding references (`&T`) to all values in the `Choice`.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::datatypes::choice::Choice;
    ///
    /// let choice = Choice::new(10, vec![20, 30, 40]);
    /// let mut iterator = choice.iter();
    ///
    /// assert_eq!(iterator.next(), Some(&10)); // Primary
    /// assert_eq!(iterator.next(), Some(&20)); // First alternative
    /// assert_eq!(iterator.next(), Some(&30)); // Second alternative
    /// assert_eq!(iterator.next(), Some(&40)); // Third alternative
    /// assert_eq!(iterator.next(), None);
    ///
    /// // Using in a for loop
    /// let mut collected_values = Vec::new();
    /// for value in choice.iter() {
    ///     collected_values.push(*value);
    /// }
    /// assert_eq!(collected_values, vec![10, 20, 30, 40]);
    ///
    /// // Iterating an empty choice
    /// let empty_choice: Choice<i32> = Choice::new_empty();
    /// assert_eq!(empty_choice.iter().next(), None);
    /// ```
    ///
    /// # See Also
    /// - [`iter_alternatives`](Self::iter_alternatives) - For an iterator over only the alternatives.
    /// - [`into_iter`](#impl-IntoIterator-for-&'a-Choice<T>) - For consuming iteration by reference.
    /// - [`into_iter`](#impl-IntoIterator-for-Choice<T>) - For consuming iteration by value.
    #[inline]
    pub fn iter(&self) -> impl Iterator<Item = &T> {
        self.values.iter()
    }

    /// Returns an iterator over the alternative values in the `Choice`, excluding the primary value.
    ///
    /// The iterator yields items in their stored order.
    ///
    /// # Returns
    ///
    /// An iterator yielding references (`&T`) to the alternative values.
    /// If there are no alternatives, or if the `Choice` is empty, the iterator will be empty.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::datatypes::choice::Choice;
    ///
    /// let choice = Choice::new(10, vec![20, 30, 40]);
    /// let mut alt_iterator = choice.iter_alternatives();
    ///
    /// assert_eq!(alt_iterator.next(), Some(&20));
    /// assert_eq!(alt_iterator.next(), Some(&30));
    /// assert_eq!(alt_iterator.next(), Some(&40));
    /// assert_eq!(alt_iterator.next(), None);
    ///
    /// // Using in a for loop
    /// let mut collected_alternatives = Vec::new();
    /// for alt_value in choice.iter_alternatives() {
    ///     collected_alternatives.push(*alt_value);
    /// }
    /// assert_eq!(collected_alternatives, vec![20, 30, 40]);
    ///
    /// // Choice with no alternatives
    /// let single_choice = Choice::new(100, Vec::<i32>::new());
    /// assert_eq!(single_choice.iter_alternatives().next(), None);
    ///
    /// // Iterating an empty choice
    /// let empty_choice: Choice<i32> = Choice::new_empty();
    /// assert_eq!(empty_choice.iter_alternatives().next(), None);
    /// ```
    ///
    /// # See Also
    /// - [`iter`](Self::iter) - For an iterator over all values, including the primary.
    /// - [`alternatives`](Self::alternatives) - To get a slice of alternatives directly.
    #[inline]
    pub fn iter_alternatives(&self) -> impl Iterator<Item = &T> {
        self.values.iter().skip(1)
    }

    /// Swaps the primary value with the alternative at the specified `alt_index`.
    #[deprecated(
        since = "0.11.0",
        note = "Index-based swapping is not a core categorical operation. Use external patterns instead. Will be removed in v0.12.0"
    )]
    pub fn swap_with_alternative(self, alt_index: usize) -> Self
    where
        T: Clone,
    {
        if self.values.len() <= 1 {
            panic!("Cannot swap with alternative from Choice with no alternatives");
        }
        if alt_index >= self.alternatives().len() {
            panic!(
                "Index out of bounds: the len is {} but the index is {}",
                self.alternatives().len(),
                alt_index
            );
        }

        let actual_alt_index = alt_index + 1;

        let mut new_values = self.values;
        new_values.swap(0, actual_alt_index);
        Self { values: new_values }
    }

    /// Creates a lazy iterator that applies bind operation without immediate allocation.
    ///
    /// This provides a lazy evaluation version of bind that can be more memory-efficient
    /// for large operations or when only some results are needed.
    ///
    /// # Arguments
    ///
    /// * `f` - A function that takes a reference to T and returns `Choice<U>`
    ///
    /// # Returns
    ///
    /// An iterator that yields U values lazily
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::datatypes::choice::Choice;
    ///
    /// let choice = Choice::new(1, vec![2, 3]);
    /// let mut iter = choice.bind_lazy(|x| Choice::new(x * 10, vec![x * 20]));
    ///
    /// assert_eq!(iter.next(), Some(10)); // Primary result from f(1)
    /// assert_eq!(iter.next(), Some(20)); // Alternative from f(1)
    /// assert_eq!(iter.next(), Some(20)); // Primary from f(2)
    /// assert_eq!(iter.next(), Some(40)); // Alternative from f(2)
    /// ```
    #[deprecated(
        since = "0.11.0",
        note = "Too specialized. Use bind() with into_iter() or flat_map patterns instead. Will be removed in v0.12.0"
    )]
    pub fn bind_lazy<U, F>(&self, f: F) -> impl Iterator<Item = U>
    where
        F: Fn(&T) -> Choice<U>,
        U: Clone,
    {
        self.iter().flat_map(move |val| {
            let choice = f(val);
            choice.into_iter()
        })
    }

    /// Safely swaps the primary value with the alternative at the specified index, returning a Result.
    ///
    /// This is the safe version of `swap_with_alternative` that returns an error instead of panicking.
    ///
    /// # Arguments
    ///
    /// * `alt_index` - The 0-based index of the alternative to swap with the primary value.
    ///
    /// # Returns
    ///
    /// * `Ok(Choice<T>)` - A new Choice with the values swapped.
    /// * `Err(&'static str)` - An error message if the operation cannot be performed.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::datatypes::choice::Choice;
    ///
    /// let choice = Choice::new(10, vec![20, 30, 40]);
    /// let result = choice.try_swap_with_alternative(1);
    /// assert!(result.is_ok());
    /// let swapped = result.unwrap();
    /// assert_eq!(*swapped.first().unwrap(), 30);
    /// assert_eq!(swapped.alternatives(), &[20, 10, 40]);
    ///
    /// // Safe error handling
    /// let single_choice = Choice::new(10, Vec::<i32>::new());
    /// let result = single_choice.try_swap_with_alternative(0);
    /// assert!(result.is_err());
    /// ```
    #[deprecated(
        since = "0.11.0",
        note = "Index-based swapping is not a core categorical operation. Use external patterns instead. Will be removed in v0.12.0"
    )]
    pub fn try_swap_with_alternative(self, alt_index: usize) -> Result<Self, &'static str>
    where
        T: Clone,
    {
        if self.values.len() <= 1 {
            return Err("Cannot swap with alternative from Choice with no alternatives");
        }
        if alt_index >= self.alternatives().len() {
            return Err("Index out of bounds for alternatives");
        }

        let actual_alt_index = alt_index + 1;

        let mut new_values = self.values;
        new_values.swap(0, actual_alt_index);
        Ok(Self { values: new_values })
    }

    /// Helper function to generate alternatives for apply operation
    fn generate_apply_alternatives<A, B>(
        func_values: &SmallVec<[T; 8]>, val_values: &SmallVec<[A; 8]>,
    ) -> SmallVec<[B; 8]>
    where
        T: Fn(A) -> B,
        A: Clone,
    {
        val_values
            .iter()
            .enumerate()
            .flat_map(|(i, val)| {
                func_values.iter().enumerate().filter_map(move |(j, func)| {
                    if i == 0 && j == 0 {
                        None
                    } else {
                        Some(func(val.clone()))
                    }
                })
            })
            .collect()
    }
}

impl<T> HKT for Choice<T> {
    type Source = T;
    type Output<U> = Choice<U>;
}

impl<T> Pure for Choice<T> {
    fn pure<A: Clone>(value: &A) -> Self::Output<A> {
        Choice::from_iter([value.clone()])
    }

    fn pure_owned<A: Clone>(value: A) -> Self::Output<A> {
        Choice::from_iter([value])
    }
}

impl<T: Clone> Functor for Choice<T> {
    /// Maps a function over the `Choice` container, transforming each value.
    ///
    /// This is the implementation of the `Functor` typeclass's `fmap` method for `Choice<T>`.
    /// It applies the function `f` to each value in the `Choice`, producing a new `Choice` containing
    /// the results.
    ///
    /// # Functor Laws
    ///
    /// This implementation satisfies the functor laws:
    ///
    /// ## Identity Law
    ///
    /// `choice.fmap(|x| x) == choice`
    ///
    /// ```rust
    /// # use rustica::prelude::*;
    /// # use rustica::datatypes::choice::Choice;
    /// let choice = Choice::new(1, vec![2, 3]);
    /// let mapped = choice.clone().fmap(|x: &i32| *x); // Apply identity function
    /// assert_eq!(choice, mapped);
    /// ```
    ///
    /// ## Composition Law
    ///
    /// `choice.fmap(f).fmap(g) == choice.fmap(|x| g(f(x)))`
    ///
    /// ```rust
    /// # use rustica::prelude::*;
    /// # use rustica::datatypes::choice::Choice;
    /// let choice = Choice::new(1, vec![2, 3]);
    /// let f = |x: &i32| *x + 10;
    /// let g = |x: &i32| *x * 2;
    ///
    /// let left = choice.clone().fmap(f).fmap(g);
    /// let right = choice.fmap(|x| g(&f(x)));
    /// assert_eq!(left, right);
    /// ```
    #[inline]
    fn fmap<B, F>(&self, f: F) -> Self::Output<B>
    where
        F: Fn(&T) -> B,
        B: Clone,
    {
        if self.values.is_empty() {
            return Choice::new_empty();
        }

        let values = &self.values;
        let primary = f(&values[0]);
        let alternatives: SmallVec<[B; 8]> = values[1..].iter().map(f).collect();

        Choice::new(primary, alternatives)
    }

    fn fmap_owned<B, F>(self, f: F) -> Self::Output<B>
    where
        F: FnMut(T) -> B,
    {
        if self.values.is_empty() {
            return Choice::new_empty();
        }

        let mut values = self.values;
        let mut f = f;
        let primary = f(values.remove(0));
        let alternatives: SmallVec<[B; 8]> = values.into_iter().map(f).collect();
        Choice::new(primary, alternatives)
    }
}

impl<T: Clone> Monad for Choice<T> {
    /// Chains computations that return `Choice`s.
    ///
    /// This is the implementation of the Monad typeclass's `bind` (or `>>=` in Haskell) method for `Choice<T>`.
    /// It applies the function `f` to each value in the `Choice`, where `f` itself returns a `Choice`.
    /// The results are then flattened into a single `Choice`.
    ///
    /// # Monad Laws
    ///
    /// This implementation satisfies the monad laws:
    ///
    /// ## Left Identity Law
    ///
    /// `Choice::pure(a).bind(f) == f(a)`
    ///
    /// ```rust
    /// # use rustica::prelude::*;
    /// # use rustica::datatypes::choice::Choice;
    /// let a = 5;
    /// let f = |x: &i32| Choice::new(*x * 2, vec![*x * 3]);
    ///
    /// let left = Choice::<i32>::pure(&a).bind(f);
    /// let right = f(&a);
    /// assert_eq!(left, right);
    /// ```
    ///
    /// ## Right Identity Law
    ///
    /// `m.bind(Choice::pure) == m`
    ///
    /// ```rust
    /// # use rustica::prelude::*;
    /// # use rustica::datatypes::choice::Choice;
    /// let m = Choice::new(10, vec![20, 30]);
    /// let bound = m.clone().bind(Choice::<i32>::pure);
    /// assert_eq!(m, bound);
    /// ```
    ///
    /// ## Associativity Law
    ///
    /// `(m.bind(f)).bind(g) == m.bind(|x| f(x).bind(g))`
    ///
    /// ```rust
    /// # use rustica::prelude::*;
    /// # use rustica::datatypes::choice::Choice;
    /// let m = Choice::new(5, vec![10]);
    /// let f = |x: &i32| Choice::new(*x + 1, vec![*x + 2]);
    /// let g = |x: &i32| Choice::new(*x * 2, vec![*x * 3]);
    ///
    /// let left = m.clone().bind(f).bind(g);
    /// let right = m.bind(|x| f(x).bind(g));
    /// assert_eq!(left, right);
    /// ```
    #[inline]
    fn bind<U, F>(&self, f: F) -> Self::Output<U>
    where
        F: Fn(&T) -> Self::Output<U>,
        U: Clone,
    {
        if self.values.is_empty() {
            return Choice::new_empty();
        }

        let self_values = &self.values;
        let first_choice = f(&self_values[0]);

        if first_choice.values.is_empty() {
            return Choice::new_empty();
        }

        let first_choice_values = &first_choice.values;
        let first = first_choice_values[0].clone();

        // Simple capacity estimate
        let mut alternatives =
            Vec::with_capacity(first_choice_values.len() - 1 + self_values.len() - 1);

        // Add alternatives from primary choice
        alternatives.extend_from_slice(&first_choice_values[1..]);

        // Apply f to each alternative and collect all values
        for alt in &self_values[1..] {
            let alt_choice = f(alt);
            alternatives.extend_from_slice(alt_choice.values.as_ref());
        }

        Choice::new(first, alternatives)
    }

    fn bind_owned<U, F>(self, mut f: F) -> Self::Output<U>
    where
        F: FnMut(Self::Source) -> Self::Output<U>,
        U: Clone,
    {
        if self.values.is_empty() {
            return Choice::new_empty();
        }

        let mut values = self.values;
        let primary_choice = f(values.remove(0));

        if primary_choice.values.is_empty() {
            return Choice::new_empty();
        }

        let primary_choice_values = &primary_choice.values;
        let first = primary_choice_values[0].clone();

        // Calculate better capacity estimate for bind_owned
        let mut alternatives = Vec::with_capacity(primary_choice_values.len() - 1 + values.len());

        alternatives.extend_from_slice(&primary_choice_values[1..]);

        for alt in values {
            let alt_choice = f(alt);
            alternatives.extend(alt_choice.values);
        }

        Choice::new(first, alternatives)
    }

    #[inline]
    fn join<U>(&self) -> Self::Output<U>
    where
        T: Into<Self::Output<U>> + Clone,
        U: Clone,
    {
        if self.values.is_empty() {
            return Choice::new_empty();
        }

        let primary_value = self.first().unwrap().clone();
        let primary_choice: Self::Output<U> = primary_value.into();

        if primary_choice.values.is_empty() {
            return Choice::new_empty();
        }

        let first = primary_choice.first().unwrap().clone();

        // Simple capacity estimate
        let mut alternatives =
            Vec::with_capacity(primary_choice.alternatives().len() + self.alternatives().len());

        // Add alternatives from primary choice
        alternatives.extend_from_slice(primary_choice.alternatives());

        // Add all values from alternative choices
        for alt in self.alternatives() {
            let alt_choice: Self::Output<U> = alt.clone().into();
            alternatives.extend_from_slice(alt_choice.values.as_ref());
        }

        Choice::new(first, alternatives)
    }

    #[inline]
    fn join_owned<U>(self) -> Self::Output<U>
    where
        T: Into<Self::Output<U>> + Clone,
        U: Clone,
    {
        if self.values.is_empty() {
            return Choice::new_empty();
        }

        let mut values = self.values;
        let primary_value = values.remove(0);
        let primary_choice: Self::Output<U> = primary_value.into();

        if primary_choice.values.is_empty() {
            return Choice::new_empty();
        }

        let first = primary_choice.first().unwrap().clone();

        // Simple capacity estimate
        let mut alternatives =
            Vec::with_capacity(primary_choice.alternatives().len() + values.len());

        // Add alternatives from primary choice
        alternatives.extend_from_slice(primary_choice.alternatives());

        // Add all values from alternative choices
        for alt in values {
            let alt_choice: Self::Output<U> = alt.into();
            alternatives.extend_from_slice(&alt_choice.values);
        }

        Choice::new(first, alternatives)
    }
}

impl<T: Clone> Semigroup for Choice<T> {
    fn combine(&self, other: &Self) -> Self {
        if self.values.is_empty() {
            return other.clone();
        }

        if other.values.is_empty() {
            return self.clone();
        }

        let self_values = &self.values;
        let other_values = &other.values;

        // Take the primary value from self
        let primary = self_values[0].clone();

        // Create a new Choice using iterators instead of extending vectors
        Choice::new(
            primary,
            self_values[1..]
                .iter()
                .cloned()
                .chain(other_values.iter().cloned()),
        )
    }

    fn combine_owned(self, other: Self) -> Self {
        if self.values.is_empty() {
            return other;
        }

        if other.values.is_empty() {
            return self;
        }

        let mut self_values = self.values;
        let primary = self_values.remove(0);
        Choice::new(primary, self_values.into_iter().chain(other.values))
    }
}

impl<T: Clone> Monoid for Choice<T> {
    fn empty() -> Self {
        Self::new_empty()
    }
}

impl<T: Clone> Applicative for Choice<T> {
    /// Applies a `Choice` of functions to a `Choice` of values.
    ///
    /// This is the implementation of the Applicative typeclass's `apply` (or `<*>` in Haskell) method for `Choice<T>`.
    /// It applies functions contained in the `f` parameter to values in the current `Choice`, producing
    /// a new `Choice` containing all results.
    ///
    /// # Applicative Laws
    ///
    /// This implementation satisfies the applicative laws:
    ///
    /// ## Identity Law
    ///
    /// `Applicative::apply(&Choice::pure(|x| x), &choice) == choice`
    ///
    /// ```rust
    /// # use rustica::prelude::*;
    /// # use rustica::datatypes::choice::Choice;
    /// let choice = Choice::new(5, vec![10, 15]);
    /// let id_fn: fn(&i32) -> i32 = |x: &i32| *x;
    /// let id_fn_choice = Choice::<fn(&i32) -> i32>::pure(&id_fn);
    /// let applied = Applicative::apply(&id_fn_choice, &choice);
    /// assert_eq!(choice, applied);
    /// ```
    ///
    /// ## Homomorphism Law
    ///
    /// `Applicative::apply(&Choice::pure(f), &Choice::pure(x)) == Choice::pure(f(x))`
    ///
    /// ```rust
    /// # use rustica::prelude::*;
    /// # use rustica::datatypes::choice::Choice;
    /// let f = |x: &i32| *x * 2;
    /// let x = 7;
    /// let pure_f = Choice::<fn(&i32) -> i32>::pure(&f);
    /// let pure_x = Choice::<i32>::pure(&x);
    /// let left = Applicative::apply(&pure_f, &pure_x);
    /// let right = Choice::<i32>::pure(&f(&x));
    /// assert_eq!(left, right);
    /// ```
    ///
    /// ## Interchange Law
    ///
    /// `Applicative::apply(&functions, &Choice::pure(y)) == functions.fmap(|f| f(y))`
    ///
    /// ```rust
    /// # use rustica::prelude::*;
    /// # use rustica::datatypes::choice::Choice;
    /// let y = 3;
    /// type IntFn = fn(&i32) -> i32;
    /// let f1: IntFn = |x: &i32| *x + 1;
    /// let f2: IntFn = |x: &i32| *x * 2;
    /// let functions = Choice::new(f1, vec![f2]);
    /// let pure_y = Choice::<i32>::pure(&y);
    /// let left = Applicative::apply(&functions, &pure_y);
    /// let right = functions.fmap(|f| f(&y));
    /// assert_eq!(left, right);
    /// ```
    #[inline]
    fn apply<A, B>(&self, value: &Self::Output<A>) -> Self::Output<B>
    where
        Self::Source: Fn(&A) -> B,
        B: Clone,
    {
        if self.values.is_empty() || value.values.is_empty() {
            return Choice::new_empty();
        }

        let func_values = &self.values;
        let val_values = &value.values;
        let func_first = &func_values[0];

        let primary = func_first(&val_values[0]);

        // Apply additional functions to primary value + apply all functions to all alternatives
        let alternatives: SmallVec<[B; 8]> = func_values[1..]
            .iter()
            .map(|f_alt| f_alt(&val_values[0]))
            .chain(val_values[1..].iter().flat_map(|val_alt| {
                std::iter::once(func_first(val_alt))
                    .chain(func_values[1..].iter().map(move |f_alt| f_alt(val_alt)))
            }))
            .collect();

        Choice::new(primary, alternatives)
    }

    fn apply_owned<A, B>(self, value: Self::Output<A>) -> Self::Output<B>
    where
        Self::Source: Fn(A) -> B,
        A: Clone,
    {
        if self.values.is_empty() || value.values.is_empty() {
            return Choice::new_empty();
        }

        let func_values = self.values;
        let val_values = value.values;

        let primary = func_values[0](val_values[0].clone());
        let alternatives = Self::generate_apply_alternatives(&func_values, &val_values);

        Choice::new(primary, alternatives)
    }

    fn lift2<A, B, C, F>(f: F, fa: &Self::Output<A>, fb: &Self::Output<B>) -> Self::Output<C>
    where
        F: Fn(&A, &B) -> C,
        A: Clone,
        B: Clone,
        C: Clone,
        Self: Sized,
    {
        if fa.values.is_empty() || fb.values.is_empty() {
            return Choice::new_empty();
        }

        let fa_values = fa.values.as_ref();
        let fb_values = fb.values.as_ref();

        let primary = f(&fa_values[0], &fb_values[0]);

        // Calculate capacity for alternatives vector
        let capacity = fa_values.len() * fb_values.len() - 1;
        let mut alternatives = SmallVec::<[C; 8]>::with_capacity(capacity);

        for (i, fa_val) in fa_values.iter().enumerate() {
            for (j, fb_val) in fb_values.iter().enumerate() {
                if i == 0 && j == 0 {
                    continue; // Skip primary
                }
                alternatives.push(f(fa_val, fb_val));
            }
        }

        Choice::new(primary, alternatives)
    }

    fn lift2_owned<A, B, C, F>(f: F, fa: Self::Output<A>, fb: Self::Output<B>) -> Self::Output<C>
    where
        F: Fn(A, B) -> C,
        A: Clone,
        B: Clone,
        C: Clone,
        Self: Sized,
    {
        if fa.values.is_empty() || fb.values.is_empty() {
            return Choice::new_empty();
        }

        let primary = f(fa.values[0].clone(), fb.values[0].clone());

        // Calculate capacity for alternatives vector
        let capacity = fa.len() * fb.len() - 1;
        let mut alternatives = Vec::with_capacity(capacity);

        for (i, a) in fa.values.iter().enumerate() {
            for (j, b_val) in fb.values.iter().enumerate() {
                if i == 0 && j == 0 {
                    continue; // Skip primary
                }
                alternatives.push(f(a.clone(), b_val.clone()));
            }
        }

        Choice::new(primary, alternatives)
    }

    fn lift3<A, B, C, D, F>(
        f: F, fa: &Self::Output<A>, fb: &Self::Output<B>, fc: &Self::Output<C>,
    ) -> Self::Output<D>
    where
        F: Fn(&A, &B, &C) -> D,
        A: Clone,
        B: Clone,
        C: Clone,
        D: Clone,
        Self: Sized,
    {
        if fa.values.is_empty() || fb.values.is_empty() || fc.values.is_empty() {
            return Choice::new_empty();
        }

        // Get references to the values
        let fa_values = &fa.values;
        let fb_values = &fb.values;
        let fc_values = &fc.values;

        let primary = f(&fa_values[0], &fb_values[0], &fc_values[0]);

        // Calculate capacity for alternatives vector
        let capacity = fa_values.len() * fb_values.len() * fc_values.len() - 1;
        let mut alternatives = SmallVec::<[D; 8]>::with_capacity(capacity);

        for (i, fa_val) in fa_values.iter().enumerate() {
            for (j, fb_val) in fb_values.iter().enumerate() {
                for (k, fc_val) in fc_values.iter().enumerate() {
                    if i == 0 && j == 0 && k == 0 {
                        continue; // Skip primary
                    }
                    alternatives.push(f(fa_val, fb_val, fc_val));
                }
            }
        }

        Choice::new(primary, alternatives)
    }

    fn lift3_owned<A, B, C, D, F>(
        f: F, fa: Self::Output<A>, fb: Self::Output<B>, fc: Self::Output<C>,
    ) -> Self::Output<D>
    where
        F: Fn(A, B, C) -> D,
        A: Clone,
        B: Clone,
        C: Clone,
        D: Clone,
        Self: Sized,
    {
        if fa.values.is_empty() || fb.values.is_empty() || fc.values.is_empty() {
            return Choice::new_empty();
        }

        let primary = f(
            fa.values[0].clone(),
            fb.values[0].clone(),
            fc.values[0].clone(),
        );

        let capacity = fa.len() * fb.len() * fc.len() - 1;
        let mut alternatives = SmallVec::<[D; 8]>::with_capacity(capacity);

        for (i, a) in fa.values.iter().enumerate() {
            for (j, b_val) in fb.values.iter().enumerate() {
                for (k, c_val) in fc.values.iter().enumerate() {
                    if i == 0 && j == 0 && k == 0 {
                        continue; // Skip primary
                    }
                    alternatives.push(f(a.clone(), b_val.clone(), c_val.clone()));
                }
            }
        }

        Choice::new(primary, alternatives)
    }
}

impl<T: Clone> Alternative for Choice<T> {
    fn alt(&self, other: &Self) -> Self
    where
        Self: Sized + Clone,
    {
        if self.values.is_empty() {
            return other.clone();
        }

        if other.values.is_empty() {
            return self.clone();
        }

        // Get the primary value from self
        let primary = self.values[0].clone();

        // Use iterators with chain() instead of extending vectors
        Choice::new(
            primary,
            self.values[1..]
                .iter()
                .cloned()
                .chain(other.values.iter().cloned()),
        )
    }

    fn empty_alt<B>() -> Self::Output<B> {
        Choice::new_empty()
    }

    fn guard(condition: bool) -> Self::Output<()> {
        if condition {
            Self::pure(&())
        } else {
            Self::empty_alt()
        }
    }

    fn many(&self) -> Self::Output<Vec<Self::Source>>
    where
        Self::Source: Clone,
    {
        if self.is_empty() {
            Choice::new_empty()
        } else {
            let primary = vec![self.first().unwrap().clone()];
            Choice::new(primary, vec![])
        }
    }
}

impl<T: Clone> MonadPlus for Choice<T> {
    fn mzero<U>() -> Self::Output<U> {
        Choice::new_empty()
    }

    fn mplus(&self, other: &Self) -> Self {
        if self.values.is_empty() {
            other.clone()
        } else if other.values.is_empty() {
            self.clone()
        } else {
            self.combine(other)
        }
    }

    fn mplus_owned(self, other: Self) -> Self {
        if self.values.is_empty() {
            other
        } else if other.values.is_empty() {
            self
        } else {
            self.combine_owned(other)
        }
    }
}

impl<T: Clone> Choice<Option<T>> {
    /// Sequences a `Choice` of `Option`s into an `Option` of a `Choice`.
    ///
    /// If all values inside the `Choice` are `Some(T)`, this returns `Some(Choice<T>)`.
    /// If any value is `None`, this returns `None`.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::datatypes::choice::Choice;
    ///
    /// let choice_all_some = Choice::new(Some(1), vec![Some(2), Some(3)]);
    /// let sequenced = choice_all_some.sequence();
    /// assert_eq!(sequenced, Some(Choice::new(1, vec![2, 3])));
    ///
    /// let choice_with_none = Choice::new(Some(1), vec![None, Some(3)]);
    /// let sequenced_none = choice_with_none.sequence();
    /// assert_eq!(sequenced_none, None);
    /// ```
    pub fn sequence(self) -> Option<Choice<T>> {
        let sequenced_values: Option<SmallVec<[T; 8]>> = self.values.iter().cloned().collect();
        sequenced_values.map(|values| Choice { values })
    }
}

impl<'a, T> IntoIterator for &'a Choice<T> {
    type Item = &'a T;
    type IntoIter = std::slice::Iter<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.values.iter()
    }
}

impl<T: Clone> IntoIterator for Choice<T> {
    type Item = T;
    type IntoIter = smallvec::IntoIter<[T; 8]>;

    fn into_iter(self) -> Self::IntoIter {
        self.values.into_iter()
    }
}

impl<T: Clone + Display> Display for Choice<T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        if let Some(first) = self.first() {
            write!(f, "{first}")?;
            let alternatives_slice = self.alternatives();
            if !alternatives_slice.is_empty() {
                let alternatives_str = alternatives_slice
                    .iter()
                    .map(|alt| alt.to_string())
                    .collect::<Vec<_>>()
                    .join(", ");
                write!(f, " | {alternatives_str}")?;
            }
            Ok(())
        } else {
            Ok(())
        }
    }
}

impl<T: Clone> Foldable for Choice<T> {
    fn fold_left<B, F>(&self, initial: &B, f: F) -> B
    where
        F: Fn(&B, &Self::Source) -> B,
        B: Clone,
    {
        self.iter()
            .fold(initial.clone(), |acc, value| f(&acc, value))
    }

    fn fold_right<B, F>(&self, initial: &B, f: F) -> B
    where
        F: Fn(&Self::Source, &B) -> B,
        B: Clone,
    {
        self.values
            .iter()
            .rev()
            .fold(initial.clone(), |acc, value| f(value, &acc))
    }
}

impl<T> FromIterator<T> for Choice<T> {
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        let collected: SmallVec<[T; 8]> = iter.into_iter().collect();
        match collected.len() {
            0 => Self::new_empty(),
            _ => Self { values: collected },
        }
    }
}

impl<T: Clone> FromIterator<Choice<T>> for Choice<T> {
    fn from_iter<I: IntoIterator<Item = Choice<T>>>(iter: I) -> Self {
        let values: SmallVec<[T; 8]> = iter.into_iter().flat_map(|choice| choice.values).collect();

        match values.len() {
            0 => Self::new_empty(),
            _ => Self { values },
        }
    }
}

impl<T: Clone> From<Vec<T>> for Choice<T> {
    fn from(v: Vec<T>) -> Self {
        if v.is_empty() {
            return Choice::new_empty();
        }

        let mut iter = v.into_iter();
        let primary = iter.next().unwrap();
        let alternatives: Vec<T> = iter.collect();

        Choice::new(primary, alternatives)
    }
}

impl<T: Clone> From<&[T]> for Choice<T> {
    fn from(slice: &[T]) -> Self {
        if slice.is_empty() {
            return Choice::new_empty();
        }

        let primary = slice[0].clone();
        let alternatives: Vec<T> = slice[1..].to_vec();

        Choice::new(primary, alternatives)
    }
}

impl<T: Clone> From<Choice<T>> for Vec<T> {
    fn from(choice: Choice<T>) -> Self {
        choice.values.to_vec()
    }
}

impl<T: Clone + Default> Default for Choice<T> {
    fn default() -> Self {
        Self::new_empty()
    }
}

impl<T: Clone + Default> std::iter::Sum for Choice<T> {
    fn sum<I: Iterator<Item = Self>>(iter: I) -> Self {
        iter.fold(Self::empty(), |a, b| a.mplus(&b))
    }
}

impl<T: Arbitrary + 'static> Arbitrary for Choice<T> {
    fn arbitrary(g: &mut Gen) -> Self {
        let items: Vec<T> = Arbitrary::arbitrary(g);
        Choice::of_many(items)
    }
}
