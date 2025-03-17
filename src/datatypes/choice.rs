//! # Choice
//!
//! The `Choice` datatype represents a value with alternatives.
//! It consists of a collection of values of type `T`.
//!
//! ## Mathematical Definition
//!
//! From a category theory perspective, `Choice<T>` can be seen as a structure
//! that represents a selection among multiple values of type `T`.
//!
//! ## Laws
//!
//! Choice implements various typeclasses with their associated laws:
//!
//! ### Functor Laws
//! - Identity: `fmap(id) = id`
//! - Composition: `fmap(f . g) = fmap(f) . fmap(g)`
//!
//! ### Applicative Laws
//! - Identity: `pure id <*> v = v`
//! - Composition: `pure (.) <*> u <*> v <*> w = u <*> (v <*> w)`
//! - Homomorphism: `pure f <*> pure x = pure (f x)`
//! - Interchange: `u <*> pure y = pure ($ y) <*> u`
//!
//! ### Monad Laws
//! - Left identity: `return a >>= f = f a`
//! - Right identity: `m >>= return = m`
//! - Associativity: `(m >>= f) >>= g = m >>= (\x -> f x >>= g)`
//!
//! ## Examples
//!
//! ```rust
//! use rustica::datatypes::choice::Choice;
//! use rustica::traits::functor::Functor;
//! use rustica::traits::applicative::Applicative;
//! use rustica::traits::monad::Monad;
//!
//! // Create a Choice with a primary value and some alternatives
//! let c: Choice<i32> = Choice::new(5, vec![10, 15, 20]);
//!
//! // Map over all values using the Functor instance
//! let doubled: Choice<i32> = c.fmap(|x: &i32| x * 2);
//! assert_eq!(*doubled.first().unwrap(), 10);
//! assert_eq!(doubled.alternatives(), &[20, 30, 40]);
//! ```
//!
//! ## TODO
//!
//! - Add more examples and test cases
//! - Implement additional utility methods
//! - Optimize performance for large collections of alternatives
//! - Add property-based tests for typeclass laws

use crate::traits::{
    applicative::Applicative, functor::Functor, hkt::HKT, identity::Identity, monad::Monad,
    monoid::Monoid, pure::Pure, semigroup::Semigroup,
};
use smallvec::{smallvec, SmallVec};
use std::collections::HashSet;
use std::fmt::{Debug, Display, Formatter};
use std::hash::Hash;
use std::marker::PhantomData;

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
/// * `values`: A vector containing all the values of type `T`.
///
/// # Examples
///
/// ```
/// use rustica::prelude::*;
/// use rustica::datatypes::choice::Choice;
///
/// let choice = Choice::new(1, vec![2, 3, 4]);
/// assert_eq!(*choice.first().unwrap(), 1);
/// assert_eq!(choice.alternatives().len(), 3);
/// ```
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Choice<T> {
    values: SmallVec<[T; 8]>,
    phantom: PhantomData<T>,
}

impl<T> Choice<T> {
    /// Creates a new `Choice` with a primary value and a vector of alternatives.
    ///
    /// # Arguments
    ///
    /// * `first` - The primary value of type `T`.
    /// * `alternatives` - A vector of alternative values of type `T`.
    ///
    /// # Returns
    ///
    /// A new `Choice<T>` instance.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::datatypes::choice::Choice;
    ///
    /// let choice = Choice::new(1, vec![2, 3, 4]);
    /// assert_eq!(*choice.first().unwrap(), 1);
    /// assert_eq!(choice.alternatives(), &[2, 3, 4]);
    /// ```
    #[inline]
    pub fn new(first: T, alternatives: Vec<T>) -> Self {
        let mut values = SmallVec::with_capacity(alternatives.len() + 1);
        values.push(first);
        values.extend(alternatives);
        Self {
            values,
            phantom: PhantomData,
        }
    }

    /// Creates a new empty `Choice`.
    ///
    /// # Returns
    ///
    /// A new `Choice<T>` instance with no values.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::datatypes::choice::Choice;
    ///
    /// let empty_choice: Choice<i32> = Choice::new_empty();
    ///
    /// assert!(empty_choice.is_empty());
    /// ```
    #[inline]
    pub fn new_empty() -> Self {
        Self {
            values: SmallVec::new(),
            phantom: PhantomData,
        }
    }

    /// Returns a reference to the primary value.
    ///
    /// # Returns
    ///
    /// A reference to the primary value of type `T`
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::datatypes::choice::Choice;
    ///
    /// let choice = Choice::new(42, vec![1, 2, 3]);
    /// assert_eq!(*choice.first().unwrap(), 42);
    /// ```
    #[inline]
    pub fn first(&self) -> Option<&T> {
        self.values.first()
    }

    /// Returns a reference to the vector of alternative values.
    ///
    /// # Returns
    ///
    /// A slice containing alternative values of type `T`
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::datatypes::choice::Choice;
    ///
    /// let choice = Choice::new(1, vec![2, 3, 4]);
    /// assert_eq!(choice.alternatives(), &[2, 3, 4]);
    /// ```
    #[inline]
    pub fn alternatives(&self) -> &[T] {
        &self.values[1..]
    }

    /// Checks if there are any alternatives.
    ///
    /// # Returns
    ///
    /// `true` if there are any alternatives, `false` otherwise.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::datatypes::choice::Choice;
    ///
    /// let choice_with_alternatives = Choice::new(1, vec![2, 3]);
    /// assert!(choice_with_alternatives.has_alternatives());
    ///
    /// let choice_without_alternatives = Choice::new(1, vec![]);
    /// assert!(!choice_without_alternatives.has_alternatives());
    /// ```
    #[inline]
    pub fn has_alternatives(&self) -> bool {
        self.values.len() > 1
    }

    /// Returns the total number of choices, including the primary value and all alternatives.
    ///
    /// # Returns
    ///
    /// The count of all choices as `usize`.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::datatypes::choice::Choice;
    ///
    /// let choice = Choice::new(42, vec![1, 2, 3]);
    /// assert_eq!(choice.len(), 4); // Primary value + 3 alternatives
    /// ```
    #[inline]
    pub fn len(&self) -> usize {
        self.values.len()
    }

    /// Checks if the `Choice` is empty (contains no values).
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
    ///
    /// assert!(empty_choice.is_empty());
    ///
    /// let non_empty_choice = Choice::new(1, vec![2, 3]);
    /// assert!(!non_empty_choice.is_empty());
    /// ```
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.values.is_empty()
    }

    /// Changes the primary value of the `Choice`.
    ///
    /// This method creates a new `Choice` instance with the new primary value
    /// and all existing alternatives.
    ///
    /// # Arguments
    ///
    /// * `first` - A reference to the new primary value of type `T`.
    ///
    /// # Returns
    ///
    /// A new `Choice<T>` instance with the updated primary value.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::datatypes::choice::Choice;
    ///
    /// let choice = Choice::new(1, vec![2, 3]);
    /// let changed = choice.change_first(&42);
    ///
    /// assert_eq!(*changed.first().unwrap(), 42);
    /// assert_eq!(changed.alternatives(), &[2, 3]);
    /// ```
    #[inline]
    pub fn change_first(&self, first: &T) -> Self
    where
        T: Clone,
    {
        let mut new_values = self.values.clone();
        new_values[0] = first.clone();
        Self {
            values: new_values,
            phantom: PhantomData,
        }
    }

    /// Adds a new alternative to the `Choice`.
    ///
    /// This method creates a new `Choice` instance with the same primary value
    /// and all existing alternatives, plus the new item as an additional alternative.
    ///
    /// # Arguments
    ///
    /// * `item` - A value of type `T` to be added as a new alternative.
    ///
    /// # Returns
    ///
    /// A new `Choice<T>` instance with the added alternative.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::datatypes::choice::Choice;
    ///
    /// let choice = Choice::new(1, vec![2, 3]);
    /// let new_choice = choice.add_alternative(&4);
    ///
    /// assert_eq!(*new_choice.first().unwrap(), 1);
    /// assert_eq!(new_choice.alternatives(), &[2, 3, 4]);
    /// ```
    #[inline]
    pub fn add_alternative(&self, item: &T) -> Self
    where
        T: Clone,
    {
        let mut new_values = self.values.clone();
        new_values.push(item.clone());
        Self {
            values: new_values,
            phantom: PhantomData,
        }
    }

    /// Adds multiple new alternatives to the `Choice`, consuming the original.
    ///
    /// This method creates a new `Choice` instance with the same primary value
    /// and all existing alternatives, plus the new items as additional alternatives.
    ///
    /// # Arguments
    ///
    /// * `items` - An iterator of values of type `T` to be added as new alternatives.
    ///
    /// # Returns
    ///
    /// A new `Choice<T>` instance with the added alternatives.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::datatypes::choice::Choice;
    ///
    /// let choice = Choice::new(1, vec![2, 3]);
    /// let new_choice = choice.add_alternatives_owned(vec![4, 5]);
    ///
    /// assert_eq!(*new_choice.first().unwrap(), 1);
    /// assert_eq!(new_choice.alternatives(), &[2, 3, 4, 5]);
    /// ```
    #[inline]
    pub fn add_alternatives_owned<I>(mut self, items: I) -> Self
    where
        I: IntoIterator<Item = T>,
    {
        self.values.extend(items);
        self
    }

    /// Removes an alternative at the specified index and returns a new `Choice`.
    ///
    /// # Arguments
    ///
    /// * `index` - The index of the alternative to remove (0-based, relative to the alternatives list).
    ///
    /// # Returns
    ///
    /// A new `Choice<T>` with the alternative at the specified index removed.
    ///
    /// # Panics
    ///
    /// Panics if the index is out of bounds.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::datatypes::choice::Choice;
    ///
    /// let choice = Choice::new(1, vec![2, 3, 4]);
    /// let new_choice = choice.remove_alternative(1);
    ///
    /// assert_eq!(*new_choice.first().unwrap(), 1);
    /// assert_eq!(new_choice.alternatives(), &[2, 4]);
    /// ```
    #[inline]
    pub fn remove_alternative(&self, index: usize) -> Self
    where
        T: Clone,
    {
        assert!(
            index < self.values.len() - 1,
            "Alternative index out of bounds"
        );

        let mut new_values = self.values.clone();
        new_values.remove(index + 1); // +1 because alternatives start at index 1
        Self {
            values: new_values,
            phantom: PhantomData,
        }
    }

    /// Filters the alternatives based on a predicate.
    ///
    /// # Arguments
    ///
    /// * `predicate` - A function that takes a reference to an alternative and returns a boolean.
    ///
    /// # Returns
    ///
    /// A new `Choice` with only the alternatives that satisfy the predicate.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::datatypes::choice::Choice;
    ///
    /// let choice = Choice::new(1, vec![2, 3, 4, 5]);
    /// let filtered = choice.filter(|x| x % 2 == 0);
    ///
    /// assert_eq!(*filtered.first().unwrap(), 1);
    /// assert_eq!(filtered.alternatives(), &[2, 4]);
    /// ```
    #[inline]
    pub fn filter<P>(&self, predicate: P) -> Self
    where
        T: Clone,
        P: Fn(&T) -> bool,
    {
        if let Some(first) = self.first() {
            let first = first.clone();
            let alternatives = self
                .alternatives()
                .iter()
                .filter(|item| predicate(item))
                .cloned()
                .collect::<Vec<_>>();
            Self::new(first, alternatives)
        } else {
            Self::new_empty()
        }
    }

    /// Finds the index of a given value in the alternatives.
    ///
    /// # Arguments
    ///
    /// * `value` - The value to search for in the alternatives.
    ///
    /// # Returns
    ///
    /// An `Option<usize>` containing the index if found, or `None` if not present.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::datatypes::choice::Choice;
    ///
    /// let choice = Choice::new(1, vec![2, 3, 4]);
    /// assert_eq!(choice.find_alternative(&3), Some(1));
    /// assert_eq!(choice.find_alternative(&5), None);
    /// ```
    #[inline]
    pub fn find_alternative(&self, value: &T) -> Option<usize>
    where
        T: PartialEq,
    {
        self.values.iter().skip(1).position(|v| v == value)
    }

    /// Applies a function to all values in the `Choice`, including the primary value and alternatives.
    ///
    /// # Arguments
    ///
    /// * `f` - A function that takes a reference to `T` and returns a new `T`
    ///
    /// # Returns
    ///
    /// A new `Choice<T>` with the function applied to all values
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::datatypes::choice::Choice;
    ///
    /// let choice = Choice::new(1, vec![2, 3, 4]);
    /// let doubled = choice.map_alternatives(|&x| x * 2);
    ///
    /// assert_eq!(*doubled.first().unwrap(), 2);
    /// assert_eq!(doubled.alternatives(), &[4, 6, 8]);
    /// ```
    #[inline]
    pub fn map_alternatives<F, U>(&self, f: F) -> Choice<U>
    where
        F: Fn(&T) -> U,
    {
        Choice {
            values: self.values.iter().map(f).collect(),
            phantom: PhantomData,
        }
    }

    /// Flattens a `Choice` of iterable items into a `Choice` of individual items.
    ///
    /// This method transforms a `Choice<T>` where `T` is an iterable type into a `Choice<T::Item>`.
    /// The first item of the primary value becomes the new primary value, and all other items
    /// (including those from alternatives) are collected into the new alternatives.
    ///
    /// # Type Parameters
    ///
    /// * `T`: The original type, which must be clonable and iterable.
    /// * `T::Item`: The item type of the iterable, which must be clonable.
    ///
    /// # Returns
    ///
    /// A new `Choice<T::Item>` with flattened contents.
    ///
    /// # Panics
    ///
    /// Panics if the primary value is an empty iterator.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::datatypes::choice::Choice;
    ///
    /// let nested = Choice::new(vec![1, 2], vec![vec![3, 4], vec![5]]);
    /// let flattened = nested.flatten();
    ///
    /// assert_eq!(*flattened.first().unwrap(), 1);
    /// assert_eq!(flattened.alternatives(), &[2, 3, 4, 5]);
    /// ```
    #[inline]
    pub fn flatten<I>(&self) -> Choice<I>
    where
        T: IntoIterator<Item = I> + Clone,
        I: Clone,
    {
        let mut all_items: Vec<I> = Vec::new();

        for value in &self.values {
            for item in value.clone().into_iter() {
                all_items.push(item);
            }
        }

        assert!(!all_items.is_empty(), "Cannot flatten empty iterators");

        let first = all_items.remove(0);
        Choice {
            values: std::iter::once(first).chain(all_items).collect(),
            phantom: PhantomData,
        }
    }

    /// Creates a new `Choice` by partitioning elements according to a predicate.
    ///
    /// The first element for which the predicate returns true becomes the primary value.
    /// All other elements (both those for which the predicate returns true or false)
    /// become alternatives.
    ///
    /// # Arguments
    ///
    /// * `vec` - A vector of elements to partition.
    /// * `predicate` - A function that returns true for elements that should be considered for the primary value.
    ///
    /// # Returns
    ///
    /// A new `Choice<T>` with the partitioned elements.
    ///
    /// # Panics
    ///
    /// Panics if the predicate doesn't return true for any element in the vector.
    #[inline]
    pub fn partition(vec: Vec<T>, predicate: impl Fn(&T) -> bool) -> Self {
        let position = vec
            .iter()
            .position(predicate)
            .expect("No element satisfies the predicate");

        let mut values = vec;
        let first = values.remove(position);

        Self {
            values: std::iter::once(first).chain(values).collect(),
            phantom: PhantomData,
        }
    }

    /// Creates a new `Choice` from a primary value and an iterable of alternatives.
    ///
    /// # Arguments
    ///
    /// * `first` - A value of type `T` to be used as the primary value
    /// * `alternatives` - An iterable containing items of type `T` to be used as alternatives
    ///
    /// # Returns
    ///
    /// A new `Choice<T>` instance containing the primary value and alternatives
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::datatypes::choice::Choice;
    ///
    /// let choice = Choice::of_many(1, vec![2, 3, 4]);
    /// assert_eq!(*choice.first().unwrap(), 1);
    /// assert_eq!(choice.alternatives(), &[2, 3, 4]);
    /// ```
    #[inline]
    pub fn of_many(first: T, alternatives: impl IntoIterator<Item = T>) -> Self {
        Self {
            values: std::iter::once(first).chain(alternatives).collect(),
            phantom: PhantomData,
        }
    }

    /// Creates a new `Choice` from an iterator, if the iterator is non-empty.
    ///
    /// # Arguments
    ///
    /// * `iter` - An iterator yielding items of type `T`
    ///
    /// # Returns
    ///
    /// * `Some(Choice<T>)` if the iterator is non-empty, with the first item as the primary value
    /// * `None` if the iterator is empty
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::datatypes::choice::Choice;
    ///
    /// let choice = Choice::from_iterator(vec![1, 2, 3]);
    /// assert!(choice.is_some());
    /// assert_eq!(*choice.unwrap().first().unwrap(), 1);
    ///
    /// let empty: Option<Choice<i32>> = Choice::from_iterator(Vec::<i32>::new());
    /// assert!(empty.is_none());
    /// ```
    #[inline]
    pub fn from_iterator(iter: impl IntoIterator<Item = T>) -> Option<Self> {
        let mut iter = iter.into_iter();
        iter.next().map(|first| Self {
            values: std::iter::once(first).chain(iter).collect(),
            phantom: PhantomData,
        })
    }

    /// Organizes alternatives in order using a `BTreeSet`.
    ///
    /// This method creates a new `Choice` with the same primary value but with
    /// alternatives ordered and deduplicated according to their natural order.
    /// The alternatives are stored in a `BTreeSet` internally and then converted
    /// back to a `Vec` for the resulting `Choice`.
    ///
    /// # Type Parameters
    ///
    /// * `T`: The type must implement `Ord` for ordering and `Clone` for creating a new `Choice`.
    ///
    /// # Returns
    ///
    /// A new `Choice<T>` with ordered and deduplicated alternatives.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::datatypes::choice::Choice;
    ///
    /// let choice = Choice::new(5, vec![3, 1, 4, 1, 2]);
    /// let ordered = choice.with_ordered_alternatives();
    ///
    /// assert_eq!(*ordered.first().unwrap(), 5);
    /// assert_eq!(ordered.alternatives(), &[1, 2, 3, 4]);
    /// ```
    #[inline]
    pub fn with_ordered_alternatives(&self) -> Self
    where
        T: Ord + Clone,
    {
        use std::collections::BTreeSet;

        let first = self.values[0].clone();
        let mut set = BTreeSet::new();

        // Add alternatives to the set for deduplication and ordering
        for value in self.values.iter().skip(1) {
            set.insert(value.clone());
        }

        // Create a new Choice with the ordered alternatives
        Self {
            values: std::iter::once(first).chain(set).collect(),
            phantom: PhantomData,
        }
    }

    /// Consumes the `Choice` and returns a new one with ordered and unique alternatives.
    ///
    /// This method creates a new `Choice` with the same primary value but with
    /// alternatives ordered and deduplicated according to their natural order.
    /// The alternatives are stored in a `BTreeSet` internally and then converted
    /// back to a `Vec` for the resulting `Choice`.
    ///
    /// # Type Parameters
    ///
    /// * `T`: The type must implement `Ord` for ordering and `Clone` for creating a new `Choice`.
    ///
    /// # Returns
    ///
    /// A new `Choice<T>` with ordered and deduplicated alternatives.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::datatypes::choice::Choice;
    ///
    /// let choice = Choice::new(5, vec![3, 1, 4, 1, 2]);
    /// let ordered = choice.with_ordered_alternatives_owned();
    ///
    /// assert_eq!(*ordered.first().unwrap(), 5);
    /// assert_eq!(ordered.alternatives(), &[1, 2, 3, 4]);
    /// ```
    #[inline]
    pub fn with_ordered_alternatives_owned(self) -> Self
    where
        T: Ord + Clone,
    {
        use std::collections::BTreeSet;

        let first = self.clone().values.into_iter().next().unwrap();
        let mut set = BTreeSet::new();

        for value in self.values.into_iter().skip(1) {
            set.insert(value);
        }

        Self {
            values: std::iter::once(first).chain(set).collect(),
            phantom: PhantomData,
        }
    }

    /// Returns a new `Choice` with unique alternatives, preserving the primary value.
    ///
    /// This method creates a new `Choice` with the same primary value but with
    /// deduplicated alternatives. The alternatives are stored in a `HashSet` internally
    /// and then converted back to a `Vec` for the resulting `Choice`.
    ///
    /// # Type Parameters
    ///
    /// * `T`: The type must implement `Hash`, `Eq`, and `Clone`.
    ///
    /// # Returns
    ///
    /// A new `Choice<T>` with deduplicated alternatives.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::datatypes::choice::Choice;
    ///
    /// let choice = Choice::new(1, vec![2, 3, 2, 4, 3]);
    /// let unique = choice.with_unique_alternatives();
    ///
    /// assert_eq!(*unique.first().unwrap(), 1);
    /// assert_eq!(unique.alternatives().len(), 3);
    /// ```
    #[inline]
    pub fn with_unique_alternatives(&self) -> Self
    where
        T: Hash + Eq + Clone,
    {
        let first = self.values[0].clone();
        let set: HashSet<_> = self.values.iter().skip(1).cloned().collect();

        Self {
            values: std::iter::once(first).chain(set).collect(),
            phantom: PhantomData,
        }
    }

    /// Consumes the `Choice` and returns a new one with unique alternatives.
    ///
    /// This method creates a new `Choice` with the same primary value but with
    /// deduplicated alternatives. The alternatives are stored in a `HashSet` internally
    /// and then converted back to a `Vec` for the resulting `Choice`.
    ///
    /// # Type Parameters
    ///
    /// * `T`: The type must implement `Hash`, `Eq`, and `Clone`.
    ///
    /// # Returns
    ///
    /// A new `Choice<T>` with deduplicated alternatives.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::datatypes::choice::Choice;
    ///
    /// let choice = Choice::new(1, vec![2, 3, 2, 4, 3]);
    /// let unique = choice.with_unique_alternatives_owned();
    ///
    /// assert_eq!(*unique.first().unwrap(), 1);
    /// assert_eq!(unique.alternatives().len(), 3);
    /// ```
    #[inline]
    pub fn with_unique_alternatives_owned(self) -> Self
    where
        T: Hash + Eq + Clone,
    {
        let first = self.clone().values.into_iter().next().unwrap();
        let set: HashSet<_> = self.values.into_iter().skip(1).collect();

        Self {
            values: std::iter::once(first).chain(set).collect(),
            phantom: PhantomData,
        }
    }

    /// Replaces the primary value with an alternative at the specified index,
    /// and moves the current primary value to alternatives.
    ///
    /// # Arguments
    ///
    /// * `index` - The index of the alternative to promote (0-based, relative to the alternatives list).
    ///
    /// # Returns
    ///
    /// A new `Choice<T>` with the primary value and specified alternative swapped.
    ///
    /// # Panics
    ///
    /// Panics if the index is out of bounds.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::datatypes::choice::Choice;
    ///
    /// let choice = Choice::new(1, vec![2, 3, 4]);
    /// let swapped = choice.swap_with_alternative(1);
    ///
    /// assert_eq!(*swapped.first().unwrap(), 3);
    /// assert_eq!(swapped.alternatives().contains(&1), true);
    /// ```
    #[inline]
    pub fn swap_with_alternative(&self, index: usize) -> Self
    where
        T: Clone,
    {
        assert!(
            index < self.values.len() - 1,
            "Alternative index out of bounds"
        );

        let real_index = index + 1; // +1 because alternatives start at index 1
        let old_first = self.values[0].clone();
        let new_first = self.values[real_index].clone();

        let mut new_values = self.values.clone();
        new_values[0] = new_first;
        new_values[real_index] = old_first;

        Self {
            values: new_values,
            phantom: PhantomData,
        }
    }

    /// Consumes the `Choice` and swaps the primary value with an alternative at the specified index.
    ///
    /// # Arguments
    ///
    /// * `index` - The index of the alternative to promote (0-based, relative to the alternatives list).
    ///
    /// # Returns
    ///
    /// A new `Choice<T>` with the primary value and specified alternative swapped.
    ///
    /// # Panics
    ///
    /// Panics if the index is out of bounds.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::datatypes::choice::Choice;
    ///
    /// let choice = Choice::new(1, vec![2, 3, 4]);
    /// let swapped = choice.swap_with_alternative_owned(1);
    ///
    /// assert_eq!(*swapped.first().unwrap(), 3);
    /// assert_eq!(swapped.alternatives().contains(&1), true);
    /// ```
    #[inline]
    pub fn swap_with_alternative_owned(self, index: usize) -> Self
    where
        T: Clone,
    {
        assert!(
            index < self.values.len() - 1,
            "Alternative index out of bounds"
        );

        let real_index = index + 1; // +1 because alternatives start at index 1
        let old_first = self.values[0].clone();
        let new_first = self.values[real_index].clone();

        let mut new_values = self.values;
        new_values[0] = new_first;
        new_values[real_index] = old_first;

        Self {
            values: new_values,
            phantom: PhantomData,
        }
    }

    /// Replaces all alternatives with the current primary value.
    ///
    /// This method creates a new `Choice` with the same primary value,
    /// but with all alternatives replaced by copies of the primary value.
    ///
    /// # Returns
    ///
    /// A new `Choice<T>` where all alternatives are identical to the primary value.
    /// If the choice is empty, returns an empty choice.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::datatypes::choice::Choice;
    ///
    /// let choice = Choice::new(42, vec![1, 2, 3]);
    /// let replaced = choice.replace_alternatives_with_first();
    ///
    /// assert_eq!(*replaced.first().unwrap(), 42);
    /// assert_eq!(replaced.alternatives(), &[42, 42, 42]);
    /// ```
    #[inline]
    pub fn replace_alternatives_with_first(&self) -> Self
    where
        T: Clone,
    {
        if let Some(first) = self.first() {
            let first = first.clone();
            let alt_count = self.alternatives().len();

            let mut new_values = SmallVec::with_capacity(alt_count + 1);
            new_values.push(first.clone());

            for _ in 0..alt_count {
                new_values.push(first.clone());
            }

            Self {
                values: new_values,
                phantom: PhantomData,
            }
        } else {
            Self::new_empty()
        }
    }

    /// Replaces all alternatives with the first value, consuming the original `Choice`.
    ///
    /// This method is similar to `replace_alternatives_with_first`, but it consumes
    /// the original `Choice` instance.
    ///
    /// # Returns
    ///
    /// A new `Choice<T>` where all alternatives are identical to the primary value.
    /// If the choice is empty, returns an empty choice.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::datatypes::choice::Choice;
    ///
    /// let choice = Choice::new(42, vec![1, 2, 3]);
    /// let replaced = choice.replace_alternatives_with_first_owned();
    ///
    /// assert_eq!(*replaced.first().unwrap(), 42);
    /// assert_eq!(replaced.alternatives(), &[42, 42, 42]);
    /// ```
    #[inline]
    pub fn replace_alternatives_with_first_owned(self) -> Self
    where
        T: Clone,
    {
        if self.values.is_empty() {
            return Self::new_empty();
        }

        let first = self.values[0].clone();
        let alt_count = self.values.len() - 1;

        let mut new_values = SmallVec::with_capacity(alt_count + 1);
        new_values.push(first.clone());

        for _ in 0..alt_count {
            new_values.push(first.clone());
        }

        Self {
            values: new_values,
            phantom: PhantomData,
        }
    }

    /// Returns an iterator over all values in the `Choice`, including the primary value and alternatives.
    ///
    /// # Returns
    ///
    /// An iterator yielding references to all values of type `&T`.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::datatypes::choice::Choice;
    ///
    /// let choice = Choice::new(1, vec![2, 3, 4]);
    /// let values: Vec<&i32> = choice.iter().collect();
    /// assert_eq!(values, vec![&1, &2, &3, &4]);
    /// ```
    #[inline]
    pub fn iter(&self) -> impl Iterator<Item = &T> {
        self.values.iter()
    }

    /// Returns an iterator over the alternative values in the `Choice`, excluding the primary value.
    ///
    /// # Returns
    ///
    /// An iterator yielding references to the alternative values of type `&T`.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::datatypes::choice::Choice;
    ///
    /// let choice = Choice::new(1, vec![2, 3, 4]);
    /// let alternatives: Vec<&i32> = choice.iter_alternatives().collect();
    /// assert_eq!(alternatives, vec![&2, &3, &4]);
    /// ```
    #[inline]
    pub fn iter_alternatives(&self) -> impl Iterator<Item = &T> {
        self.values.iter().skip(1)
    }

    /// Pattern matching for Choice, allowing different handling for empty and non-empty choices.
    ///
    /// # Arguments
    ///
    /// * `empty_case` - Function to call if the Choice is empty
    /// * `non_empty_case` - Function to call if the Choice has values, receiving the first value and alternatives
    ///
    /// # Returns
    ///
    /// The result of calling either the empty_case or non_empty_case function
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::datatypes::choice::Choice;
    ///
    /// let choice = Choice::new(1, vec![2, 3, 4]);
    /// let result = choice.match_choice(
    ///     || "Empty".to_string(),
    ///     |first, alternatives| format!("First: {}, Alternatives: {:?}", first, alternatives)
    /// );
    /// assert_eq!(result, "First: 1, Alternatives: [2, 3, 4]");
    /// ```
    #[inline]
    pub fn match_choice<U, F, G>(&self, empty_case: F, non_empty_case: G) -> U
    where
        F: FnOnce() -> U,
        G: FnOnce(&T, Vec<&T>) -> U,
    {
        if self.is_empty() {
            empty_case()
        } else {
            let first = &self.values[0];
            let alternatives = self.values.iter().skip(1).collect();
            non_empty_case(first, alternatives)
        }
    }

    /// Pattern matching for Choice, consuming the choice and passing ownership to the handler functions.
    ///
    /// # Arguments
    ///
    /// * `empty_case` - Function to call if the Choice is empty
    /// * `non_empty_case` - Function to call if the Choice has values, receiving ownership of the first value and alternatives
    ///
    /// # Returns
    ///
    /// The result of calling either the empty_case or non_empty_case function
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::datatypes::choice::Choice;
    ///
    /// let choice = Choice::new(1, vec![2, 3, 4]);
    /// let result = choice.match_choice_owned(
    ///     || "Empty".to_string(),
    ///     |first, alternatives| format!("First: {}, Alternatives: {:?}", first, alternatives)
    /// );
    /// assert_eq!(result, "First: 1, Alternatives: [2, 3, 4]");
    /// ```
    #[inline]
    pub fn match_choice_owned<U, F, G>(self, empty_case: F, non_empty_case: G) -> U
    where
        F: FnOnce() -> U,
        G: FnOnce(T, Vec<T>) -> U,
    {
        if self.is_empty() {
            empty_case()
        } else {
            let mut values = self.values.into_iter();
            let first = values.next().unwrap();
            let alternatives = values.collect();
            non_empty_case(first, alternatives)
        }
    }
}

impl<T> HKT for Choice<T> {
    type Source = T;
    type Output<U> = Choice<U>;
}

impl<T> Identity for Choice<T> {
    fn value(&self) -> &Self::Source {
        self.first().expect("Cannot get value from an empty Choice")
    }

    fn pure_identity<A>(value: A) -> Self::Output<A> {
        Choice {
            values: smallvec![value],
            phantom: PhantomData,
        }
    }

    fn into_value(self) -> Self::Source {
        self.values
            .into_iter()
            .next()
            .expect("Cannot get value from an empty Choice")
    }
}

impl<T> Functor for Choice<T> {
    fn fmap<B, F>(&self, f: F) -> Self::Output<B>
    where
        F: Fn(&Self::Source) -> B,
    {
        Choice {
            values: self.values.iter().map(f).collect(),
            phantom: PhantomData,
        }
    }

    fn fmap_owned<B, F>(self, f: F) -> Self::Output<B>
    where
        F: Fn(Self::Source) -> B,
        Self: Sized,
    {
        Choice {
            values: self.values.into_iter().map(f).collect(),
            phantom: PhantomData,
        }
    }
}

impl<T: Clone> Monad for Choice<T> {
    fn bind<U: Clone, F>(&self, f: F) -> Self::Output<U>
    where
        F: Fn(&Self::Source) -> Self::Output<U>,
    {
        let first_choice = f(&self.values[0]);

        // We need to extract values from the first_choice as a Choice<U>
        let first_choice_concrete = first_choice.as_choice();
        let first_value = first_choice_concrete.values[0].clone();
        let mut alternatives = first_choice_concrete.values[1..].to_vec();

        // Bind each alternative to f and collect all the results into a flat list
        for alt in &self.values[1..] {
            let alt_choice = f(alt);
            let alt_choice_concrete = alt_choice.as_choice();
            alternatives.extend(alt_choice_concrete.values.clone());
        }

        Choice {
            values: std::iter::once(first_value).chain(alternatives).collect(),
            phantom: PhantomData,
        }
    }

    fn bind_owned<U: Clone, F>(self, f: F) -> Self::Output<U>
    where
        F: Fn(Self::Source) -> Self::Output<U>,
        Self: Sized,
    {
        let first = self.values[0].clone();
        let alternatives = self.values[1..].to_vec();

        let first_choice = f(first);
        let first_choice_concrete = first_choice.as_choice();
        let first_value = first_choice_concrete.values[0].clone();
        let mut result_alternatives = first_choice_concrete.values[1..].to_vec();

        // Bind each alternative to f and collect all the results
        for alt in alternatives {
            let alt_choice = f(alt);
            let alt_choice_concrete = alt_choice.as_choice();
            result_alternatives.extend(alt_choice_concrete.values.clone());
        }

        Choice {
            values: std::iter::once(first_value)
                .chain(result_alternatives)
                .collect(),
            phantom: PhantomData,
        }
    }

    fn join<U: Clone>(&self) -> Self::Output<U>
    where
        Self::Source: Clone,
        Self::Source: Into<Self::Output<U>>,
    {
        let first_choice: Self::Output<U> = self.values[0].clone().into();
        let first_choice_concrete = first_choice.as_choice();
        let first_value = first_choice_concrete.values[0].clone();
        let mut alternatives = first_choice_concrete.values[1..].to_vec();

        // Add alternatives from each nested Choice
        for alt in &self.values[1..] {
            let alt_choice: Self::Output<U> = alt.clone().into();
            let alt_choice_concrete = alt_choice.as_choice();
            alternatives.extend(alt_choice_concrete.values.clone());
        }

        Choice {
            values: std::iter::once(first_value).chain(alternatives).collect(),
            phantom: PhantomData,
        }
    }

    fn join_owned<U: Clone>(self) -> Self::Output<U>
    where
        Self::Source: Into<Self::Output<U>>,
        Self: Sized,
    {
        let first_choice: Self::Output<U> = self.values[0].clone().into();
        let first_choice_concrete = first_choice.as_choice();
        let first_value = first_choice_concrete.values[0].clone();
        let mut alternatives = first_choice_concrete.values[1..].to_vec();

        // Add alternatives from each nested Choice
        for alt in self.values.into_iter().skip(1) {
            let alt_choice: Self::Output<U> = alt.into();
            let alt_choice_concrete = alt_choice.as_choice();
            alternatives.extend(alt_choice_concrete.values.clone());
        }

        Choice {
            values: std::iter::once(first_value).chain(alternatives).collect(),
            phantom: PhantomData,
        }
    }
}

// Helper trait to access concrete Choice values from HKT types
trait AsChoice<T> {
    fn as_choice(&self) -> &Choice<T>;
}

impl<T> AsChoice<T> for Choice<T> {
    fn as_choice(&self) -> &Choice<T> {
        self
    }
}

impl<T> Pure for Choice<T> {
    fn pure<A: Clone>(value: &A) -> Self::Output<A> {
        Choice {
            values: smallvec![value.clone()],
            phantom: PhantomData,
        }
    }
}

impl<T: Clone> Applicative for Choice<T> {
    fn apply<B, F>(&self, f: &Self::Output<F>) -> Self::Output<B>
    where
        F: Fn(&Self::Source) -> B,
    {
        if self.is_empty() || f.is_empty() {
            return Choice::new_empty();
        }

        let f_first = f.first().expect("f_first should not be None");
        let self_first = self.first().expect("self_first should not be None");

        let first_result = f_first(self_first);

        let mut alt_result = Vec::new();

        // Apply each function to the first value
        for f_alt in f.alternatives() {
            alt_result.push(f_alt(self_first));
        }

        // Apply the first function to each alternative
        for self_alt in self.alternatives() {
            alt_result.push(f_first(self_alt));
        }

        // Various combinations of values from a, b
        for self_alt in self.alternatives() {
            for f_alt in f.alternatives() {
                alt_result.push(f_alt(self_alt));
            }
        }

        Choice {
            values: std::iter::once(first_result).chain(alt_result).collect(),
            phantom: PhantomData,
        }
    }

    fn apply_owned<B, F>(self, f: Self::Output<F>) -> Self::Output<B>
    where
        F: Fn(Self::Source) -> B,
        Self: Sized,
    {
        let first = self.values[0].clone();
        let alternatives = self.values[1..].to_vec();

        let f_first = f.first().expect("f_first should not be None");

        let first_result = f_first(first.clone());

        let mut alt_result = Vec::new();

        // Apply each function to the first value
        for f_alt in f.alternatives() {
            alt_result.push(f_alt(first.clone()));
        }

        // Apply the first function to each alternative
        for alt in &alternatives {
            alt_result.push(f_first(alt.clone()));
        }

        // Various combinations of values from a, b
        for alt in &alternatives {
            for f_alt in f.alternatives() {
                alt_result.push(f_alt(alt.clone()));
            }
        }

        Choice {
            values: std::iter::once(first_result).chain(alt_result).collect(),
            phantom: PhantomData,
        }
    }

    fn lift2<B, C, F>(&self, b: &Self::Output<B>, f: F) -> Self::Output<C>
    where
        F: Fn(&Self::Source, &B) -> C,
        B: Clone,
    {
        if self.is_empty() || b.is_empty() {
            return Choice::new_empty();
        }

        let self_first = self.first().expect("self_first should not be None");
        let b_first = b.first().expect("b_first should not be None");

        let first_result = f(self_first, b_first);

        let mut alt_result = Vec::new();

        // Various combinations of values from a, b
        for b_alt in b.alternatives() {
            alt_result.push(f(self_first, b_alt));
        }

        for self_alt in self.alternatives() {
            alt_result.push(f(self_alt, b_first));
        }

        for b_alt in b.alternatives() {
            for self_alt in self.alternatives() {
                alt_result.push(f(self_alt, b_alt));
            }
        }

        Choice {
            values: std::iter::once(first_result).chain(alt_result).collect(),
            phantom: PhantomData,
        }
    }

    fn lift2_owned<B, C, F>(self, b: Self::Output<B>, f: F) -> Self::Output<C>
    where
        F: Fn(Self::Source, B) -> C,
        Self: Sized,
        B: Clone,
    {
        // Clone everything to avoid moved value issues
        let first = self.values[0].clone();
        let alternatives = self.values[1..].to_vec();
        let b_first = b.values[0].clone();
        let b_alternatives = b.values[1..].to_vec();

        let first_result = f(first.clone(), b_first.clone());

        let mut alt_result = Vec::new();

        // Various combinations of values from a, b
        for b_alt in &b_alternatives {
            alt_result.push(f(first.clone(), b_alt.clone()));
        }

        for alt in &alternatives {
            alt_result.push(f(alt.clone(), b_first.clone()));
        }

        for alt in &alternatives {
            for b_alt in &b_alternatives {
                alt_result.push(f(alt.clone(), b_alt.clone()));
            }
        }

        Choice {
            values: std::iter::once(first_result).chain(alt_result).collect(),
            phantom: PhantomData,
        }
    }

    fn lift3<B, C, D, F>(&self, b: &Self::Output<B>, c: &Self::Output<C>, f: F) -> Self::Output<D>
    where
        F: Fn(&Self::Source, &B, &C) -> D,
        B: Clone,
        C: Clone,
        Self::Source: Clone,
    {
        if self.is_empty() || b.is_empty() || c.is_empty() {
            return Choice::new_empty();
        }

        let self_first = self.first().expect("self_first should not be None");
        let b_first = b.first().expect("b_first should not be None");
        let c_first = c.first().expect("c_first should not be None");

        let first_result = f(self_first, b_first, c_first);

        let mut alt_result = Vec::new();

        // Various combinations of values from a, b, c
        for b_alt in b.alternatives() {
            alt_result.push(f(self_first, b_alt, c_first));
        }

        for c_alt in c.alternatives() {
            alt_result.push(f(self_first, b_first, c_alt));
        }

        for self_alt in self.alternatives() {
            alt_result.push(f(self_alt, b_first, c_first));
        }

        for b_alt in b.alternatives() {
            for c_alt in c.alternatives() {
                alt_result.push(f(self_first, b_alt, c_alt));
            }
        }

        for self_alt in self.alternatives() {
            for b_alt in b.alternatives() {
                alt_result.push(f(self_alt, b_alt, c_first));
            }
        }

        for self_alt in self.alternatives() {
            for c_alt in c.alternatives() {
                alt_result.push(f(self_alt, b_first, c_alt));
            }
        }

        for self_alt in self.alternatives() {
            for b_alt in b.alternatives() {
                for c_alt in c.alternatives() {
                    alt_result.push(f(self_alt, b_alt, c_alt));
                }
            }
        }

        Choice {
            values: std::iter::once(first_result).chain(alt_result).collect(),
            phantom: PhantomData,
        }
    }

    fn lift3_owned<B, C, D, F>(
        self,
        b: Self::Output<B>,
        c: Self::Output<C>,
        f: F,
    ) -> Self::Output<D>
    where
        F: Fn(Self::Source, B, C) -> D,
        Self: Sized,
        B: Clone,
        C: Clone,
    {
        // Clone everything to avoid moved value issues
        let first = self.values[0].clone();
        let alternatives = self.values[1..].to_vec();
        let b_first = b.values[0].clone();
        let b_alternatives = b.values[1..].to_vec();
        let c_first = c.values[0].clone();
        let c_alternatives = c.values[1..].to_vec();

        let first_result = f(first.clone(), b_first.clone(), c_first.clone());

        let mut alt_result = Vec::new();

        // Various combinations of values from a, b, c
        for b_alt in &b_alternatives {
            alt_result.push(f(first.clone(), b_alt.clone(), c_first.clone()));
        }

        for c_alt in &c_alternatives {
            alt_result.push(f(first.clone(), b_first.clone(), c_alt.clone()));
        }

        for alt in &alternatives {
            alt_result.push(f(alt.clone(), b_first.clone(), c_first.clone()));
        }

        for b_alt in &b_alternatives {
            for c_alt in &c_alternatives {
                alt_result.push(f(first.clone(), b_alt.clone(), c_alt.clone()));
            }
        }

        for alt in &alternatives {
            for b_alt in &b_alternatives {
                alt_result.push(f(alt.clone(), b_alt.clone(), c_first.clone()));
            }
        }

        for alt in &alternatives {
            for c_alt in &c_alternatives {
                alt_result.push(f(alt.clone(), b_first.clone(), c_alt.clone()));
            }
        }

        for alt in &alternatives {
            for b_alt in &b_alternatives {
                for c_alt in &c_alternatives {
                    alt_result.push(f(alt.clone(), b_alt.clone(), c_alt.clone()));
                }
            }
        }

        Choice {
            values: std::iter::once(first_result).chain(alt_result).collect(),
            phantom: PhantomData,
        }
    }
}

impl<T: Clone> Semigroup for Choice<T> {
    fn combine(&self, other: &Self) -> Self {
        let mut combined_values = self.values.clone();
        combined_values.extend(other.values.clone());
        Choice {
            values: combined_values,
            phantom: PhantomData,
        }
    }

    fn combine_owned(self, other: Self) -> Self {
        let mut combined_values = self.values;
        combined_values.extend(other.values);
        Choice {
            values: combined_values,
            phantom: PhantomData,
        }
    }
}

impl<T: Clone + Default> Monoid for Choice<T> {
    fn empty() -> Self {
        Choice {
            values: smallvec![T::default()],
            phantom: PhantomData,
        }
    }
}

impl<T> IntoIterator for Choice<T> {
    type Item = T;
    type IntoIter = smallvec::IntoIter<[T; 8]>;

    fn into_iter(self) -> Self::IntoIter {
        self.values.into_iter()
    }
}

impl<T: Clone + Display> Display for Choice<T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.values[0])?;
        if self.values.len() > 1 {
            let alternatives = self.values[1..]
                .iter()
                .map(|alt| alt.to_string())
                .collect::<Vec<_>>()
                .join(", ");
            write!(f, " | {}", alternatives)?;
        }
        Ok(())
    }
}
