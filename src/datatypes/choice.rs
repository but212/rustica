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
//! assert_eq!(*doubled.first(), 10);
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
use std::fmt::{Debug, Display, Formatter};

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
/// assert_eq!(*choice.value(), 1);
/// assert_eq!(choice.alternatives().len(), 3);
/// ```
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Choice<T> {
    /// A vector of values.
    values: Vec<T>,
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
    /// assert_eq!(*choice.first(), 1);
    /// assert_eq!(choice.alternatives(), &vec![2, 3, 4]);
    /// ```
    pub fn new(first: T, alternatives: Vec<T>) -> Self {
        let mut values = Vec::with_capacity(alternatives.len() + 1);
        values.push(first);
        values.extend(alternatives);
        Self { values }
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
    /// assert_eq!(*choice.first(), 42);
    /// ```
    pub fn first(&self) -> &T {
        &self.values[0]
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
    pub fn len(&self) -> usize {
        self.values.len()
    }

    pub fn is_empty(&self) -> bool {
        self.values.is_empty()
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
    /// assert_eq!(*new_choice.first(), 1);
    /// assert_eq!(new_choice.alternatives(), &[2, 3, 4]);
    /// ```
    pub fn add_alternative(&self, item: &T) -> Self
    where
        T: Clone,
    {
        let mut new_values = self.values.clone();
        new_values.push(item.clone());
        Self { values: new_values }
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
    /// assert_eq!(*new_choice.first(), 1);
    /// assert_eq!(new_choice.alternatives(), &[2, 4]);
    /// ```
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
        Self { values: new_values }
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
    /// assert_eq!(*doubled.first(), 2);
    /// assert_eq!(doubled.alternatives(), &[4, 6, 8]);
    /// ```
    pub fn map_alternatives<F, U>(&self, f: F) -> Choice<U>
    where
        F: Fn(&T) -> U,
    {
        Choice {
            values: self.values.iter().map(f).collect(),
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
    /// assert_eq!(*flattened.first(), 1);
    /// assert_eq!(flattened.alternatives(), &[2, 3, 4, 5]);
    /// ```
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
    pub fn partition(vec: Vec<T>, predicate: impl Fn(&T) -> bool) -> Self {
        let position = vec
            .iter()
            .position(predicate)
            .expect("No element satisfies the predicate");

        let mut values = vec;
        let first = values.remove(position);

        Self {
            values: std::iter::once(first).chain(values).collect(),
        }
    }

    /// Creates a new `Choice` from a primary value and any iterable of alternatives.
    pub fn of_many(first: T, alternatives: impl IntoIterator<Item = T>) -> Self {
        Self {
            values: std::iter::once(first).chain(alternatives).collect(),
        }
    }

    /// Creates a new `Choice` from an iterator, taking the first element as the primary value.
    ///
    /// Returns `None` if the iterator is empty.
    pub fn from_iterator(iter: impl IntoIterator<Item = T>) -> Option<Self> {
        let values: Vec<T> = iter.into_iter().collect();
        if values.is_empty() {
            None
        } else {
            Some(Self { values })
        }
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
    /// let ordered = choice.ordered_alternatives();
    ///
    /// assert_eq!(*ordered.first(), 5);
    /// assert_eq!(ordered.alternatives(), &[1, 2, 3, 4]);
    /// ```
    pub fn ordered_alternatives(&self) -> Self
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
        }
    }
}

impl<T: Clone + PartialEq> Choice<T> {
    /// Combines `self` with another `Choice`, preserving both sets of values.
    ///
    /// This operation combines the values from `self` and `other` to create a new
    /// `Choice` instance that includes all values from both choices.
    ///
    /// # Arguments
    ///
    /// * `other` - Another `Choice<T>` to combine with `self`.
    ///
    /// # Returns
    ///
    /// A new `Choice<T>` containing all the values from both `self` and `other`.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::choice::Choice;
    ///
    /// let a = Choice::new(1, vec![2, 3]);
    /// let b = Choice::new(4, vec![5, 6]);
    /// let combined = a.combine(&b);
    ///
    /// assert_eq!(combined.first(), &1);
    /// assert_eq!(combined.alternatives().len(), 5);
    /// assert!(combined.alternatives().contains(&2));
    /// assert!(combined.alternatives().contains(&3));
    /// assert!(combined.alternatives().contains(&4));
    /// assert!(combined.alternatives().contains(&5));
    /// assert!(combined.alternatives().contains(&6));
    /// ```
    pub fn combine(&self, other: &Self) -> Self {
        // Clone everything to avoid moved value issues
        let first = self.values[0].clone();
        let alternatives = self.values[1..].to_vec();
        let b_first = other.values[0].clone();
        let b_alternatives = other.values[1..].to_vec();

        let mut result_alternatives = alternatives;

        // Add b.first to alternatives if it's not already in alternatives
        if !result_alternatives.contains(&b_first) {
            result_alternatives.push(b_first);
        }

        // Add b.alternatives to alternatives if they're not already in alternatives
        for alt in b_alternatives {
            if !result_alternatives.contains(&alt) {
                result_alternatives.push(alt);
            }
        }

        Self {
            values: std::iter::once(first).chain(result_alternatives).collect(),
        }
    }
}

impl<T> HKT for Choice<T> {
    type Source = T;
    type Output<U> = Choice<U>;
}

impl<T> Identity for Choice<T> {
    fn value(&self) -> &Self::Source {
        &self.values[0]
    }

    fn pure_identity<A>(value: A) -> Self::Output<A> {
        Choice {
            values: vec![value],
        }
    }

    fn into_value(self) -> Self::Source {
        self.values.into_iter().next().unwrap()
    }
}

impl<T> Functor for Choice<T> {
    fn fmap<B, F>(&self, f: F) -> Self::Output<B>
    where
        F: Fn(&Self::Source) -> B,
    {
        Choice {
            values: self.values.iter().map(f).collect(),
        }
    }

    fn fmap_owned<B, F>(self, f: F) -> Self::Output<B>
    where
        F: Fn(Self::Source) -> B,
        Self: Sized,
    {
        Choice {
            values: self.values.into_iter().map(f).collect(),
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
            values: vec![value.clone()],
        }
    }
}

impl<T: Clone> Applicative for Choice<T> {
    fn apply<B, F>(&self, f: &Self::Output<F>) -> Self::Output<B>
    where
        F: Fn(&Self::Source) -> B,
    {
        let first_result = f.first()(&self.values[0]);

        let mut alt_result = Vec::new();

        // Apply each function to the first value
        for f_alt in f.alternatives() {
            alt_result.push(f_alt(&self.values[0]));
        }

        // Apply the first function to each alternative
        for alt in &self.values[1..] {
            alt_result.push(f.first()(alt));
        }

        // Apply each alternative function to each alternative value
        for f_alt in f.alternatives() {
            for alt in &self.values[1..] {
                alt_result.push(f_alt(alt));
            }
        }

        Choice {
            values: std::iter::once(first_result).chain(alt_result).collect(),
        }
    }

    fn apply_owned<B, F>(self, f: Self::Output<F>) -> Self::Output<B>
    where
        F: Fn(Self::Source) -> B,
        Self: Sized,
    {
        let first = self.values[0].clone();
        let alternatives = self.values[1..].to_vec();

        let first_result = f.first()(first.clone());

        let mut alt_result = Vec::new();

        // Apply each function to the first value
        for f_alt in f.alternatives() {
            alt_result.push(f_alt(first.clone()));
        }

        // Apply the first function to each alternative
        for alt in &alternatives {
            alt_result.push(f.first()(alt.clone()));
        }

        // Apply each alternative function to each alternative value
        for f_alt in f.alternatives() {
            for alt in &alternatives {
                alt_result.push(f_alt(alt.clone()));
            }
        }

        Choice {
            values: std::iter::once(first_result).chain(alt_result).collect(),
        }
    }

    fn lift2<B, C, F>(&self, b: &Self::Output<B>, f: F) -> Self::Output<C>
    where
        F: Fn(&Self::Source, &B) -> C,
        B: Clone,
    {
        let first_result = f(&self.values[0], &b.values[0]);

        let mut alt_result = Vec::new();

        // Apply to first and each b alternative
        for b_alt in &b.values[1..] {
            alt_result.push(f(&self.values[0], b_alt));
        }

        // Apply to each self alternative and b first
        for alt in &self.values[1..] {
            alt_result.push(f(alt, &b.values[0]));
        }

        // Apply to each self alternative and each b alternative
        for alt in &self.values[1..] {
            for b_alt in &b.values[1..] {
                alt_result.push(f(alt, b_alt));
            }
        }

        Choice {
            values: std::iter::once(first_result).chain(alt_result).collect(),
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

        // Apply to first and each b alternative
        for b_alt in &b_alternatives {
            alt_result.push(f(first.clone(), b_alt.clone()));
        }

        // Apply to each self alternative and b first
        for alt in &alternatives {
            alt_result.push(f(alt.clone(), b_first.clone()));
        }

        // Apply to each self alternative and each b alternative
        for alt in &alternatives {
            for b_alt in &b_alternatives {
                alt_result.push(f(alt.clone(), b_alt.clone()));
            }
        }

        Choice {
            values: std::iter::once(first_result).chain(alt_result).collect(),
        }
    }

    fn lift3<B, C, D, F>(&self, b: &Self::Output<B>, c: &Self::Output<C>, f: F) -> Self::Output<D>
    where
        F: Fn(&Self::Source, &B, &C) -> D,
        B: Clone,
        C: Clone,
        Self::Source: Clone,
    {
        let first_result = f(&self.values[0], &b.values[0], &c.values[0]);

        let mut alt_result = Vec::new();

        // Various combinations of values from a, b, c
        for b_alt in &b.values[1..] {
            alt_result.push(f(&self.values[0], b_alt, &c.values[0]));
        }

        for c_alt in &c.values[1..] {
            alt_result.push(f(&self.values[0], &b.values[0], c_alt));
        }

        for a_alt in &self.values[1..] {
            alt_result.push(f(a_alt, &b.values[0], &c.values[0]));
        }

        for b_alt in &b.values[1..] {
            for c_alt in &c.values[1..] {
                alt_result.push(f(&self.values[0], b_alt, c_alt));
            }
        }

        for a_alt in &self.values[1..] {
            for b_alt in &b.values[1..] {
                alt_result.push(f(a_alt, b_alt, &c.values[0]));
            }
        }

        for a_alt in &self.values[1..] {
            for c_alt in &c.values[1..] {
                alt_result.push(f(a_alt, &b.values[0], c_alt));
            }
        }

        for a_alt in &self.values[1..] {
            for b_alt in &b.values[1..] {
                for c_alt in &c.values[1..] {
                    alt_result.push(f(a_alt, b_alt, c_alt));
                }
            }
        }

        Choice {
            values: std::iter::once(first_result).chain(alt_result).collect(),
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

        for a_alt in &alternatives {
            alt_result.push(f(a_alt.clone(), b_first.clone(), c_first.clone()));
        }

        for b_alt in &b_alternatives {
            for c_alt in &c_alternatives {
                alt_result.push(f(first.clone(), b_alt.clone(), c_alt.clone()));
            }
        }

        for a_alt in &alternatives {
            for b_alt in &b_alternatives {
                alt_result.push(f(a_alt.clone(), b_alt.clone(), c_first.clone()));
            }
        }

        for a_alt in &alternatives {
            for c_alt in &c_alternatives {
                alt_result.push(f(a_alt.clone(), b_first.clone(), c_alt.clone()));
            }
        }

        for a_alt in &alternatives {
            for b_alt in &b_alternatives {
                for c_alt in &c_alternatives {
                    alt_result.push(f(a_alt.clone(), b_alt.clone(), c_alt.clone()));
                }
            }
        }

        Choice {
            values: std::iter::once(first_result).chain(alt_result).collect(),
        }
    }
}

impl<T: Clone> Semigroup for Choice<T> {
    fn combine(&self, other: &Self) -> Self {
        let mut combined_values = self.values.clone();
        combined_values.extend(other.values.clone());
        Choice {
            values: combined_values,
        }
    }

    fn combine_owned(self, other: Self) -> Self {
        self.combine(&other)
    }
}

impl<T: Clone + Default> Monoid for Choice<T> {
    fn empty() -> Self {
        Choice {
            values: vec![T::default()],
        }
    }
}

impl<T> IntoIterator for Choice<T> {
    type Item = T;
    type IntoIter = std::vec::IntoIter<T>;

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
