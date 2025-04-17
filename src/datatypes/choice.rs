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

use std::fmt::{Debug, Display, Formatter};
use std::hash::Hash;
use std::iter::FromIterator;
use std::sync::Arc;

use smallvec::SmallVec;

use crate::prelude::*;
use crate::traits::applicative::Applicative;
use crate::traits::foldable::Foldable;
use crate::traits::monad::Monad;
use crate::traits::monoid::Monoid;
use crate::traits::pure::Pure;
use crate::traits::semigroup::Semigroup;

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
/// assert_eq!(choice.alternatives(), &[2, 3, 4]);
/// ```
#[repr(transparent)]
#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Choice<T> {
    values: Arc<SmallVec<[T; 8]>>,
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
            values: Arc::new(SmallVec::new()),
        }
    }

    /// Creates a new `Choice` with a single item.
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
    pub fn new<I>(item: T, alternatives: I) -> Self
    where
        I: IntoIterator<Item = T>,
        I::IntoIter: Iterator,
    {
        let alternatives_iter = alternatives.into_iter();
        let size = alternatives_iter.size_hint().0;
        let mut values = SmallVec::<[T; 8]>::with_capacity(size + 1);
        values.push(item);
        values.extend(alternatives_iter);

        Self {
            values: Arc::new(values),
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
        self.values.as_ref().first()
    }

    /// Get a reference to the alternatives (all items except the first).
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
        // Return empty slice if no alternatives exist
        if self.values.len() <= 1 {
            &[]
        } else {
            &self.values[1..]
        }
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
    /// let new_choice = choice.add_alternatives(vec![4, 5]);
    ///
    /// assert_eq!(*new_choice.first().unwrap(), 1);
    /// assert_eq!(new_choice.alternatives(), &[2, 3, 4, 5]);
    /// ```
    #[inline]
    pub fn add_alternatives<I>(self, items: I) -> Self
    where
        T: Clone,
        I: IntoIterator<Item = T>,
    {
        let mut new_values = Arc::clone(&self.values);
        Arc::make_mut(&mut new_values).extend(items);
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
    /// assert_eq!(*new_choice.first().unwrap(), 1);
    /// assert_eq!(new_choice.alternatives(), &[2, 4]);
    /// ```
    #[inline]
    pub fn remove_alternative(&self, index: usize) -> Self
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

        let mut new_values = self.values.as_ref().clone();
        new_values.remove(index + 1); // +1 because alternatives start at index 1

        Self {
            values: Arc::new(new_values),
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
    /// assert_eq!(*filtered.first().unwrap(), 2);
    /// assert_eq!(filtered.alternatives(), &[4]);
    /// ```
    #[inline]
    pub fn filter<P>(&self, predicate: P) -> Self
    where
        P: Fn(&T) -> bool,
        T: Clone,
    {
        let filtered: SmallVec<[T; 8]> = self.iter().filter(|v| predicate(v)).cloned().collect();

        match filtered.len() {
            0 => Self::new_empty(),
            _ => Self {
                values: Arc::new(filtered),
            },
        }
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
    /// let doubled = choice.fmap_alternatives(|&x| x * 2);
    ///
    /// assert_eq!(*doubled.first().unwrap(), 1);
    /// assert_eq!(doubled.alternatives(), &[4, 6, 8]);
    /// ```
    #[inline]
    pub fn fmap_alternatives<F>(&self, f: F) -> Choice<T>
    where
        F: Fn(&T) -> T,
        T: Clone,
    {
        if self.values.len() <= 1 {
            return self.clone();
        }

        let values = self.values.as_ref();
        let primary = values[0].clone();

        let mut alternatives: SmallVec<[T; 8]> = SmallVec::with_capacity(values.len() - 1);
        for i in 1..values.len() {
            alternatives.push(f(&values[i]));
        }

        let mut new_values = SmallVec::with_capacity(values.len());
        new_values.push(primary);
        new_values.extend(alternatives);

        Self {
            values: Arc::new(new_values),
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
        if self.values.is_empty() {
            return Choice::new_empty();
        }

        let primary = self.first().unwrap().clone();
        let mut primary_iter = primary.into_iter();

        match primary_iter.next() {
            Some(first_item) => {
                // Pre-calculate total capacity needed
                let alternatives_count = self
                    .alternatives()
                    .iter()
                    .map(|alt| alt.clone().into_iter().size_hint().0)
                    .sum::<usize>();

                // Add remaining items from primary + space for all alternatives
                let total_capacity = primary_iter.size_hint().0 + alternatives_count;
                let mut alternatives = SmallVec::<[I; 8]>::with_capacity(total_capacity);

                // Add remaining items from the primary value
                alternatives.extend(primary_iter);

                // Add all items from all alternatives
                for alt in self.alternatives() {
                    alternatives.extend(alt.clone().into_iter());
                }

                Choice::new(first_item, alternatives)
            },
            None => panic!("Primary value was an empty iterator in Choice::flatten"),
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
    /// let choice = Choice::of_many(vec![1, 2, 3, 4]);
    /// assert_eq!(*choice.first().unwrap(), 1);
    /// assert_eq!(choice.alternatives(), &[2, 3, 4]);
    /// ```
    #[inline]
    pub fn of_many<I>(many: I) -> Self
    where
        I: IntoIterator<Item = T>,
        T: Clone,
    {
        let mut iter = many.into_iter();

        if let Some(first) = iter.next() {
            // Try to get a size hint for capacity planning
            let (lower, _) = iter.size_hint();
            let mut values = SmallVec::<[T; 8]>::with_capacity(lower + 1);

            values.push(first);
            values.extend(iter);

            Self {
                values: Arc::new(values),
            }
        } else {
            Self::new_empty()
        }
    }

    /// Returns a `Choice` containing only the values that satisfy the predicate.
    ///
    /// If the primary value doesn't satisfy the predicate, the first alternative that does
    /// becomes the new primary value.
    ///
    /// # Arguments
    ///
    /// * `predicate` - A function that takes a reference to a value and returns a boolean
    ///
    /// # Returns
    ///
    /// A new `Choice` with only the values that satisfy the predicate
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::datatypes::choice::Choice;
    ///
    /// let choice = Choice::new(1, vec![2, 3, 4, 5]);
    /// let even = choice.filter_values(|x: &i32| x % 2 == 0);
    ///
    /// assert_eq!(*even.first().unwrap(), 2);
    /// assert_eq!(even.alternatives(), &[4]);
    /// ```
    #[inline]
    pub fn filter_values<F>(&self, predicate: F) -> Self
    where
        T: Clone,
        F: Fn(&T) -> bool,
    {
        let filtered: SmallVec<[T; 8]> = self.iter().filter(|v| predicate(v)).cloned().collect();

        match filtered.len() {
            0 => Self::new_empty(),
            _ => Self {
                values: Arc::new(filtered),
            },
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

    /// Swaps the first value with the alternative at the specified index, consuming the original.
    ///
    /// # Arguments
    ///
    /// * `alt_index` - The index of the alternative to swap with the first value
    ///
    /// # Returns
    ///
    /// A new Choice with the first value swapped with the specified alternative
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::datatypes::choice::Choice;
    ///
    /// let choice = Choice::new(1, vec![2, 3, 4]);
    /// let swapped = choice.swap_with_alternative(1);
    /// assert_eq!(*swapped.first().unwrap(), 3);
    /// assert_eq!(swapped.alternatives(), &[2, 1, 4]);
    /// ```
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

        let actual_alt_index = alt_index + 1; // +1 to account for first value

        let mut values = Arc::try_unwrap(self.values).unwrap_or_else(|arc| (*arc).clone());

        // Swap the first value with the alternative
        values.swap(0, actual_alt_index);

        Self {
            values: Arc::new(values),
        }
    }
}

impl<T> HKT for Choice<T> {
    type Source = T;
    type Output<U> = Choice<U>;
}

impl<T> Pure for Choice<T> {
    fn pure<A: Clone>(value: &A) -> Self::Output<A> {
        Choice::new(value.clone(), vec![])
    }

    fn pure_owned<A: Clone>(value: A) -> Self::Output<A> {
        Choice::new(value, vec![])
    }
}

impl<T: Clone> Identity for Choice<T> {
    #[inline]
    fn value(&self) -> &Self::Source {
        self.first().expect("Cannot get value from an empty Choice")
    }

    #[inline]
    fn pure_identity<A>(value: A) -> Self::Output<A> {
        Choice::new(value, vec![])
    }

    #[inline]
    fn into_value(self) -> Self::Source {
        match Arc::try_unwrap(self.values) {
            Ok(values) => values.into_iter().next().expect("Cannot get value from an empty Choice"),
            Err(arc) => arc.first().cloned().expect("Cannot get value from an empty Choice"),
        }
    }
}

impl<T: Clone> Functor for Choice<T> {
    #[inline]
    fn fmap<B, F>(&self, f: F) -> Self::Output<B>
    where
        F: Fn(&T) -> B,
        B: Clone,
    {
        if self.values.is_empty() {
            return Choice::new_empty();
        }

        let values = self.values.as_ref();
        let primary = f(&values[0]);
        let alternatives: Vec<B> = values[1..].iter().map(f).collect();

        Choice::new(primary, alternatives)
    }

    #[inline]
    fn fmap_owned<B, F>(self, f: F) -> Self::Output<B>
    where
        F: FnMut(T) -> B,
    {
        if self.values.is_empty() {
            return Choice::new_empty();
        }

        match Arc::try_unwrap(self.values) {
            Ok(mut values) => {
                let mut f = f;
                let primary = f(values.remove(0));
                let alternatives: Vec<B> = values.into_iter().map(f).collect();
                Choice::new(primary, alternatives)
            },
            Err(arc) => {
                let values = arc.as_ref();
                let mut f = f;
                let primary = f(values[0].clone());
                let alternatives: Vec<B> = values[1..].iter().cloned().map(&mut f).collect();
                Choice::new(primary, alternatives)
            },
        }
    }
}

impl<T: Clone> Monad for Choice<T> {
    #[inline]
    fn bind<U, F>(&self, f: F) -> Self::Output<U>
    where
        F: Fn(&T) -> Self::Output<U>,
        U: Clone,
    {
        if self.values.is_empty() {
            return Choice::new_empty();
        }

        let self_values = self.values.as_ref();
        let first_choice = f(&self_values[0]);

        if first_choice.values.is_empty() {
            return Choice::new_empty();
        }

        let first_choice_values = first_choice.values.as_ref();
        let first = first_choice_values[0].clone();

        let capacity = first_choice_values.len() - 1 + (self_values.len() - 1) * 2;
        let mut alternatives = Vec::with_capacity(capacity);

        // Add alternatives from primary choice
        alternatives.extend_from_slice(&first_choice_values[1..]);

        // Apply f to each alternative and collect all values
        for alt in &self_values[1..] {
            let alt_choice = f(alt);
            alternatives.extend_from_slice(alt_choice.values.as_ref());
        }

        Choice::new(first, alternatives)
    }

    #[inline]
    fn bind_owned<U, F>(self, f: F) -> Self::Output<U>
    where
        F: Fn(Self::Source) -> Self::Output<U>,
        U: Clone,
    {
        if self.values.is_empty() {
            return Choice::new_empty();
        }

        match Arc::try_unwrap(self.values) {
            Ok(mut values) => {
                let primary_choice = f(values.remove(0));

                if primary_choice.values.is_empty() {
                    return Choice::new_empty();
                }

                let primary_choice_values = primary_choice.values.as_ref();
                let first = primary_choice_values[0].clone();

                let mut alternatives =
                    Vec::with_capacity(primary_choice_values.len() - 1 + values.len() * 2);

                alternatives.extend_from_slice(&primary_choice_values[1..]);

                for alt in values {
                    let alt_choice = f(alt);
                    alternatives.extend(alt_choice.values.iter().cloned());
                }

                Choice::new(first, alternatives)
            },
            Err(arc) => {
                let values = arc.as_ref();
                let primary_choice = f(values[0].clone());

                if primary_choice.values.is_empty() {
                    return Choice::new_empty();
                }

                let first = primary_choice.first().unwrap().clone();

                let mut alternatives =
                    Vec::with_capacity(primary_choice.alternatives().len() + values.len() * 2);

                alternatives.extend_from_slice(primary_choice.alternatives());

                for alt in &values[1..] {
                    let alt_choice = f(alt.clone());
                    alternatives.extend(alt_choice.values.iter().cloned());
                }

                Choice::new(first, alternatives)
            },
        }
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

        // Calculate capacity for alternatives
        let capacity = primary_choice.alternatives().len() + self.alternatives().len() * 2;
        let mut alternatives = Vec::with_capacity(capacity);

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

        match Arc::try_unwrap(self.values) {
            Ok(mut values) => {
                let primary_value = values.remove(0);
                let primary_choice: Self::Output<U> = primary_value.into();

                if primary_choice.values.is_empty() {
                    return Choice::new_empty();
                }

                let first = primary_choice.first().unwrap().clone();

                // Calculate capacity for alternatives
                let capacity = primary_choice.alternatives().len() + values.len() * 2;
                let mut alternatives = Vec::with_capacity(capacity);

                // Add alternatives from primary choice
                alternatives.extend_from_slice(primary_choice.alternatives());

                // Add all values from alternative choices
                for alt in values {
                    let alt_choice: Self::Output<U> = alt.into();
                    alternatives.extend_from_slice(alt_choice.values.as_ref());
                }

                Choice::new(first, alternatives)
            },
            Err(arc) => {
                let values = arc.as_ref();
                let primary_choice: Self::Output<U> = values[0].clone().into();

                if primary_choice.values.is_empty() {
                    return Choice::new_empty();
                }

                let first = primary_choice.first().unwrap().clone();

                // Calculate capacity for alternatives
                let capacity = primary_choice.alternatives().len() + (values.len() - 1) * 2;
                let mut alternatives = Vec::with_capacity(capacity);

                // Add alternatives from primary choice
                alternatives.extend_from_slice(primary_choice.alternatives());

                // Add all values from alternative choices
                for alt in &values[1..] {
                    let alt_choice: Self::Output<U> = alt.clone().into();
                    alternatives.extend_from_slice(alt_choice.values.as_ref());
                }

                Choice::new(first, alternatives)
            },
        }
    }
}

impl<T: Clone> Semigroup for Choice<T> {
    #[inline]
    fn combine(&self, other: &Self) -> Self {
        if self.values.is_empty() {
            return other.clone();
        }

        if other.values.is_empty() {
            return self.clone();
        }

        // Get a copy of the values since we can't move out of Arc
        let self_values = self.values.as_ref();
        let other_values = other.values.as_ref();

        // Take the primary value from self
        let primary = self_values[0].clone();

        // Calculate capacity for alternatives
        let capacity = self_values.len() - 1 + other_values.len();
        let mut alternatives = Vec::with_capacity(capacity);

        // Add self alternatives (excluding primary)
        alternatives.extend_from_slice(&self_values[1..]);

        // Add all other values (including primary)
        alternatives.extend_from_slice(other_values);

        Choice::new(primary, alternatives)
    }

    #[inline]
    fn combine_owned(self, other: Self) -> Self {
        if self.values.is_empty() {
            return other;
        }

        if other.values.is_empty() {
            return self;
        }

        match Arc::try_unwrap(self.values) {
            Ok(mut self_values) => {
                let primary = self_values.remove(0);

                // Calculate capacity for alternatives
                let capacity = self_values.len() + other.values.len();
                let mut alternatives = Vec::with_capacity(capacity);

                // Add self alternatives
                alternatives.extend(self_values);

                // Add all other values
                alternatives.extend_from_slice(other.values.as_ref());

                Choice::new(primary, alternatives)
            },
            Err(arc) => {
                let self_values = arc.as_ref();
                let primary = self_values[0].clone();

                // Calculate capacity for alternatives
                let capacity = self_values.len() - 1 + other.values.len();
                let mut alternatives = Vec::with_capacity(capacity);

                // Add self alternatives (excluding primary)
                alternatives.extend_from_slice(&self_values[1..]);

                // Add all other values
                alternatives.extend_from_slice(other.values.as_ref());

                Choice::new(primary, alternatives)
            },
        }
    }
}

impl<T: Clone + Default> Monoid for Choice<T> {
    fn empty() -> Self {
        Self::new(T::default(), vec![])
    }
}

impl<T: Clone> Applicative for Choice<T> {
    #[inline]
    fn apply<B, F>(&self, f: &Self::Output<F>) -> Self::Output<B>
    where
        F: Fn(&T) -> B,
        B: Clone,
    {
        if self.values.is_empty() || f.values.is_empty() {
            return Choice::new_empty();
        }

        let self_values = self.values.as_ref();
        let f_values = f.values.as_ref();
        let f_first = &f_values[0];

        let primary = f_first(&self_values[0]);

        // Calculate capacity for alternatives vector
        let capacity = (f_values.len() - 1) + (self_values.len() - 1) * f_values.len();
        let mut alternatives = Vec::with_capacity(capacity);

        // First, apply additional functions to the primary value (f[1..] with self[0])
        for f_alt in &f_values[1..] {
            alternatives.push(f_alt(&self_values[0]));
        }

        // Then self[1..] with all of f
        for self_alt in &self_values[1..] {
            // First apply the primary function to self alternatives
            alternatives.push(f_first(self_alt));

            // Then apply alternative functions to self alternatives
            for f_alt in &f_values[1..] {
                alternatives.push(f_alt(self_alt));
            }
        }

        Choice::new(primary, alternatives)
    }

    #[inline]
    fn apply_owned<B, F>(self, f: Self::Output<F>) -> Self::Output<B>
    where
        F: Fn(T) -> B,
        B: Clone,
    {
        if self.values.is_empty() || f.values.is_empty() {
            return Choice::new_empty();
        }

        match Arc::try_unwrap(self.values) {
            Ok(mut self_values) => {
                let f_values = f.values.as_ref();
                let f_first = &f_values[0];

                let first_value = self_values.remove(0);
                let primary = f_first(first_value);

                // Calculate capacity for alternatives vector
                let capacity = (f_values.len() - 1) + self_values.len() * f_values.len();
                let mut alternatives = Vec::with_capacity(capacity);

                // First, apply additional functions to the primary value (f[1..] with self[0])
                for f_alt in &f_values[1..] {
                    if !self_values.is_empty() {
                        alternatives.push(f_alt(self_values[0].clone()));
                    }
                }

                // Then self[1..] with all of f
                for self_alt in self_values {
                    // First apply the primary function to self alternatives
                    alternatives.push(f_first(self_alt.clone()));

                    // Then apply alternative functions to self alternatives
                    for f_alt in &f_values[1..] {
                        alternatives.push(f_alt(self_alt.clone()));
                    }
                }

                Choice::new(primary, alternatives)
            },
            Err(arc) => {
                let self_values = arc.as_ref();
                let f_values = f.values.as_ref();
                let f_first = &f_values[0];

                let primary = f_first(self_values[0].clone());

                // Calculate capacity for alternatives vector
                let capacity = (f_values.len() - 1) + (self_values.len() - 1) * f_values.len();
                let mut alternatives = Vec::with_capacity(capacity);

                // First, apply additional functions to the primary value (f[1..] with self[0])
                for f_alt in &f_values[1..] {
                    alternatives.push(f_alt(self_values[0].clone()));
                }

                // Then self[1..] with all of f
                for self_alt in &self_values[1..] {
                    // First apply the primary function to self alternatives
                    alternatives.push(f_first(self_alt.clone()));

                    // Then apply alternative functions to self alternatives
                    for f_alt in &f_values[1..] {
                        alternatives.push(f_alt(self_alt.clone()));
                    }
                }

                Choice::new(primary, alternatives)
            },
        }
    }

    fn lift2<B, C, F>(&self, b: &Self::Output<B>, f: F) -> Self::Output<C>
    where
        F: Fn(&T, &B) -> C,
        B: Clone,
        C: Clone,
    {
        if self.values.is_empty() || b.values.is_empty() {
            return Choice::new_empty();
        }

        // Get references to the values
        let self_values = self.values.as_ref();
        let b_values = b.values.as_ref();

        let primary = f(&self_values[0], &b_values[0]);

        // Calculate capacity for alternatives vector
        let capacity = self_values.len() * b_values.len() - 1;
        let mut alternatives = Vec::with_capacity(capacity);

        for (i, self_val) in self_values.iter().enumerate() {
            for (j, b_val) in b_values.iter().enumerate() {
                if i == 0 && j == 0 {
                    continue; // Skip primary
                }
                alternatives.push(f(self_val, b_val));
            }
        }

        Choice::new(primary, alternatives)
    }

    fn lift2_owned<B, C, F>(self, b: Self::Output<B>, f: F) -> Self::Output<C>
    where
        F: Fn(T, B) -> C,
        B: Clone,
        C: Clone,
    {
        if self.values.is_empty() || b.values.is_empty() {
            return Choice::new_empty();
        }

        let primary = f(
            self.values.as_ref()[0].clone(),
            b.values.as_ref()[0].clone(),
        );

        let capacity = self.len() * b.len() - 1;
        let mut alternatives = Vec::with_capacity(capacity);

        for (i, a) in self.iter().enumerate() {
            for (j, b_val) in b.iter().enumerate() {
                if i == 0 && j == 0 {
                    continue; // Skip primary
                }
                alternatives.push(f(a.clone(), b_val.clone()));
            }
        }

        Choice::new(primary, alternatives)
    }

    fn lift3<B, C, D, F>(&self, b: &Self::Output<B>, c: &Self::Output<C>, f: F) -> Self::Output<D>
    where
        F: Fn(&T, &B, &C) -> D,
        B: Clone,
        C: Clone,
        D: Clone,
    {
        if self.values.is_empty() || b.values.is_empty() || c.values.is_empty() {
            return Choice::new_empty();
        }

        // Get references to the values
        let self_values = self.values.as_ref();
        let b_values = b.values.as_ref();
        let c_values = c.values.as_ref();

        let primary = f(&self_values[0], &b_values[0], &c_values[0]);

        // Calculate capacity for alternatives vector
        let capacity = self_values.len() * b_values.len() * c_values.len() - 1;
        let mut alternatives = Vec::with_capacity(capacity);

        for (i, self_val) in self_values.iter().enumerate() {
            for (j, b_val) in b_values.iter().enumerate() {
                for (k, c_val) in c_values.iter().enumerate() {
                    if i == 0 && j == 0 && k == 0 {
                        continue; // Skip primary
                    }
                    alternatives.push(f(self_val, b_val, c_val));
                }
            }
        }

        Choice::new(primary, alternatives)
    }

    fn lift3_owned<B, C, D, G>(
        self, b: Self::Output<B>, c: Self::Output<C>, f: G,
    ) -> Self::Output<D>
    where
        G: Fn(T, B, C) -> D,
        B: Clone,
        C: Clone,
        D: Clone,
    {
        if self.values.is_empty() || b.values.is_empty() || c.values.is_empty() {
            return Choice::new_empty();
        }

        let primary = f(
            self.values.as_ref()[0].clone(),
            b.values.as_ref()[0].clone(),
            c.values.as_ref()[0].clone(),
        );

        let capacity = self.len() * b.len() * c.len() - 1;
        let mut alternatives = Vec::with_capacity(capacity);

        for (i, a) in self.iter().enumerate() {
            for (j, b_val) in b.iter().enumerate() {
                for (k, c_val) in c.iter().enumerate() {
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

        // Create a new choice with self's primary and all values
        let mut values = Vec::with_capacity(self.values.len() + other.values.len());
        values.extend_from_slice(self.values.as_ref());
        values.extend_from_slice(other.values.as_ref());

        Choice::new(values[0].clone(), values[1..].to_vec())
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
        let values: Vec<T> = self.iter().cloned().collect();
        Choice::new(values, vec![])
    }
}

impl<'a, T> IntoIterator for &'a Choice<T> {
    type Item = &'a T;
    type IntoIter = std::slice::Iter<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        self.values.as_ref().iter()
    }
}

impl<T: Clone> IntoIterator for Choice<T> {
    type Item = T;
    type IntoIter = std::vec::IntoIter<T>;

    fn into_iter(self) -> Self::IntoIter {
        let values = self.values.as_ref().to_vec();
        values.into_iter()
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

impl<T: Clone> Foldable for Choice<T> {
    fn fold_left<B, F>(&self, initial: &B, f: F) -> B
    where
        F: Fn(&B, &Self::Source) -> B,
        B: Clone,
    {
        let mut acc = initial.clone();
        for value in self.iter() {
            acc = f(&acc, value);
        }
        acc
    }

    fn fold_right<B, F>(&self, initial: &B, f: F) -> B
    where
        F: Fn(&Self::Source, &B) -> B,
        B: Clone,
    {
        // Convert to Vec, then iterate in reverse
        let values: Vec<T> = self.values.iter().cloned().collect();
        let mut acc = initial.clone();
        for value in values.into_iter().rev() {
            acc = f(&value, &acc);
        }
        acc
    }
}

impl<T> FromIterator<T> for Choice<T> {
    fn from_iter<I: IntoIterator<Item = T>>(iter: I) -> Self {
        let collected: SmallVec<[T; 8]> = iter.into_iter().collect();
        match collected.len() {
            0 => Self::new_empty(),
            _ => Self {
                values: Arc::new(collected),
            },
        }
    }
}

impl<T: Clone> FromIterator<Choice<T>> for Choice<T> {
    fn from_iter<I: IntoIterator<Item = Choice<T>>>(iter: I) -> Self {
        let mut all_values: SmallVec<[T; 8]> = SmallVec::new();
        for choice in iter {
            all_values.extend(choice.values.as_ref().iter().cloned());
        }

        if all_values.is_empty() {
            return Self::new_empty();
        }

        let first = all_values[0].clone();
        let alternatives: Vec<T> = all_values[1..].to_vec();

        Self::new(first, alternatives)
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
        choice.values.as_ref().iter().cloned().collect()
    }
}

impl<T: Clone + Default> Default for Choice<T> {
    fn default() -> Self {
        Self::new(T::default(), vec![])
    }
}

impl<T: Clone> std::iter::Sum for Choice<T> {
    fn sum<I: Iterator<Item = Self>>(iter: I) -> Self {
        Choice::from_iter(iter)
    }
}
