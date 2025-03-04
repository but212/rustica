//! # Choice Datatype
//!
//! The `Choice` datatype represents a value with multiple alternatives, providing a way to work with 
//! values that have multiple possible options. It is a powerful abstraction for modeling non-deterministic 
//! computations and representing multiple possible outcomes.
//!
//! ## Functional Programming Context
//!
//! In functional programming, the `Choice` type is commonly used for:
//!
//! - Representing non-deterministic computations
//! - Modeling multiple possible outcomes of a calculation
//! - Implementing search algorithms with backtracking
//! - Expressing computations that can produce multiple results
//! - Building parsers and combinatorial algorithms
//!
//! ## Type Class Implementations
//!
//! The `Choice` type implements several important functional programming abstractions:
//!
//! - `Functor`: Maps a function over all values in the `Choice`
//! - `Applicative`: Applies functions contained in one `Choice` to values in another `Choice`
//! - `Monad`: Chains computations that produce multiple results
//! - `Semigroup`: Combines two `Choice` values, merging their alternatives
//! - `Monoid`: Provides an identity element for the `Choice` type
//! - `Identity`: Accesses the primary value
//! - `Pure`: Creates a `Choice` with a single value
//!
//! ## Structure
//!
//! The `Choice<T>` struct contains:
//! - A primary value of type `T`
//! - A vector of alternative values, also of type `T`
//!
//! ## Basic Usage
//!
//! ```rust
//! use rustica::datatypes::choice::Choice;
//! use rustica::prelude::*;
//! 
//! // Create a Choice with a primary value and alternatives
//! let numbers = Choice::new(1, vec![2, 3, 4]);
//! 
//! // Access the primary value and alternatives
//! assert_eq!(*numbers.first(), 1);
//! assert_eq!(numbers.alternatives(), &vec![2, 3, 4]);
//! 
//! // Transform all values using fmap (Functor)
//! let doubled = numbers.fmap(|x| x * 2);
//! assert_eq!(*doubled.first(), 2);
//! assert_eq!(doubled.alternatives(), &vec![4, 6, 8]);
//! 
//! // Chain operations that produce multiple results (Monad)
//! let result = numbers.bind(|&x| Choice::new(x * 10, vec![x * 100]));
//! assert_eq!(*result.first(), 10);
//! assert_eq!(result.alternatives(), &vec![100, 20, 200, 30, 300, 40, 400]);
//! 
//! // Combine two Choice values (Semigroup)
//! let more_numbers = Choice::new(5, vec![6, 7]);
//! let combined = numbers.combine(&more_numbers);
//! assert_eq!(*combined.first(), 1);
//! assert_eq!(combined.alternatives(), &vec![2, 3, 4, 5, 6, 7]);
//! ```
use crate::traits::{
    hkt::HKT,
    identity::Identity,
    functor::Functor,
    pure::Pure,
    applicative::Applicative,
    monad::Monad,
    semigroup::Semigroup,
    monoid::Monoid,
};
use std::fmt::{Debug, Display, Formatter, Result};

/// A type representing a value with multiple alternatives.
///
/// `Choice<T>` encapsulates a primary value of type `T` along with a collection
/// of alternative values of the same type. This structure is useful in scenarios
/// where multiple options or choices need to be represented and manipulated.
///
/// # Type Parameters
///
/// * `T`: The type of the values stored in this `Choice`.
///
/// # Fields
///
/// * `first`: The primary value of type `T`.
/// * `alternatives`: A vector containing alternative values of type `T`.
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
#[derive(Clone)]
pub struct Choice<T> {
    /// The primary value.
    first: T,
    /// A vector of alternative values.
    alternatives: Vec<T>,
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
        Self { first, alternatives }
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
        &self.first
    }

    /// Returns a reference to the vector of alternative values.
    ///
    /// # Returns
    ///
    /// A reference to the `Vec<T>` containing alternative values of type `T`
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::datatypes::choice::Choice;
    ///
    /// let choice = Choice::new(42, vec![1, 2, 3]);
    /// assert_eq!(choice.alternatives(), &vec![1, 2, 3]);
    /// ```
    pub fn alternatives(&self) -> &Vec<T> {
        &self.alternatives
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
        !self.alternatives.is_empty()
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
        self.alternatives.len() + 1
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
    /// assert_eq!(new_choice.alternatives(), &vec![2, 3, 4]);
    /// ```
    pub fn add_alternative(&self, item: &T) -> Self
    where
        T: Clone,
    {
        let mut new_alternatives = Vec::with_capacity(self.alternatives.len() + 1);
        new_alternatives.extend_from_slice(&self.alternatives);
        new_alternatives.push(item.clone());
        Choice::new(self.first.clone(), new_alternatives)
    }

    /// Removes an alternative at the specified index and returns a new `Choice`.
    ///
    /// # Arguments
    ///
    /// * `index` - The index of the alternative to remove.
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
    /// assert_eq!(new_choice.alternatives(), &vec![2, 4]);
    /// ```
    pub fn remove_alternative(&self, index: usize) -> Self
    where
        T: Clone,
    {
        let mut new_alternatives = self.alternatives.clone();
        new_alternatives.remove(index);
        Choice::new(self.first.clone(), new_alternatives)
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
        T: Eq,
    {
        self.alternatives.iter().position(|x| x == value)
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
    /// assert_eq!(doubled.alternatives(), &vec![4, 6, 8]);
    /// ```
    pub fn map_alternatives<F>(&self, f: F) -> Self
    where
        T: Clone,
        F: Fn(&T) -> T,
    {
        Choice::new(f(&self.first), self.alternatives.iter().map(f).collect())
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
    /// Panics if the primary value (`self.first`) is an empty iterator.
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
    /// assert_eq!(flattened.alternatives(), &vec![2, 3, 4, 5]);
    /// ```
    pub fn flatten(&self) -> Choice<T::Item>
    where
        T: Clone + IntoIterator,
        T::Item: Clone,
    {
        let first = self.first.clone().into_iter().next().unwrap();
        let mut flattened_alternatives = Vec::new();
        flattened_alternatives.extend(self.first.clone().into_iter().skip(1));
        flattened_alternatives.extend(self.alternatives.iter().flat_map(|x| x.clone().into_iter()));
        Choice::new(first, flattened_alternatives)
    }

    pub fn partition(vec: Vec<T>, predicate: impl Fn(&T) -> bool) -> Self {
        let mut first = None;
        let mut alternatives = Vec::new();
        
        for item in vec {
            match (&mut first, predicate(&item)) {
                (None, true) => first = Some(item),
                (_, true) => alternatives.push(item),
                (None, false) => {
                    let old_first = std::mem::replace(&mut first, Some(item));
                    if let Some(old) = old_first {
                        alternatives.push(old);
                    }
                }
                (_, false) => alternatives.push(item),
            }
        }
        
        Choice::new(first.expect("Empty vector"), alternatives)
    }

    pub fn of_many(first: T, alternatives: impl IntoIterator<Item = T>) -> Self {
        Choice::new(first, alternatives.into_iter().collect())
    }

    pub fn from_iter(iter: impl IntoIterator<Item = T>) -> Option<Self> {
        let mut iter = iter.into_iter();
        iter.next().map(|first| {
            Choice::new(first, iter.collect())
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
    /// let ordered = choice.ordered_alternatives();
    ///
    /// assert_eq!(*ordered.first(), 5);
    /// assert_eq!(ordered.alternatives(), &vec![1, 2, 3, 4]);
    /// ```
    pub fn ordered_alternatives(&self) -> Self
    where
        T: Ord + Clone,
    {
        use std::collections::BTreeSet;
        
        let mut set = BTreeSet::new();
        for alt in &self.alternatives {
            set.insert(alt.clone());
        }
        
        Choice::new(self.first.clone(), set.into_iter().collect())
    }
}

/// Implements the Higher-Kinded Type (HKT) trait for `Choice<T>`.
///
/// This implementation allows `Choice<T>` to be used in contexts that require
/// higher-kinded types, enabling more generic and flexible code.
///
/// # Type Parameters
///
/// * `T`: The type parameter of the `Choice`.
///
/// # Associated Types
///
/// * `Source`: The type of values contained in the `Choice`.
/// * `Output<U>`: The type resulting from applying `Choice` to another type `U`.
impl<T> HKT for Choice<T> {
    type Source = T;
    type Output<U> = Choice<U>;
    type Source2 = ();
    type BinaryOutput<U, V> = ();
}

impl<T> Identity for Choice<T> {
    /// Returns a reference to the primary value of the `Choice`.
    ///
    /// This implementation satisfies the `Identity` trait by providing
    /// access to the main value stored in the `Choice` structure.
    ///
    /// # Returns
    ///
    /// A reference to the primary value of type `T`.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::datatypes::choice::Choice;
    /// use rustica::traits::identity::Identity;
    ///
    /// let choice = Choice::new(42, vec![1, 2, 3]);
    /// assert_eq!(*choice.value(), 42);
    /// ```
    fn value(&self) -> &Self::Source {
        &self.first
    }

    fn pure_identity<A>(value: A) -> Self::Output<A>
        where
            Self::Output<A>: Identity,
            A: Clone {
        Choice::new(value, Vec::new())
    }
}

impl<T> Functor for Choice<T> {
    /// Maps a function over the `Choice`, transforming both the primary value and alternatives.
    ///
    /// This method applies the given function `f` to the primary value and all alternatives,
    /// creating a new `Choice` with the transformed values.
    ///
    /// # Arguments
    ///
    /// * `f` - A function that takes a reference to `Self::Source` and returns a value of type `B`
    ///
    /// # Returns
    ///
    /// A new `Choice<B>` containing the transformed values
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::datatypes::choice::Choice;
    /// use rustica::traits::functor::Functor;
    ///
    /// let choice = Choice::new(2, vec![3, 4]);
    /// let doubled = choice.fmap(|x| x * 2);
    ///
    /// assert_eq!(*doubled.first(), 4);
    /// assert_eq!(doubled.alternatives(), &vec![6, 8]);
    /// ```
    fn fmap<B, F>(&self, f: F) -> Self::Output<B>
        where
            F: Fn(&Self::Source) -> B {
        Choice::new(f(&self.first), self.alternatives.iter().map(f).collect())
    }
}

impl<T> Pure for Choice<T> {
    /// Creates a new `Choice` with a single value and no alternatives.
    ///
    /// This method implements the `pure` operation for the `Pure` trait,
    /// lifting a value into the `Choice` context.
    ///
    /// # Arguments
    ///
    /// * `value` - The value to be wrapped in a `Choice`.
    ///
    /// # Returns
    ///
    /// A new `Choice<U>` containing the given value as its primary value
    /// and an empty vector of alternatives.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::datatypes::choice::Choice;
    /// use rustica::traits::pure::Pure;
    ///
    /// let choice: Choice<i32> = Choice::<i32>::pure(42);
    /// assert_eq!(*choice.first(), 42);
    /// assert!(choice.alternatives().is_empty());
    /// ```
    fn pure<U>(value: U) -> Self::Output<U> {
        Choice::new(value, vec![])
    }
}

impl<T> Applicative for Choice<T> {
    /// Applies a `Choice` of functions to this `Choice`, producing a new `Choice` of results.
    ///
    /// This method implements the `apply` operation for the `Applicative` trait. It applies each function
    /// in the input `Choice` to each value in this `Choice`, combining the results into a new `Choice`.
    ///
    /// # Arguments
    ///
    /// * `f` - A `Choice` containing functions that map from `Self::Source` to `B`
    ///
    /// # Returns
    ///
    /// A new `Choice<B>` containing the results of applying the functions to the values
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::datatypes::choice::Choice;
    /// use rustica::traits::applicative::Applicative;
    ///
    /// let values = Choice::new(2, vec![3, 4]);
    /// let add_one = Box::new(|x: &i32| x + 1);
    /// let double = Box::new(|x: &i32| x * 2);
    /// let functions = Choice::new(add_one as Box<dyn Fn(&i32) -> i32>, vec![double]);
    /// let result = values.apply(&functions);
    ///
    /// assert_eq!(*result.first(), 3);
    /// assert_eq!(result.alternatives(), &vec![4, 5, 4, 6, 8]);
    /// ```
    fn apply<B, F>(&self, f: &Self::Output<F>) -> Self::Output<B>
    where
        F: Fn(&Self::Source) -> B
    {
        let first_result = (f.first)(&self.first);
        let mut alt_result = Vec::new();

        alt_result.extend(self.alternatives.iter().map(|x| (f.first)(x)));
        alt_result.extend(f.alternatives.iter().map(|g| g(&self.first)));
        
        for g in &f.alternatives {
            alt_result.extend(self.alternatives.iter().map(|x| g(x)));
        }

        Choice::new(first_result, alt_result)
    }

    /// Applies a binary function to the values of two `Choice`s.
    ///
    /// This method combines two `Choice`s by applying a function to their values,
    /// producing a new `Choice` with the results.
    ///
    /// # Arguments
    ///
    /// * `b` - Another `Choice` containing values of type `B`
    /// * `f` - A function that takes references to `Self::Source` and `B`, returning `C`
    ///
    /// # Returns
    ///
    /// A new `Choice<C>` containing the results of applying `f` to all combinations
    /// of values from `self` and `b`.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::datatypes::choice::Choice;
    /// use rustica::traits::applicative::Applicative;
    ///
    /// let a = Choice::new(2, vec![3]);
    /// let b = Choice::new(10, vec![20]);
    /// let result = a.lift2(&b, |x, y| x + y);
    ///
    /// assert_eq!(*result.first(), 12);
    /// assert_eq!(result.alternatives(), &vec![22, 13, 23]);
    /// ```
    fn lift2<B, C, F>(
        &self,
        b: &Self::Output<B>,
        f: F,
    ) -> Self::Output<C> 
    where
        F: Fn(&Self::Source, &B) -> C,
    {
        let first_result = f(&self.first, &b.first);
        let mut alt_result = Vec::new();

        alt_result.extend(b.alternatives.iter().map(|y| f(&self.first, y)));
        alt_result.extend(self.alternatives.iter().map(|x| f(x, &b.first)));

        for x in &self.alternatives {
            alt_result.extend(b.alternatives.iter().map(|y| f(x, y)));
        }

        Choice::new(first_result, alt_result)
    }

    /// Applies a ternary function to the values of three `Choice`s.
    ///
    /// This method combines three `Choice`s by applying a function to their values,
    /// producing a new `Choice` with the results.
    ///
    /// # Arguments
    ///
    /// * `b` - Second `Choice` containing values of type `B`
    /// * `c` - Third `Choice` containing values of type `C`
    /// * `f` - A function that takes references to `Self::Source`, `B`, and `C`, returning `D`
    ///
    /// # Returns
    ///
    /// A new `Choice<D>` containing the results of applying `f` to all combinations
    /// of values from `self`, `b`, and `c`.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::datatypes::choice::Choice;
    /// use rustica::traits::applicative::Applicative;
    ///
    /// let a = Choice::new(1, vec![2]);
    /// let b = Choice::new(10, vec![20]);
    /// let c = Choice::new(100, vec![200]);
    /// let result = a.lift3(&b, &c, |x, y, z| x + y + z);
    ///
    /// assert_eq!(*result.first(), 111);
    /// assert_eq!(result.alternatives(), &vec![211, 121, 221, 112, 212, 122, 222]);
    /// ```
    fn lift3<B, C, D, F>(
        &self,
        b: &Self::Output<B>,
        c: &Self::Output<C>,
        f: F,
    ) -> Self::Output<D> 
    where
        F: Fn(&Self::Source, &B, &C) -> D,
    {
        let first_result = f(&self.first, &b.first, &c.first);
        let mut alt_result = Vec::new();

        alt_result.extend(c.alternatives.iter().map(|z| f(&self.first, &b.first, z)));
        alt_result.extend(b.alternatives.iter().map(|y| f(&self.first, y, &c.first)));
        for y in &b.alternatives {
            alt_result.extend(c.alternatives.iter().map(|z| f(&self.first, y, z)));
        }
        for x in &self.alternatives {
            alt_result.push(f(x, &b.first, &c.first));
            alt_result.extend(c.alternatives.iter().map(|z| f(x, &b.first, z)));
            alt_result.extend(b.alternatives.iter().map(|y| f(x, y, &c.first)));
            for y in &b.alternatives {
                alt_result.extend(c.alternatives.iter().map(|z| f(x, y, z)));
            }
        }

        Choice::new(first_result, alt_result)
    }
}

impl<T: Clone> Monad for Choice<T> {
    /// Applies a function to each value in the `Choice`, flattening the results.
    ///
    /// This method implements the `bind` operation for the `Monad` trait. It applies the given
    /// function to the primary value and all alternatives, then combines the results into a new `Choice`.
    ///
    /// # Arguments
    ///
    /// * `f` - A function that takes a reference to `Self::Source` and returns a `Choice<U>`
    ///
    /// # Returns
    ///
    /// A new `Choice<U>` containing the flattened results of applying `f` to all values
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::datatypes::choice::Choice;
    /// use rustica::traits::monad::Monad;
    ///
    /// let choice = Choice::new(2, vec![3, 4]);
    /// let result = choice.bind(|&x| Choice::new(x * 10, vec![x * 100]));
    ///
    /// assert_eq!(*result.first(), 20);
    /// assert_eq!(result.alternatives(), &vec![200, 30, 300, 40, 400]);
    /// ```
    fn bind<U, F>(&self, f: F) -> Self::Output<U>
    where
        F: Fn(&Self::Source) -> Self::Output<U>,
    {
        let first_choice = f(&self.first);
        let mut alt_values = Vec::new();
        
        // Move alternatives instead of borrowing to avoid cloning
        alt_values.extend(first_choice.alternatives);
    
        for x in &self.alternatives {
            let choice = f(x);
            alt_values.push(choice.first);
            alt_values.extend(choice.alternatives);
        }
        
        Choice::new(first_choice.first, alt_values)
    }
    
    /// Flattens a nested `Choice` structure.
    ///
    /// This method implements the `join` operation for the `Monad` trait. It takes a `Choice`
    /// of `Choice`s and flattens it into a single `Choice`, combining all alternatives.
    ///
    /// # Type Parameters
    ///
    /// * `U`: The type of the inner `Choice`'s values.
    ///
    /// # Returns
    ///
    /// A flattened `Choice<U>`.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::datatypes::choice::Choice;
    /// use rustica::traits::monad::Monad;
    ///
    /// let nested = Choice::new(
    ///     Choice::new(1, vec![2, 3]),
    ///     vec![Choice::new(4, vec![5]), Choice::new(6, vec![7, 8])]
    /// );
    /// let flattened = nested.join();
    ///
    /// assert_eq!(*flattened.first(), 1);
    /// assert_eq!(flattened.alternatives(), &vec![2, 3, 4, 5, 6, 7, 8]);
    /// ```
    fn join<U>(&self) -> Self::Output<U>
    where
        T: Clone + Into<Self::Output<U>>,
    {
        let first_choice: Self::Output<U> = self.first.clone().into();
        let mut alt: Vec<U> = first_choice.alternatives;
        
        for x in &self.alternatives {
            let choice: Self::Output<U> = x.clone().into();
            alt.push(choice.first);
            alt.extend(choice.alternatives);
        }
        
        Choice::new(first_choice.first, alt)
    }
}

impl<T: Clone> Semigroup for Choice<T> {
    /// Combines two `Choice` instances, merging their alternatives.
    ///
    /// This method implements the `combine` operation for the `Semigroup` trait.
    /// It creates a new `Choice` with the first value of `self` and combines
    /// the alternatives from both `self` and `other`.
    ///
    /// # Arguments
    ///
    /// * `other` - Another `Choice` instance to combine with `self`
    ///
    /// # Returns
    ///
    /// A new `Choice` instance with combined alternatives
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::datatypes::choice::Choice;
    /// use rustica::traits::semigroup::Semigroup;
    ///
    /// let a = Choice::new(1, vec![2, 3]);
    /// let b = Choice::new(4, vec![5, 6]);
    /// let combined = a.combine(&b);
    ///
    /// assert_eq!(*combined.first(), 1);
    /// assert_eq!(combined.alternatives(), &vec![2, 3, 4, 5, 6]);
    /// ```
    fn combine(&self, other: &Self) -> Self {
        let mut combined_alternatives = self.alternatives.clone();
        combined_alternatives.push(other.first.clone());
        combined_alternatives.extend(other.alternatives.clone());
        Choice::new(self.first.clone(), combined_alternatives)
    }
}

impl<T: Clone + Default> Monoid for Choice<T> {
    /// Creates an empty `Choice` with the default value of type `T`.
    ///
    /// This method implements the `empty` operation for the `Monoid` trait,
    /// providing an identity element for the `Choice` type.
    ///
    /// # Returns
    ///
    /// A new `Choice<T>` with the default value as its primary value and no alternatives.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::datatypes::choice::Choice;
    /// use rustica::traits::monoid::Monoid;
    ///
    /// let empty_choice: Choice<i32> = Choice::empty();
    /// assert_eq!(*empty_choice.first(), 0);
    /// assert!(empty_choice.alternatives().is_empty());
    /// ```
    fn empty() -> Self {
        Choice::new(T::default(), vec![])
    }
}

impl<T> IntoIterator for Choice<T> {
    type Item = T;
    type IntoIter = std::iter::Chain<std::iter::Once<T>, std::vec::IntoIter<T>>;

    fn into_iter(self) -> Self::IntoIter {
        std::iter::once(self.first).chain(self.alternatives.into_iter())
    }
}

impl<T: Debug> Debug for Choice<T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        write!(f, "Choice({:?}, {:?})", self.first, self.alternatives)
    }
}

impl<T: Display> Display for Choice<T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        write!(f, "{}", self.first)?;
        if !self.alternatives.is_empty() {
            write!(f, " | {}", self.alternatives.iter().map(|alt| alt.to_string()).collect::<Vec<_>>().join(", "))?;
        }
        Ok(())
    }
}