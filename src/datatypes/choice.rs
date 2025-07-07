//! # Choice (`Choice<T>`)
//!
//! The `Choice<T>` datatype represents a primary value along with a list of alternative values,
//! all of type `T`. It's designed for scenarios where you need to manage a preferred option
//! while keeping other possibilities available. `Choice` is particularly useful in contexts like
//! configuration management, user preference handling, or any situation involving fallback mechanisms.
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
//! - **Immutability and Copy-on-Write**: `Choice` instances are immutable. Operations that modify
//!   a `Choice` (e.g., adding alternatives, filtering) return a new `Choice` instance.
//!   Internally, `Choice` uses `Arc<SmallVec<[T; 8]>>` to store values, enabling efficient
//!   cloning (cheap reference count increment) and copy-on-write semantics when modifications are needed.
//!   This means cloning a `Choice` is very fast, and modifications only incur the cost of copying the
//!   underlying data if the `Arc` is shared (i.e., has more than one reference).
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
//! let filtered = choice.filter_values(|&x| x > 25);
//! assert_eq!(filtered.first(), Some(&30)); // First value that passes the predicate
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
//!         Choice::new(format!("verified_{}", name), vec![])
//!     });
//!
//! assert_eq!(*processed.first().unwrap(), "verified_user123");
//! ```
//!
//! ## Performance Characteristics
//!
//! - **Memory Usage:**
//!   - Uses `Arc<SmallVec<[T; 8]>>` for efficient memory management
//!   - Small instances (up to 8 elements) avoid heap allocation via `SmallVec` optimization
//!   - Cloning a `Choice<T>` is O(1) due to `Arc` reference counting
//!   - Copy-on-write semantics avoid unnecessary copies when modifications occur
//!
//! - **Time Complexity:**
//!   - Construction: O(n) where n is the number of alternatives
//!   - Cloning: O(1) via `Arc`
//!   - Access operations (`first()`, `alternatives()`): O(1)
//!   - Modification operations (`add_alternatives`, `filter_values`): O(n) in the worst case due to potential cloning
//!   - `fmap`, `bind`: O(n) where n is the number of elements
//!   - Iteration: O(n) linear time, similar to `Vec`
//!
//! - **Concurrency:**
//!   - Thread-safe due to immutable semantics and `Arc` for shared ownership
//!   - No interior mutability or synchronization overhead
//!   - Safe to share across thread boundaries when `T: Send + Sync`
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
//! `Choice` adheres to standard functional programming laws.
//!
//! ### Functor Laws
//!
//! 1.  **Identity**: `choice.fmap(|x| x) == choice`
//! 2.  **Composition**: `choice.fmap(f).fmap(g) == choice.fmap(|x| g(f(x)))`
//!
//! ```rust
//! use rustica::prelude::*;
//! use rustica::datatypes::choice::Choice;
//!
//! // Identity law
//! let choice = Choice::new(1, vec![2, 3]);
//! let mapped_identity = choice.clone().fmap(|x: &i32| *x);
//! assert_eq!(choice, mapped_identity);
//!
//! // Composition law
//! let f = |x: &i32| *x + 10;
//! let g = |x: &i32| *x * 2;
//!
//! let composition1 = choice.clone().fmap(f).fmap(g);
//! let composition2 = choice.clone().fmap(|x| g(&f(x)));
//! assert_eq!(composition1, composition2);
//! ```
//!
//! ### Applicative Laws
//!
//! 1.  **Identity**: `Choice::pure(|x| x).apply(&choice) == choice`
//! 2.  **Homomorphism**: `Choice::pure(f).apply(&Choice::pure(x)) == Choice::pure(f(x))`
//! 3.  **Interchange**: `func_choice.apply(&Choice::pure(y)) == Choice::pure(|f_inner| f_inner(y)).apply(&func_choice)`
//!     (Note: `apply` takes a reference to the argument for ergonomic borrowing)
//! 4.  **Composition**: `Choice::pure(|g_val| |f_val| g_val(f_val)).apply(&u).apply(&v).apply(&w) == u.apply(&v.apply(&w))`
//!     (This is a bit complex to show directly due to currying and types, simplified version often shown)
//!
//! ```rust
//! use rustica::prelude::*;
//! use rustica::datatypes::choice::Choice;
//!
//! // Identity law
//! let choice = Choice::new(5, vec![10, 15]);
//! let id_fn = |x: &i32| *x;
//! let id_fn_choice = Choice::new(id_fn, vec![]);
//! let applied = choice.clone().apply(&id_fn_choice);
//! assert_eq!(choice, applied);
//!
//! // Homomorphism law
//! let f = |x: &i32| *x * 2;
//! let x = 7;
//! let pure_f = Choice::new(f, vec![]);
//! let pure_x = Choice::new(x, vec![]);
//! let lhs = pure_x.apply(&pure_f);
//! let result = f(&x);
//! let rhs = Choice::new(result, vec![]);
//! assert_eq!(lhs, rhs);
//!
//! // Interchange law
//! let y = 3;
//! // Using a type alias so both closures have the same type
//! type IntFn = fn(&i32) -> i32;
//! let f1: IntFn = |x: &i32| *x + 1;
//! let f2: IntFn = |x: &i32| *x + 2;
//! let func_choice = Choice::new(f1, vec![f2]);
//! let pure_y = Choice::new(y, vec![]);
//! let lhs = pure_y.apply(&func_choice);
//! let apply_y = |f: &IntFn| f(&y);
//! let apply_y_choice = Choice::new(apply_y, vec![]);
//! let rhs = func_choice.fmap(|f| apply_y(f));
//! assert_eq!(lhs, rhs);
//! ```
//!
//! ### Monad Laws
//!
//! 1.  **Left Identity**: `Choice::pure(a).bind(f) == f(a)`
//! 2.  **Right Identity**: `m.bind(Choice::pure) == m`
//! 3.  **Associativity**: `m.bind(f).bind(g) == m.bind(|x| f(x).bind(g))`
//!
//! ```rust
//! use rustica::prelude::*;
//! use rustica::datatypes::choice::Choice;
//!
//! // Left Identity law
//! let a = 5;
//! let f = |x: &i32| Choice::new(*x * 2, vec![*x * 3]);
//!
//! let left = Choice::<i32>::pure(&a).bind(f);
//! let right = f(&a);
//! assert_eq!(left, right);
//!
//! // Right Identity law
//! let m = Choice::new(10, vec![20, 30]);
//! let bound = m.clone().bind(Choice::<i32>::pure);
//! assert_eq!(m, bound);
//!
//! // Associativity law
//! let m = Choice::new(5, vec![10]);
//! let f = |x: &i32| Choice::new(*x + 1, vec![*x + 2]);
//! let g = |x: &i32| Choice::new(*x * 2, vec![*x * 3]);
//!
//! let left = m.clone().bind(f).bind(g);
//! let right = m.bind(|x| f(x).bind(g));
//! assert_eq!(left, right);
//! ```
//! The `Choice` type provides several advanced operations such as:
//! - Filtering alternatives based on predicates
//! - Flattening nested choices
//! - Converting between collections and choices
//! - Monadic operations for sequencing computations
//!
//! ## TODO
//!
//! - Optimize performance for large collections of alternatives
//! - Add property-based tests for typeclass laws

#[cfg(feature = "develop")]
use quickcheck::{Arbitrary, Gen};
use std::fmt::{Debug, Display, Formatter};
use std::hash::Hash;
use std::iter::FromIterator;
use std::sync::Arc;

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

    /// Creates a new `Choice` with a primary value and alternatives.
    ///
    /// # Performance
    /// - Time complexity: O(n) where n is the number of alternatives, due to extending the internal SmallVec.
    /// - Space complexity: O(n) for storing alternatives.
    /// - Memory efficiency: Uses `Arc<SmallVec<[T; 8]>>` for shared ownership. The initial allocation is for `size_hint().0 + 1`.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::datatypes::choice::Choice;
    ///
    /// // Create with a primary value and alternatives
    /// let choice = Choice::new(1, vec![2, 3, 4]);
    /// assert_eq!(*choice.first().unwrap(), 1);
    /// assert_eq!(choice.alternatives(), &[2, 3, 4]);
    /// assert_eq!(choice.len(), 4);
    ///
    /// // Create with empty alternatives
    /// let single: Choice<&str> = Choice::new("primary", Vec::<&str>::new());
    /// assert_eq!(*single.first().unwrap(), "primary");
    /// assert!(single.alternatives().is_empty());
    ///
    /// // Create with a different type
    /// let string_choice = Choice::new("hello".to_string(), vec!["world".to_string()]);
    /// assert_eq!(*string_choice.first().unwrap(), "hello");
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
    /// # Performance
    /// - Time complexity: O(1) as it's a direct access to the first element of the internal collection.
    /// - Space complexity: O(1).
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
        self.values.as_ref().first()
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
    /// # Performance
    /// - Time complexity: O(1) as it involves slicing an existing collection.
    /// - Space complexity: O(1) as it returns a reference.
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
    /// let choice_no_alts = Choice::new(1000, Vec::<i32>::new());
    /// assert_eq!(choice_no_alts.alternatives(), &[]);
    ///
    /// let empty_choice: Choice<i32> = Choice::new_empty();
    /// assert_eq!(empty_choice.alternatives(), &[]);
    /// ```
    ///
    /// # See Also
    /// - [`first`](Self::first) - To get the primary value.
    /// - [`has_alternatives`](Self::has_alternatives) - To check if any alternatives exist.
    /// - [`iter_alternatives`](Self::iter_alternatives) - For an iterator over alternatives.
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
    ///
    /// This is true if the total number of items in the `Choice` is greater than one.
    ///
    /// # Returns
    ///
    /// - `true` if there is at least one alternative value.
    /// - `false` if the `Choice` only contains a primary value or is empty.
    ///
    /// # Performance
    /// - Time complexity: O(1) as it's a check on the length of the internal collection.
    /// - Space complexity: O(1).
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::datatypes::choice::Choice;
    ///
    /// let choice_with_alts = Choice::new(1, vec![2, 3]);
    /// assert!(choice_with_alts.has_alternatives());
    ///
    /// let choice_no_alts = Choice::new(1, Vec::<i32>::new());
    /// assert!(!choice_no_alts.has_alternatives());
    ///
    /// let empty_choice: Choice<i32> = Choice::new_empty();
    /// assert!(!empty_choice.has_alternatives());
    /// ```
    ///
    /// # See Also
    /// - [`alternatives`](Self::alternatives) - To get the actual alternative values.
    /// - [`len`](Self::len) - To get the total count of items.
    #[inline]
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
    /// # Performance
    /// - Time complexity: O(1) as it returns the stored length of the internal collection.
    /// - Space complexity: O(1).
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
    /// # Performance
    /// - Time complexity: O(1) as it checks the length of the internal collection.
    /// - Space complexity: O(1).
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

    /// Adds multiple new alternatives to the `Choice`, consuming the original.
    ///
    /// This method creates a new `Choice` instance. If the `Arc` holding the values
    /// has other references, the underlying `SmallVec` is cloned (copy-on-write).
    /// Otherwise, the existing `SmallVec` is mutated in place.
    ///
    /// # Performance
    /// - Time complexity: O(n + m) where n is the current number of values in the `Choice`
    ///   and m is the number of alternatives being added. This is due to potentially cloning
    ///   the existing `SmallVec` and then extending it.
    /// - Space complexity: O(n + m) for the new `Choice` if a clone occurs, or O(m) additional
    ///   space if mutation happens in place (amortized for `SmallVec` extension).
    /// - Memory efficiency: Uses `Arc` for shared ownership. Cloning is copy-on-write.
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
    /// let expanded = choice.add_alternatives(vec![4, 5, 6]);
    ///
    /// assert_eq!(*expanded.first().unwrap(), 1);
    /// assert_eq!(expanded.alternatives(), &[2, 3, 4, 5, 6]);
    /// assert_eq!(expanded.len(), 6);
    ///
    /// // Demonstrate chaining
    /// // Note: Each call to add_alternatives might clone if the Arc is shared.
    /// // For optimal performance when adding many items in sequence to an unshared Choice,
    /// // consider collecting items first and adding them in one go.
    /// let further_expanded = expanded.add_alternatives([7, 8]);
    /// assert_eq!(*further_expanded.first().unwrap(), 1);
    /// assert_eq!(further_expanded.alternatives(), &[2, 3, 4, 5, 6, 7, 8]);
    /// assert_eq!(further_expanded.len(), 8);
    ///
    /// // Adding to an empty choice
    /// let empty_choice: Choice<i32> = Choice::new_empty();
    /// // Since new_empty() creates a Choice with no primary, add_alternatives will add to an empty list.
    /// // This behavior might be surprising; typically, Choice should have a primary value.
    /// // If the intent is to create a Choice from a list where the first item is primary:
    /// // let from_list = Choice::from_iter(vec![10,20]); or Choice::new(10, vec![20]);
    /// let from_empty_add = empty_choice.add_alternatives(vec![10, 20]);
    /// assert_eq!(from_empty_add.len(), 2);
    /// assert_eq!(*from_empty_add.first().unwrap(), 10); // The first item added becomes primary
    /// assert_eq!(from_empty_add.alternatives(), &[20]);
    /// ```
    #[inline]
    pub fn add_alternatives<I>(self, items: I) -> Self
    where
        T: Clone,
        I: IntoIterator<Item = T>,
    {
        let values = match Arc::try_unwrap(self.values) {
            Ok(mut values) => {
                values.extend(items);
                Arc::new(values)
            },
            Err(arc) => {
                let mut new_values = Arc::clone(&arc);
                Arc::make_mut(&mut new_values).extend(items);
                new_values
            },
        };
        Self { values }
    }

    /// Removes an alternative at the specified index and returns a new `Choice`.
    ///
    /// The `index` is 0-based and relative to the list of alternatives (excluding the primary value).
    /// This method creates a new `Choice` instance. If the `Arc` holding the values
    /// has other references, the underlying `SmallVec` is cloned (copy-on-write).
    /// Otherwise, the existing `SmallVec` is mutated in place.
    ///
    /// # Arguments
    ///
    /// * `index` - The 0-based index of the alternative to remove.
    ///
    /// # Returns
    ///
    /// A new `Choice<T>` with the alternative at the specified index removed.
    ///
    /// # Performance
    /// - Time complexity: O(N) where N is the number of values in the `Choice`. This is due to
    ///   `SmallVec::remove` which is O(N), and potentially cloning the `SmallVec` (also O(N)).
    /// - Space complexity: O(N) for the new `Choice` if a clone occurs.
    /// - Memory efficiency: Uses `Arc` for shared ownership. Cloning is copy-on-write.
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

        let values = match Arc::try_unwrap(self.values) {
            Ok(mut values) => {
                values.remove(index + 1); // +1 because alternatives start at index 1
                Arc::new(values)
            },
            Err(arc) => {
                let mut new_values = Arc::clone(&arc);
                Arc::make_mut(&mut new_values).remove(index + 1);
                new_values
            },
        };

        Self { values }
    }

    /// Filters the alternatives of the `Choice` based on a predicate, returning a new `Choice`.
    ///
    /// This method applies the `predicate` to each alternative value. The primary value
    /// of the `Choice` remains unchanged and is always included in the new `Choice`,
    /// regardless of whether it satisfies the predicate. Only alternatives are filtered.
    ///
    /// If the original `Choice` is empty, an empty `Choice` is returned.
    /// If the original `Choice` has a primary value but no alternatives, the new `Choice`
    /// will be identical (containing only the primary value).
    ///
    /// This method uses reference counting optimization: if the current `Choice` has
    /// exclusive ownership of its data (`Arc` reference count is 1), it reuses the
    /// existing allocation. Otherwise, it creates a new allocation.
    ///
    /// # Arguments
    ///
    /// * `predicate` - A closure `F: Fn(&T) -> bool` that takes a reference to an
    ///   alternative value and returns `true` if the alternative should be kept,
    ///   or `false` if it should be discarded.
    ///
    /// # Returns
    ///
    /// A new `Choice<T>` instance containing the original primary value and only
    /// the alternatives that satisfied the `predicate`.
    ///
    /// # Performance
    /// - Time complexity: O(N) where N is the number of alternatives. The predicate is called
    ///   for each alternative.
    /// - Space complexity: O(M) for the new `Choice` where M is the number of items kept.
    /// - Memory efficiency: Reuses existing allocation when possible (when Arc reference count is 1),
    ///   otherwise allocates new memory.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::datatypes::choice::Choice;
    ///
    /// let choice = Choice::new(1, vec![2, 3, 4, 5, 6]);
    ///
    /// // Filter alternatives for even numbers
    /// let even_alternatives = choice.filter(|&x| x % 2 == 0);
    ///
    /// // Primary value (1) is always kept, even though it's odd
    /// assert_eq!(*even_alternatives.first().unwrap(), 1);
    /// // Only even alternatives are kept
    /// assert_eq!(even_alternatives.alternatives(), &[2, 4, 6]);
    ///
    /// // Primary value is kept even when it doesn't satisfy the predicate
    /// let choice2 = Choice::new(7, vec![8, 9, 10]);
    /// let filtered = choice2.filter(|&x| x % 2 == 0);
    /// assert_eq!(*filtered.first().unwrap(), 7); // 7 is kept despite being odd
    /// assert_eq!(filtered.alternatives(), &[8, 10]);
    ///
    /// // When there are no alternatives, the primary is still kept
    /// let single = Choice::new(10, Vec::<i32>::new());
    /// let filtered_single = single.filter(|&x| x > 100);
    /// assert_eq!(*filtered_single.first().unwrap(), 10);
    /// assert!(filtered_single.alternatives().is_empty());
    ///
    /// // Empty Choice remains empty
    /// let empty: Choice<i32> = Choice::new_empty();
    /// let filtered_empty = empty.filter(|&x| x > 0);
    /// assert!(filtered_empty.is_empty());
    /// ```
    ///
    /// # See Also
    /// - [`filter_values`](Self::filter_values) - Filters all values (primary and alternatives),
    ///   potentially changing the primary value.
    /// - [`remove_alternative`](Self::remove_alternative) - To remove a single alternative by index.
    ///
    #[inline]
    pub fn filter<P>(&self, predicate: P) -> Self
    where
        P: Fn(&T) -> bool,
        T: Clone,
    {
        if self.is_empty() {
            return Self::new_empty();
        }

        match Arc::try_unwrap(self.values.clone()) {
            Ok(mut values) => {
                // We have exclusive ownership, reuse the allocation
                values.truncate(1); // Keep only primary
                values.extend(self.values.iter().skip(1).filter(|v| predicate(v)).cloned());

                Self {
                    values: Arc::new(values),
                }
            },
            Err(_) => {
                // Shared ownership, create new allocation
                let mut filtered = SmallVec::<[T; 8]>::with_capacity(self.values.len());
                filtered.push(self.values[0].clone());
                filtered.extend(self.values.iter().skip(1).filter(|v| predicate(v)).cloned());

                Self {
                    values: Arc::new(filtered),
                }
            },
        }
    }

    /// Applies a function to each alternative value in the `Choice`, returning a new `Choice<T>`.
    ///
    /// This method transforms each alternative value using the provided function `f`.
    /// The primary value of the `Choice` remains unchanged (it is cloned) and is the primary
    /// value of the new `Choice`. The function `f` is not applied to the primary value.
    ///
    /// If the original `Choice` is empty, an empty `Choice<T>` is returned.
    /// If the original `Choice` has a primary value but no alternatives, the new `Choice`
    /// will be identical to the original (containing the cloned primary value and no alternatives).
    ///
    /// This method uses copy-on-write semantics for the underlying `Arc<SmallVec>`.
    ///
    /// # Arguments
    ///
    /// * `f` - A closure `F: FnMut(&T) -> T` that takes a reference to an
    ///   alternative value of type `T` and returns a new value of type `T`.
    ///
    /// # Returns
    ///
    /// A new `Choice<T>` instance containing the original primary value (cloned)
    /// and the transformed alternatives.
    ///
    /// # Performance
    /// - Time complexity: O(N) where N is the number of alternatives. The function `f` is called
    ///   for each alternative. Cloning the primary value and constructing the new `SmallVec`
    ///   also contribute.
    /// - Space complexity: O(M) for the new `Choice<T>`, where M is the total number of items.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::datatypes::choice::Choice;
    ///
    /// let choice_i32 = Choice::new(10, vec![20, 3, 45, 60, 7]);
    ///
    /// // Double only the alternatives
    /// let choice_doubled_alts = choice_i32.fmap_alternatives(|&alt| alt * 2);
    /// assert_eq!(*choice_doubled_alts.first().unwrap(), 10); // Primary is kept (cloned)
    /// assert_eq!(choice_doubled_alts.alternatives(), &[40, 6, 90, 120, 14]);
    ///
    /// // On a choice with no alternatives
    /// let primary_only_choice: Choice<i32> = Choice::new(100, Vec::<i32>::new());
    /// let mapped_primary_only = primary_only_choice.fmap_alternatives(|&alt| alt * 2);
    /// assert_eq!(*mapped_primary_only.first().unwrap(), 100); // Primary cloned
    /// assert!(mapped_primary_only.alternatives().is_empty());
    ///
    /// // On an empty choice
    /// let empty_choice: Choice<i32> = Choice::new_empty();
    /// let mapped_empty = empty_choice.fmap_alternatives(|&alt| alt * 2);
    /// assert!(mapped_empty.is_empty());
    /// ```
    ///
    /// # See Also
    /// - [`fmap`](crate::traits::functor::Functor::fmap) - To apply a function to all values (primary and alternatives), potentially changing type.
    /// - [`filter`](Self::filter) - To filter alternatives based on a predicate.
    #[inline]
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
            values: Arc::new(final_values),
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
    /// # Performance
    /// - Time complexity: O(N * M) where N is the total number of inner collections (primary + alternatives)
    ///   and M is the average number of items in each inner collection. This is because each item
    ///   is iterated over and potentially cloned.
    /// - Space complexity: O(TotalItems) for storing all the flattened items in the new `Choice`.
    /// - Memory efficiency: A new `Arc<SmallVec<[I; 8]>>` is allocated for the resulting `Choice`.
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
    /// use rustica::traits::functor::Functor; // For fmap in the string example
    ///
    /// // Basic flattening with Vec<i32>
    /// let nested_numbers: Choice<Vec<i32>> = Choice::new(vec![1, 2], vec![vec![3, 4], vec![5]]);
    /// let flattened_numbers: Choice<i32> = nested_numbers.flatten();
    /// assert_eq!(*flattened_numbers.first().unwrap(), 1);
    /// // Order of alternatives: items from alternatives ([3, 4], then [5]), then rest of primary ([2])
    /// assert_eq!(flattened_numbers.alternatives(), &[3, 4, 5, 2]);
    ///
    /// // Flattening with strings, demonstrating fmap to prepare for flatten
    /// let words: Choice<&str> = Choice::new("hello", vec!["world", "rust"]);
    /// // First, map &str to an iterable collection of chars, like Vec<char>
    /// let choice_of_vec_char: Choice<Vec<char>> = words.fmap(|s: &&str| s.chars().collect::<Vec<_>>());
    /// let flattened_chars: Choice<char> = choice_of_vec_char.flatten();
    /// assert_eq!(*flattened_chars.first().unwrap(), 'h');
    /// // Order: chars from alternatives ("world", then "rust"), then rest of primary ("hello")
    /// assert_eq!(flattened_chars.alternatives(), &['w', 'o', 'r', 'l', 'd', 'r', 'u', 's', 't', 'e', 'l', 'l', 'o']);
    ///
    /// // Flattening a Choice where alternatives are empty Vecs
    /// let single_nested_list: Choice<Vec<i32>> = Choice::new(vec![10, 20, 30], vec![Vec::<i32>::new(), vec![40]]);
    /// let flat_from_single_list: Choice<i32> = single_nested_list.flatten();
    /// assert_eq!(*flat_from_single_list.first().unwrap(), 10);
    /// // Order: items from alternatives (empty, then [40]), then rest of primary ([20, 30])
    /// assert_eq!(flat_from_single_list.alternatives(), &[40, 20, 30]);
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
    ///
    /// * [`flatten_sorted`](Self::flatten_sorted) - Similar, but sorts the resulting alternatives.
    /// * [`join`](crate::traits::monad::Monad::join) - The Monad trait's equivalent operation for `Choice<Choice<T>>`.
    /// * [`bind`](crate::traits::monad::Monad::bind) - For more general monadic sequencing which can achieve flattening.
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
                // Collect all remaining items from primary and all alternatives
                let alternatives = self
                    .values
                    .iter()
                    .skip(1) // Skip the primary value
                    .flat_map(|val| val.clone().into_iter())
                    .chain(primary_iter) // Add remaining items from primary
                    .collect::<SmallVec<[I; 8]>>();

                Choice::new(first_item, alternatives)
            },
            None => panic!("Primary value was an empty iterator in Choice::flatten"),
        }
    }

    /// Flattens a `Choice` of iterable items into a sorted `Choice` of individual items.
    ///
    /// Similar to `flatten()`, but sorts the alternatives according to their natural order.
    /// The first item of the primary value becomes the new primary value, and all other items
    /// (including those from alternatives) are sorted and collected into the new alternatives.
    ///
    /// # Type Parameters
    ///
    /// * `T`: The original type, which must be clonable and iterable.
    /// * `I`: The item type of the iterable, which must be clonable and implement `Ord`.
    ///
    /// # Returns
    ///
    /// A new `Choice<I>` with flattened and sorted alternatives.
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
    /// let nested = Choice::new(vec![3, 1], vec![vec![4, 2], vec![5]]);
    /// let flattened = nested.flatten_sorted();
    ///
    /// assert_eq!(*flattened.first().unwrap(), 3);
    /// assert_eq!(flattened.alternatives(), &[1, 2, 4, 5]);
    /// ```
    ///
    /// # Performance
    /// - Time complexity: O(TotalItems + A log A), where `TotalItems` is the total number of
    ///   individual items after flattening, and `A` is the number of these items that become
    ///   alternatives. The `TotalItems` part comes from iterating and cloning all items,
    ///   and `A log A` comes from sorting the alternatives.
    /// - Space complexity: O(TotalItems) for storing all flattened items in the new `Choice`,
    ///   plus temporary space for collecting alternatives before sorting.
    /// - Memory efficiency: A new `Arc<SmallVec<[I; 8]>>` is allocated for the resulting `Choice`.
    ///
    /// # See Also
    /// - [`flatten()`](Self::flatten) - For a version that flattens without sorting alternatives.
    /// - [`Choice::new()`](Self::new) - For creating a `Choice`.
    /// - [`Vec::sort()`](https://doc.rust-lang.org/std/vec/struct.Vec.html#method.sort) - For the sorting mechanism used on alternatives.
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
    /// # Performance
    /// - Time complexity: O(N) where N is the number of items in the `many` iterator.
    ///   This is due to iterating through all items and collecting them into a `SmallVec`.
    /// - Space complexity: O(N) for storing the items in the new `Choice`.
    /// - Memory efficiency: A new `Arc<SmallVec<[T; 8]>>` is allocated for the `Choice`.
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
            Self {
                values: Arc::new(values),
            }
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
    /// This method uses copy-on-write semantics for the underlying `Arc<SmallVec>`.
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
    /// # Performance
    /// - Time complexity: O(N) where N is the total number of values in the `Choice`.
    ///   The predicate is called for each value. Constructing the new `SmallVec` also
    ///   contributes.
    /// - Space complexity: O(N) in the worst case for the new `Choice` if all items are kept.
    /// - Memory efficiency: Uses `Arc` for shared ownership.
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
            _ => Self {
                values: Arc::new(filtered),
            },
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
    /// # Performance
    /// - Time complexity: O(1) to create the iterator. Iterating through all N items is O(N).
    /// - Space complexity: O(1) for the iterator itself.
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
    /// # Performance
    /// - Time complexity: O(1) to create the iterator. Iterating through all M alternatives is O(M).
    /// - Space complexity: O(1) for the iterator itself.
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
    ///
    /// This method consumes the original `Choice` and returns a new `Choice`
    /// with the primary value and the chosen alternative exchanged. The `alt_index`
    /// is 0-based and relative to the list of alternatives (i.e., excluding the primary value).
    ///
    /// This operation involves creating a new `SmallVec` for the values. If the `Arc`
    /// holding the original values has other references (i.e., `Arc::strong_count() > 1`),
    /// the `SmallVec` is cloned. Otherwise, if the `Arc` is uniquely owned, the
    /// `SmallVec` can be mutated in place before constructing the new `Choice`.
    ///
    /// # Arguments
    ///
    /// * `alt_index` - The 0-based index of the alternative to swap with the primary value.
    ///
    /// # Returns
    ///
    /// A new `Choice<T>` where the original primary value and the alternative at `alt_index`
    /// have been swapped.
    ///
    /// # Performance
    /// - Time complexity: O(N) if the underlying `SmallVec` needs to be cloned due to
    ///   shared `Arc` references (where N is the total number of items). If the `SmallVec`
    ///   can be mutated in place (unique `Arc`), the swap itself is O(1), plus the cost
    ///   of cloning the two swapped elements.
    /// - Space complexity: O(N) for the new `Choice` if a clone of the `SmallVec` occurs.
    /// - Memory efficiency: Uses `Arc` for shared ownership, enabling copy-on-write.
    ///
    /// # Panics
    ///
    /// Panics if:
    /// - The `Choice` has no alternatives (i.e., it only contains a primary value or is empty).
    /// - `alt_index` is out of bounds for the list of alternatives.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::datatypes::choice::Choice;
    ///
    /// // Basic swap
    /// let choice1 = Choice::new(10, vec![20, 30, 40]); // primary: 10, alts: [20, 30, 40]
    /// let swapped1 = choice1.swap_with_alternative(1); // Swap 10 with 30 (alt_index 1)
    /// assert_eq!(*swapped1.first().unwrap(), 30);
    /// assert_eq!(swapped1.alternatives(), &[20, 10, 40]);
    ///
    /// // Swap with the first alternative
    /// let choice2 = Choice::new(5, vec![15, 25]); // primary: 5, alts: [15, 25]
    /// let swapped2 = choice2.swap_with_alternative(0); // Swap 5 with 15 (alt_index 0)
    /// assert_eq!(*swapped2.first().unwrap(), 15);
    /// assert_eq!(swapped2.alternatives(), &[5, 25]);
    ///
    /// // Swap with the last alternative
    /// let choice3 = Choice::new(100, vec![200, 300, 400]); // primary: 100, alts: [200, 300, 400]
    /// let swapped3 = choice3.swap_with_alternative(2); // Swap 100 with 400 (alt_index 2)
    /// assert_eq!(*swapped3.first().unwrap(), 400);
    /// assert_eq!(swapped3.alternatives(), &[200, 300, 100]);
    /// ```
    ///
    /// ### Panics - Index out of bounds
    /// ```should_panic
    /// use rustica::datatypes::choice::Choice;
    ///
    /// let choice = Choice::new(1, vec![2, 3]); // alternatives: [2, 3] (len 2)
    /// // Panics because alt_index 2 is out of bounds.
    /// let _ = choice.swap_with_alternative(2);
    /// ```
    ///
    /// ### Panics - No alternatives to swap with
    /// ```should_panic
    /// use rustica::datatypes::choice::Choice;
    ///
    /// let choice_only_primary = Choice::new(1, Vec::<i32>::new());
    /// // Panics because there are no alternatives.
    /// let _ = choice_only_primary.swap_with_alternative(0);
    /// ```
    ///
    /// ### Panics - Empty Choice
    /// ```should_panic
    /// use rustica::datatypes::choice::Choice;
    ///
    /// let empty_choice: Choice<i32> = Choice::new_empty();
    /// // Panics because an empty choice has no primary or alternatives.
    /// let _ = empty_choice.swap_with_alternative(0);
    /// ```
    ///
    /// # See Also
    /// - [`Choice::new()`](Self::new) - For creating a `Choice`.
    /// - [`Choice::remove_alternative()`](Self::remove_alternative) - To remove an alternative.
    /// - [`Choice::add_alternatives()`](Self::add_alternatives) - To add alternatives.
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

        let values = match Arc::try_unwrap(self.values) {
            Ok(mut values) => {
                values.swap(0, actual_alt_index);
                Arc::new(values)
            },
            Err(arc) => {
                let mut new_values = Arc::clone(&arc);
                Arc::make_mut(&mut new_values).swap(0, actual_alt_index);
                new_values
            },
        };

        Self { values }
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
            Ok(values) => values
                .into_iter()
                .next()
                .expect("Cannot get value from an empty Choice"),
            Err(arc) => arc
                .first()
                .cloned()
                .expect("Cannot get value from an empty Choice"),
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

        match Arc::try_unwrap(self.values) {
            Ok(mut values) => {
                let mut f = f;
                let primary = f(values.remove(0));
                let alternatives: SmallVec<[B; 8]> = values.into_iter().map(f).collect();
                Choice::new(primary, alternatives)
            },
            Err(arc) => {
                let values = arc.as_ref();
                let mut f = f;
                let primary = f(values[0].clone());
                let alternatives: SmallVec<[B; 8]> =
                    values[1..].iter().map(|val| f(val.clone())).collect();
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

        match Arc::try_unwrap(self.values) {
            Ok(mut self_values) => {
                let primary = self_values.remove(0);
                Choice::new(
                    primary,
                    self_values
                        .into_iter()
                        .chain(other.values.as_ref().iter().cloned()),
                )
            },
            Err(arc) => {
                let self_values = arc.as_ref();
                let primary = self_values[0].clone();
                Choice::new(
                    primary,
                    self_values[1..]
                        .iter()
                        .cloned()
                        .chain(other.values.as_ref().iter().cloned()),
                )
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

        // Apply additional functions to primary value + apply all functions to all alternatives
        let alternatives: SmallVec<[B; 8]> = f_values[1..]
            .iter()
            .map(|f_alt| f_alt(&self_values[0]))
            .chain(self_values[1..].iter().flat_map(|self_alt| {
                std::iter::once(f_first(self_alt))
                    .chain(f_values[1..].iter().map(move |f_alt| f_alt(self_alt)))
            }))
            .collect();

        Choice::new(primary, alternatives)
    }

    fn apply_owned<B, F>(self, f: Self::Output<F>) -> Self::Output<B>
    where
        F: Fn(T) -> B,
        B: Clone,
    {
        if self.values.is_empty() || f.values.is_empty() {
            return Choice::new_empty();
        }

        let f_values = f.values;

        match Arc::try_unwrap(self.values) {
            Ok(mut self_values) => {
                let f_first = &f_values.as_ref()[0];
                let first_value = self_values[0].clone();
                let primary = f_first(first_value);

                // Apply functions to primary value
                let primary_alternatives: SmallVec<[B; 8]> = f_values.as_ref()[1..]
                    .iter()
                    .map(|f_alt| f_alt(self_values[0].clone()))
                    .collect();

                // Apply all functions to all alternative values
                let remaining_values = self_values.drain(1..).collect::<Vec<_>>();
                let other_alternatives: SmallVec<[B; 8]> = remaining_values
                    .into_iter()
                    .flat_map(|self_alt| {
                        std::iter::once(f_first(self_alt.clone())).chain(
                            f_values.as_ref()[1..]
                                .iter()
                                .map(move |f_alt| f_alt(self_alt.clone())),
                        )
                    })
                    .collect();

                // Combine all alternatives
                let all_alternatives: SmallVec<[B; 8]> = primary_alternatives
                    .into_iter()
                    .chain(other_alternatives)
                    .collect();

                Choice::new(primary, all_alternatives)
            },
            Err(arc) => {
                let self_values = arc.as_ref();
                let f_first = &f_values.as_ref()[0];
                let primary = f_first(self_values[0].clone());

                // Apply all functions to all values using iterators
                let alternatives: SmallVec<[B; 8]> = f_values.as_ref()[1..]
                    .iter()
                    .map(|f_alt| f_alt(self_values[0].clone()))
                    .chain(self_values[1..].iter().flat_map(|self_alt| {
                        std::iter::once(f_first(self_alt.clone())).chain(
                            f_values.as_ref()[1..]
                                .iter()
                                .map(move |f_alt| f_alt(self_alt.clone())),
                        )
                    }))
                    .collect();

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

        let self_values = self.values.as_ref();
        let b_values = b.values.as_ref();

        let primary = f(&self_values[0], &b_values[0]);

        // Calculate capacity for alternatives vector
        let capacity = self_values.len() * b_values.len() - 1;
        let mut alternatives = SmallVec::<[C; 8]>::with_capacity(capacity);

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

        let self_values = self.values;
        let b_values = b.values;

        let primary = f(self_values[0].clone(), b_values[0].clone());

        // Calculate capacity for alternatives vector
        let capacity = self_values.len() * b_values.len() - 1;
        let mut alternatives = SmallVec::<[C; 8]>::with_capacity(capacity);

        for (i, self_val) in self_values.iter().enumerate() {
            for (j, b_val) in b_values.iter().enumerate() {
                if i == 0 && j == 0 {
                    continue; // Skip primary
                }
                alternatives.push(f(self_val.clone(), b_val.clone()));
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
        let mut alternatives = SmallVec::<[D; 8]>::with_capacity(capacity);

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
            self.values[0].clone(),
            b.values[0].clone(),
            c.values[0].clone(),
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
    fn mzero<U: Clone>() -> Self::Output<U> {
        Choice::new_empty()
    }

    fn mplus(&self, other: &Self) -> Self {
        if self.is_empty() {
            other.clone()
        } else if other.is_empty() {
            self.clone()
        } else {
            self.combine(other)
        }
    }

    fn mplus_owned(self, other: Self) -> Self {
        if self.is_empty() {
            other
        } else if other.is_empty() {
            self
        } else {
            self.combine_owned(other)
        }
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
            write!(f, " | {alternatives}")?;
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
        self.iter()
            .fold(initial.clone(), |acc, value| f(&acc, value))
    }

    fn fold_right<B, F>(&self, initial: &B, f: F) -> B
    where
        F: Fn(&Self::Source, &B) -> B,
        B: Clone,
    {
        self.values
            .as_ref()
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
            _ => Self {
                values: Arc::new(collected),
            },
        }
    }
}

impl<T: Clone> FromIterator<Choice<T>> for Choice<T> {
    fn from_iter<I: IntoIterator<Item = Choice<T>>>(iter: I) -> Self {
        let values: SmallVec<[T; 8]> = iter
            .into_iter()
            .flat_map(|choice| {
                let values = choice.values.as_ref().to_vec();
                values.into_iter()
            })
            .collect();

        match values.len() {
            0 => Self::new_empty(),
            _ => Self {
                values: Arc::new(values),
            },
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
        choice.values.as_ref().iter().cloned().collect()
    }
}

impl<T: Clone + Default> Default for Choice<T> {
    fn default() -> Self {
        Self::new_empty()
    }
}

impl<T: Clone + Default> std::iter::Sum for Choice<T> {
    fn sum<I: Iterator<Item = Self>>(iter: I) -> Self {
        iter.fold(Choice::new_empty(), |acc, choice| acc.combine_owned(choice))
    }
}

#[cfg(feature = "develop")]
impl<T: Arbitrary + 'static> Arbitrary for Choice<T> {
    fn arbitrary(g: &mut Gen) -> Self {
        let primary = T::arbitrary(g);
        let alternatives: Vec<T> = (0..g.size()).map(|_| T::arbitrary(g)).collect();
        Choice::new(primary, alternatives)
    }
}
