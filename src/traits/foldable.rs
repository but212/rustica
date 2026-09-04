//! # Foldable
//!
//! This module provides the `Foldable` trait which represents a data structure that can be "folded" into a summary value.
//!
//! ## Mathematical Definition
//!
//! A foldable structure represents a container that supports a catamorphism operation,
//! which allows reducing the structure to a single value by applying a combining function
//! to its elements.
//!
//! ## Laws
//!
//! For a valid `Foldable` implementation, the following laws must hold:
//!
//! The precise equational laws depend on the chosen fold direction and the algebraic
//! properties of the combining function.
//!
//! In particular:
//! - `fold_left` must traverse elements from left to right.
//! - `fold_right` must traverse elements from right to left.
//! - For associative operations with an identity element (i.e., a monoid), left and right
//!   folds should agree on the final result.
//!
//! ## Common Use Cases
//!
//! The `Foldable` trait is commonly used in scenarios where:
//! - You need to reduce a collection to a single value
//! - You want to traverse a structure while accumulating results
//! - You need to combine elements using a monoid operation
//! - You want to perform operations like sum, product, or concatenation
//!
//! ## Examples
//!
//! ```rust
//! use rustica::traits::foldable::{Foldable, FoldableExt};
//! use rustica::traits::monoid::Monoid;
//!
//! // Example with Vec
//! let numbers: Vec<i32> = vec![1, 2, 3, 4, 5];
//! let sum: i32 = numbers.clone().fold_left(&0, |acc, x| acc + x);
//! assert_eq!(sum, 15);
//!
//! // `Option` and `Result` also fold their successful value, returning the initial
//! // accumulator for `None` or `Err`.
//!
//! // Using extension methods
//! assert_eq!(numbers.sum_values(), 15);
//! assert_eq!(numbers.any(|&x| x > 10), false);
//! assert_eq!(numbers.all(|&x| x < 10), true);
//! ```
//!
//! ## Relationship with Other Functional Traits
//!
//! - **Functor**: While `Functor` allows mapping over structures without changing their shape,
//!   `Foldable` allows reducing structures into a single value.
//!
//! - **Applicative**: `Applicative` focuses on applying functions within wrapped contexts,
//!   whereas `Foldable` focuses on collapsing a structure.
//!
//! - **Monad**: `Monad` deals with sequential computations where each step depends on the previous,
//!   whereas `Foldable` accumulates values independent of sequence.
//!
//! - **Monoid**: `Foldable` frequently uses monoid operations to combine elements during folding,
//!   making Monoid a natural companion trait.

use crate::traits::hkt::HKT;
use crate::traits::monoid::Monoid;
use std::ops::{Add, Mul};

/// A `Foldable` type is a data structure that can be "folded" into a summary value.
///
/// # Type Parameters
///
/// The trait is implemented on types that implement `HKT`, where:
/// * `Source` is the type of elements in the foldable structure
/// * `Output<T>` represents the structure containing elements of type `T`
pub trait Foldable: HKT {
    /// Left-associative fold of a structure.
    ///
    /// Reduces the structure to a single value by applying a combining function from
    /// left to right, starting with an initial value.
    ///
    /// # Type Parameters
    ///
    /// * `U`: The type of the accumulated value
    /// * `F`: The type of the combining function
    ///
    /// # Arguments
    ///
    /// * `init`: The initial value for the fold
    /// * `f`: A function that combines the accumulated value with an element
    ///
    /// # Returns
    ///
    /// The final accumulated value after folding the entire structure.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::traits::foldable::Foldable;
    ///
    /// let numbers: Vec<i32> = vec![1, 2, 3, 4];
    /// let sum: i32 = numbers.fold_left(&0, |acc, n| acc + n);
    /// assert_eq!(sum, 10);
    ///
    /// // Processing a Vec from left to right
    /// let strings: Vec<&str> = vec!["a", "b", "c"];
    /// let concat: String = strings.fold_left(&String::new(), |acc, s| acc.to_owned() + s);
    /// assert_eq!(concat, "abc");
    /// ```
    fn fold_left<U: Clone, F>(&self, init: &U, f: F) -> U
    where
        F: Fn(&U, &Self::Source) -> U;

    /// Right-associative fold of a structure.
    ///
    /// Reduces the structure to a single value by applying a combining function from
    /// right to left, starting with an initial value.
    ///
    /// # Type Parameters
    ///
    /// * `U`: The type of the accumulated value
    /// * `F`: The type of the combining function
    ///
    /// # Arguments
    ///
    /// * `init`: The initial value for the fold
    /// * `f`: A function that combines an element with the accumulated value
    ///
    /// # Returns
    ///
    /// The final accumulated value after folding the entire structure.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::traits::foldable::Foldable;
    ///
    /// let numbers: Vec<i32> = vec![1, 2, 3, 4];
    /// let sum: i32 = numbers.fold_right(&0, |n, acc| n + acc);
    /// assert_eq!(sum, 10);
    ///
    /// // Processing a Vec from right to left
    /// let strings: Vec<&str> = vec!["a", "b", "c"];
    /// let concat: String = strings.fold_right(&String::new(), |s, acc| s.to_string() + &acc);
    /// assert_eq!(concat, "abc");
    /// ```
    fn fold_right<U: Clone, F>(&self, init: &U, f: F) -> U
    where
        F: Fn(&Self::Source, &U) -> U;

    /// Maps elements to a monoid and combines them.
    ///
    /// This operation first maps each element to a value in a monoid, then combines
    /// all these values using the monoid's combine operation.
    ///
    /// # Type Parameters
    ///
    /// * `M`: The monoid type that elements will be mapped to
    /// * `F`: The type of the mapping function
    ///
    /// # Arguments
    ///
    /// * `f`: The function that maps elements to the monoid type
    ///
    /// # Returns
    ///
    /// The combined monoid value
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::prelude::*;
    ///
    /// let numbers = vec![1, 2, 3, 4];
    /// let result: Sum<i32> = numbers.fold_map(|n| Sum(*n));
    /// assert_eq!(result, Sum(10));
    /// ```
    #[inline]
    fn fold_map<M: Monoid + Clone, F>(&self, f: F) -> M
    where
        F: Fn(&Self::Source) -> M,
    {
        self.fold_left(&M::empty(), |acc, x| acc.combine(&f(x)))
    }

    /// Fold a structure into a monoid.
    ///
    /// Reduces the structure to a single value by combining all elements using the
    /// monoid's combine operation and identity element.
    ///
    /// # Type Parameters
    ///
    /// * `M`: The monoid type
    ///
    /// # Returns
    ///
    /// The combined value using the monoid's operations.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::prelude::*;
    ///
    /// let numbers = vec![Sum(1), Sum(2), Sum(3), Sum(4)];
    /// assert_eq!(numbers.fold_monoid::<Sum<i32>>(), Sum(10));
    /// ```
    #[inline]
    fn fold_monoid<M: Monoid + Clone>(&self) -> M
    where
        Self::Source: Clone + Into<M>,
    {
        self.fold_map(|x| x.clone().into())
    }

    /// Returns the number of elements in the foldable structure.
    ///
    /// This is a convenience method that counts the number of elements by
    /// folding over the structure with a counter.
    ///
    /// # Returns
    ///
    /// The number of elements in the structure
    #[inline]
    fn length(&self) -> usize {
        self.fold_left(&0, |acc, _| acc + 1)
    }

    /// Tests if the structure is empty.
    #[inline]
    fn is_empty(&self) -> bool {
        self.length() == 0
    }
}

/// Extension methods for the `Foldable` trait.
///
/// This trait provides additional utility methods for all types that implement `Foldable`.
pub trait FoldableExt: Foldable {
    /// Finds the first element in the foldable that satisfies the predicate.
    ///
    /// # Arguments
    ///
    /// * `pred` - A predicate function that returns true for the element to find
    ///
    /// # Returns
    ///
    /// * `Some(element)` if an element satisfying the predicate is found
    /// * `None` if no element satisfies the predicate
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::traits::foldable::FoldableExt;
    ///
    /// let numbers: Vec<i32> = vec![1, 2, 3, 4, 5];
    /// let first_even: Option<i32> = numbers.find(|&n| n % 2 == 0);
    /// assert_eq!(first_even, Some(2));
    ///
    /// let no_match: Option<i32> = numbers.find(|&n| n > 10);
    /// assert_eq!(no_match, None);
    /// ```
    #[inline]
    fn find<F>(&self, pred: F) -> Option<Self::Source>
    where
        F: Fn(&Self::Source) -> bool,
        Self::Source: Clone,
    {
        self.fold_left(&None, |acc, x| {
            if acc.is_some() {
                acc.clone()
            } else if pred(x) {
                Some(x.clone())
            } else {
                None
            }
        })
    }

    /// Tests whether all elements in the foldable satisfy the predicate.
    ///
    /// # Arguments
    ///
    /// * `pred` - A predicate function
    ///
    /// # Returns
    ///
    /// `true` if all elements satisfy the predicate, or if the foldable is empty;
    /// `false` otherwise.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::traits::foldable::FoldableExt;
    ///
    /// let numbers: Vec<i32> = vec![2, 4, 6, 8];
    /// let all_even: bool = numbers.all(|&n| n % 2 == 0);
    /// assert!(all_even);
    ///
    /// let mixed: Vec<i32> = vec![2, 4, 5, 8];
    /// let all_even: bool = mixed.all(|&n| n % 2 == 0);
    /// assert!(!all_even);
    /// ```
    #[inline]
    fn all<F>(&self, pred: F) -> bool
    where
        F: Fn(&Self::Source) -> bool,
    {
        self.fold_left(&true, |acc, x| *acc && pred(x))
    }

    /// Tests whether any element in the foldable satisfies the predicate.
    ///
    /// # Arguments
    ///
    /// * `pred` - A predicate function
    ///
    /// # Returns
    ///
    /// `true` if any element satisfies the predicate; `false` if no element
    /// satisfies the predicate or if the foldable is empty.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::traits::foldable::FoldableExt;
    ///
    /// let numbers: Vec<i32> = vec![1, 3, 5, 6];
    /// let has_even: bool = numbers.any(|&n| n % 2 == 0);
    /// assert!(has_even);
    ///
    /// let odd_only: Vec<i32> = vec![1, 3, 5, 7];
    /// let has_even: bool = odd_only.any(|&n| n % 2 == 0);
    /// assert!(!has_even);
    /// ```
    #[inline]
    fn any<F>(&self, pred: F) -> bool
    where
        F: Fn(&Self::Source) -> bool,
    {
        self.fold_left(&false, |acc, x| *acc || pred(x))
    }

    /// Tests whether the foldable contains a specific value.
    ///
    /// # Arguments
    ///
    /// * `value` - The value to search for
    ///
    /// # Returns
    ///
    /// `true` if the value is found; `false` otherwise.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::traits::foldable::FoldableExt;
    ///
    /// let numbers: Vec<i32> = vec![1, 2, 3, 4, 5];
    /// assert!(numbers.contains(&3));
    /// assert!(!numbers.contains(&10));
    /// ```
    #[inline]
    fn contains(&self, value: &Self::Source) -> bool
    where
        Self::Source: PartialEq,
    {
        self.any(|x| x == value)
    }

    /// Folds over a structure with an optional monoidal value.
    ///
    /// This is a more powerful version of fold that stops invoking `f` after `None` is encountered.
    ///
    /// # Type Parameters
    ///
    /// * `B`: The type of the accumulated value
    /// * `F`: The type of the function to apply
    ///
    /// # Arguments
    ///
    /// * `f`: Function that returns an optional monoidal value
    ///
    /// # Returns
    ///
    /// The final accumulated value, or None if a None was encountered during folding.
    #[inline]
    fn fold_option<B, F>(&self, f: F) -> Option<B>
    where
        F: Fn(&Self::Source) -> Option<B>,
        B: Monoid + Clone,
    {
        self.fold_left(&Some(B::empty()), |acc, x| {
            let Some(acc) = acc else {
                return None;
            };
            f(x).map(|value| acc.combine(&value))
        })
    }

    /// Checks if the foldable is sorted.
    ///
    /// # Returns
    ///
    /// `true` if the foldable is sorted in ascending order; `false` otherwise.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::traits::foldable::FoldableExt;
    ///
    /// let sorted: Vec<i32> = vec![1, 2, 3, 4, 5];
    /// assert!(sorted.is_sorted());
    ///
    /// let unsorted: Vec<i32> = vec![1, 3, 2, 4, 5];
    /// assert!(!unsorted.is_sorted());
    /// ```
    #[inline]
    fn is_sorted(&self) -> bool
    where
        Self::Source: Clone + Ord,
    {
        self.fold_left(&(true, None), |(is_sorted, prev), curr| {
            if !is_sorted {
                (false, Some(curr.clone()))
            } else {
                match prev {
                    None => (true, Some(curr.clone())),
                    Some(p) => (p <= curr, Some(curr.clone())),
                }
            }
        })
        .0
    }

    /// Converts a foldable structure to a Vec.
    ///
    /// # Returns
    ///
    /// A Vec containing all elements from the foldable structure.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::traits::foldable::FoldableExt;
    ///
    /// let option: Option<i32> = Some(42);
    /// let vec: Vec<i32> = option.to_vec();
    /// assert_eq!(vec, vec![42]);
    ///
    /// let option: Option<i32> = None;
    /// let vec: Vec<i32> = option.to_vec();
    /// assert_eq!(vec, Vec::<i32>::new());
    /// ```
    #[inline]
    fn to_vec(&self) -> Vec<Self::Source>
    where
        Self::Source: Clone,
    {
        // `fold_left` takes its accumulator by reference and returns a new
        // value, so cloning a growing `Vec` here makes this operation O(n²).
        // Keep the public fold API unchanged while using a private mutable
        // side accumulator. Each source element is cloned exactly once.
        let out = std::cell::RefCell::new(Vec::new());
        self.fold_left(&(), |_, x| {
            out.borrow_mut().push(x.clone());
        });
        out.into_inner()
    }

    /// Sums all elements in the foldable.
    ///
    /// # Returns
    ///
    /// The sum of all elements.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::traits::foldable::FoldableExt;
    ///
    /// let numbers: Vec<i32> = vec![1, 2, 3, 4];
    /// assert_eq!(numbers.sum_values(), 10);
    /// ```
    #[inline]
    fn sum_values(&self) -> Self::Source
    where
        Self::Source: Add<Output = Self::Source> + Default + Clone,
    {
        self.fold_left(&Self::Source::default(), |acc, x| acc.clone() + x.clone())
    }

    /// Multiplies all elements in the foldable.
    ///
    /// # Returns
    ///
    /// The product of all elements.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::traits::foldable::FoldableExt;
    ///
    /// let numbers: Vec<i32> = vec![1, 2, 3, 4];
    /// assert_eq!(numbers.product_values(), 24);
    /// ```
    #[inline]
    fn product_values(&self) -> Self::Source
    where
        Self::Source: Mul<Output = Self::Source> + From<u8> + Clone,
    {
        self.fold_left(&Self::Source::from(1), |acc, x| acc.clone() * x.clone())
    }

    /// Finds the maximum element in the foldable.
    ///
    /// # Returns
    ///
    /// `Some(max)` with the maximum element, or `None` if the foldable is empty.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::traits::foldable::FoldableExt;
    ///
    /// let numbers: Vec<i32> = vec![4, 2, 7, 1, 5];
    /// assert_eq!(numbers.maximum(), Some(7));
    ///
    /// let empty: Vec<i32> = vec![];
    /// assert_eq!(empty.maximum(), None);
    /// ```
    #[inline]
    fn maximum(&self) -> Option<Self::Source>
    where
        Self::Source: Ord + Clone,
    {
        self.fold_left(&None, |max: &Option<Self::Source>, x| match max {
            None => Some(x.clone()),
            Some(current_max) => Some(if x > current_max {
                x.clone()
            } else {
                current_max.clone()
            }),
        })
    }

    /// Finds the minimum element in the foldable.
    ///
    /// # Returns
    ///
    /// `Some(min)` with the minimum element, or `None` if the foldable is empty.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::traits::foldable::FoldableExt;
    ///
    /// let numbers: Vec<i32> = vec![4, 2, 7, 1, 5];
    /// assert_eq!(numbers.minimum(), Some(1));
    ///
    /// let empty: Vec<i32> = vec![];
    /// assert_eq!(empty.minimum(), None);
    /// ```
    #[inline]
    fn minimum(&self) -> Option<Self::Source>
    where
        Self::Source: Ord + Clone,
    {
        self.fold_left(&None, |min: &Option<Self::Source>, x| match min {
            None => Some(x.clone()),
            Some(current_min) => Some(if x < current_min {
                x.clone()
            } else {
                current_min.clone()
            }),
        })
    }

    /// Uses a combining function to reduce the elements of the structure to a single value.
    ///
    /// # Type Parameters
    ///
    /// * `F`: The type of the combining function
    ///
    /// # Arguments
    ///
    /// * `f`: The combining function
    ///
    /// # Returns
    ///
    /// `Some(result)` with the reduced value, or `None` if the foldable is empty.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::traits::foldable::FoldableExt;
    ///
    /// let numbers: Vec<i32> = vec![1, 2, 3, 4];
    /// let sum = numbers.reduce(|a, b| a + b);
    /// assert_eq!(sum, Some(10));
    ///
    /// let empty: Vec<i32> = vec![];
    /// let sum = empty.reduce(|a, b| a + b);
    /// assert_eq!(sum, None);
    /// ```
    #[inline]
    fn reduce<F>(&self, f: F) -> Option<Self::Source>
    where
        F: Fn(&Self::Source, &Self::Source) -> Self::Source,
        Self::Source: Clone,
    {
        self.fold_left(&None, |acc: &Option<Self::Source>, x| match acc {
            None => Some(x.clone()),
            Some(a) => Some(f(a, x)),
        })
    }
}

// Implement FoldableExt for all types implementing Foldable
impl<T: Foldable> FoldableExt for T {}

// Implement Foldable for Vec
impl<A: Clone> Foldable for Vec<A> {
    #[inline]
    fn fold_left<U: Clone, F>(&self, init: &U, f: F) -> U
    where
        F: Fn(&U, &A) -> U,
    {
        let mut acc = init.clone();
        for item in self {
            acc = f(&acc, item);
        }
        acc
    }

    #[inline]
    fn fold_right<U: Clone, F>(&self, init: &U, f: F) -> U
    where
        F: Fn(&A, &U) -> U,
    {
        let mut acc = init.clone();
        for item in self.iter().rev() {
            acc = f(item, &acc);
        }
        acc
    }
}

// Implement Foldable for Option
impl<A: Clone> Foldable for Option<A> {
    #[inline]
    fn fold_left<U: Clone, F>(&self, init: &U, f: F) -> U
    where
        F: Fn(&U, &A) -> U,
    {
        match self {
            Some(a) => f(init, a),
            None => init.clone(),
        }
    }

    #[inline]
    fn fold_right<U: Clone, F>(&self, init: &U, f: F) -> U
    where
        F: Fn(&A, &U) -> U,
    {
        match self {
            Some(a) => f(a, init),
            None => init.clone(),
        }
    }
}

// Implement Foldable for Result
impl<A: Clone, E: Clone> Foldable for Result<A, E> {
    #[inline]
    fn fold_left<U: Clone, F>(&self, init: &U, f: F) -> U
    where
        F: Fn(&U, &A) -> U,
    {
        match self {
            Ok(a) => f(init, a),
            Err(_) => init.clone(),
        }
    }

    #[inline]
    fn fold_right<U: Clone, F>(&self, init: &U, f: F) -> U
    where
        F: Fn(&A, &U) -> U,
    {
        match self {
            Ok(a) => f(a, init),
            Err(_) => init.clone(),
        }
    }
}

#[cfg(test)]
mod unit_tests {
    use super::{Foldable, FoldableExt};
    use crate::datatypes::wrapper::sum::Sum;
    use std::cell::Cell;

    #[test]
    fn folds_combine_values_and_preserve_empty_initial_values() {
        assert_eq!(vec![1, 2, 3, 4].fold_map(|n: &i32| Sum(*n)), Sum(10));
        assert_eq!(
            vec![Sum(1), Sum(2), Sum(3), Sum(4)].fold_monoid::<Sum<i32>>(),
            Sum(10)
        );
        assert_eq!(Some(42).fold_left(&0, |_, value| value * 2), 84);
        assert_eq!(None::<i32>.fold_left(&100, |acc, _| *acc), 100);
        assert_eq!(Ok::<i32, &str>(42).fold_left(&0, |_, value| value + 10), 52);
        assert_eq!(Err::<i32, _>("error").fold_left(&100, |acc, _| *acc), 100);
    }

    #[test]
    fn fold_option_stops_after_the_first_none() {
        let visited = Cell::new(0);
        let result = vec![1, 2, 3].fold_option(|value| {
            visited.set(visited.get() + 1);
            if *value == 1 { None } else { Some(Sum(*value)) }
        });
        assert_eq!(result, None);
        assert_eq!(visited.get(), 1);
    }
}
