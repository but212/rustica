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
//! use rustica::traits::foldable::Foldable;
//! use rustica::traits::monoid::Monoid;
//!
//! // Example with Vec
//! let numbers: Vec<i32> = vec![1, 2, 3, 4, 5];
//! let sum: i32 = numbers.clone().fold_left(0, |acc, x| acc + x);
//! assert_eq!(sum, 15);
//!
//! // `Option` and `Result` also fold their successful value, returning the initial
//! // accumulator for `None` or `Err`.
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
    /// let sum: i32 = numbers.fold_left(0, |acc, n| acc + n);
    /// assert_eq!(sum, 10);
    ///
    /// // Processing a Vec from left to right
    /// let strings: Vec<&str> = vec!["a", "b", "c"];
    /// let concat: String = strings.fold_left(String::new(), |mut acc, s| { acc.push_str(s); acc });
    /// assert_eq!(concat, "abc");
    /// ```
    fn fold_left<U, F>(&self, init: U, f: F) -> U
    where
        F: FnMut(U, &Self::Source) -> U;

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
    /// let sum: i32 = numbers.fold_right(0, |n, acc| n + acc);
    /// assert_eq!(sum, 10);
    ///
    /// // Processing a Vec from right to left
    /// let strings: Vec<&str> = vec!["a", "b", "c"];
    /// let concat: String = strings.fold_right(String::new(), |s, acc| s.to_string() + &acc);
    /// assert_eq!(concat, "abc");
    /// ```
    fn fold_right<U, F>(&self, init: U, f: F) -> U
    where
        F: FnMut(&Self::Source, U) -> U;

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
    /// use rustica::traits::foldable::Foldable;
    ///
    /// let words = vec!["hello", " ", "world"];
    /// let result: String = words.fold_map(|s| s.to_string());
    /// assert_eq!(result, "hello world");
    /// ```
    #[inline]
    fn fold_map<M: Monoid, F>(&self, mut f: F) -> M
    where
        F: FnMut(&Self::Source) -> M,
    {
        self.fold_left(M::empty(), |acc, x| acc.combine(f(x)))
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
    /// use rustica::traits::foldable::Foldable;
    ///
    /// let words = vec!["hello".to_string(), " ".to_string(), "world".to_string()];
    /// assert_eq!(words.fold_monoid::<String>(), "hello world");
    /// ```
    #[inline]
    fn fold_monoid<M: Monoid>(&self) -> M
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
        self.fold_left(0, |acc, _| acc + 1)
    }

    /// Tests if the structure is empty.
    #[inline]
    fn is_empty(&self) -> bool {
        self.length() == 0
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
    fn fold_option<B, F>(&self, mut f: F) -> Option<B>
    where
        F: FnMut(&Self::Source) -> Option<B>,
        B: Monoid,
    {
        self.fold_left(Some(B::empty()), |acc, x| {
            let acc = acc?;
            f(x).map(|value| acc.combine(value))
        })
    }
}

// Implement Foldable for Vec
impl<A> Foldable for Vec<A> {
    #[inline]
    fn fold_left<U, F>(&self, init: U, mut f: F) -> U
    where
        F: FnMut(U, &Self::Source) -> U,
    {
        let mut acc = init;
        for item in self {
            acc = f(acc, item);
        }
        acc
    }

    #[inline]
    fn fold_right<U, F>(&self, init: U, mut f: F) -> U
    where
        F: FnMut(&Self::Source, U) -> U,
    {
        let mut acc = init;
        for item in self.iter().rev() {
            acc = f(item, acc);
        }
        acc
    }
}

// Implement Foldable for Option
impl<A> Foldable for Option<A> {
    #[inline]
    fn fold_left<U, F>(&self, init: U, mut f: F) -> U
    where
        F: FnMut(U, &Self::Source) -> U,
    {
        match self {
            Some(a) => f(init, a),
            None => init,
        }
    }

    #[inline]
    fn fold_right<U, F>(&self, init: U, mut f: F) -> U
    where
        F: FnMut(&Self::Source, U) -> U,
    {
        match self {
            Some(a) => f(a, init),
            None => init,
        }
    }
}

// Implement Foldable for Result
impl<A, E: Clone> Foldable for Result<A, E> {
    #[inline]
    fn fold_left<U, F>(&self, init: U, mut f: F) -> U
    where
        F: FnMut(U, &Self::Source) -> U,
    {
        match self {
            Ok(a) => f(init, a),
            Err(_) => init,
        }
    }

    #[inline]
    fn fold_right<U, F>(&self, init: U, mut f: F) -> U
    where
        F: FnMut(&Self::Source, U) -> U,
    {
        match self {
            Ok(a) => f(a, init),
            Err(_) => init,
        }
    }
}

#[cfg(test)]
mod unit_tests {
    use super::Foldable;
    use crate::traits::monoid::Monoid;
    use crate::traits::semigroup::Semigroup;
    use std::cell::Cell;

    #[derive(Debug, PartialEq, Eq, Clone, Copy)]
    struct TestSum(i32);

    impl Semigroup for TestSum {
        fn combine(self, other: Self) -> Self {
            TestSum(self.0 + other.0)
        }
    }

    impl Monoid for TestSum {
        fn empty() -> Self {
            TestSum(0)
        }
    }

    #[test]
    fn folds_combine_values_and_preserve_empty_initial_values() {
        assert_eq!(
            vec![1, 2, 3, 4].fold_map(|n: &i32| TestSum(*n)),
            TestSum(10)
        );
        assert_eq!(
            vec![TestSum(1), TestSum(2), TestSum(3), TestSum(4)].fold_monoid::<TestSum>(),
            TestSum(10)
        );
        assert_eq!(Some(42).fold_left(0, |_, value| value * 2), 84);
        assert_eq!(None::<i32>.fold_left(100, |acc, _| acc), 100);
        assert_eq!(Ok::<i32, &str>(42).fold_left(0, |_, value| value + 10), 52);
        assert_eq!(Err::<i32, _>("error").fold_left(100, |acc, _| acc), 100);
    }

    #[test]
    fn fold_option_stops_after_the_first_none() {
        let visited = Cell::new(0);
        let result = vec![1, 2, 3].fold_option(|value| {
            visited.set(visited.get() + 1);
            if *value == 1 {
                None
            } else {
                Some(TestSum(*value))
            }
        });
        assert_eq!(result, None);
        assert_eq!(visited.get(), 1);
    }

    #[test]
    fn fold_left_works_with_move_only_accumulator() {
        struct NoClone(i32);
        let numbers = vec![1, 2, 3, 4];
        let res = numbers.fold_left(NoClone(0), |acc, &n| NoClone(acc.0 + n));
        assert_eq!(res.0, 10);
    }
}
