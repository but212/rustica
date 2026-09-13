//! # Wrapper Types
//!
//! This module provides various wrapper types that implement functional programming patterns
//! and algebraic structures. Wrappers enhance existing types with specific behaviors while
//! preserving their original functionality.
//!
//! ## Purpose
//!
//! Wrapper types serve several important purposes in functional programming:
//!
//! 1. **Algebraic Structures**: Implement mathematical structures like monoids and semigroups
//! 2. **Type-Based Operations**: Enable operations based on wrapped type (like Sum, Product)
//! 3. **Context Addition**: Add additional context or capabilities to basic types
//!
//! ## Available Wrapper Types
//!
//! ### Semigroup Wrappers
//!
//! These wrappers implement the `Semigroup` trait with specific combine operations:
//!
//! - `Sum<T>`: Forms a semigroup under addition (T must support `Add`)
//! - `Product<T>`: Forms a semigroup under multiplication (T must support `Mul`)
//! - `Min<T>`: Forms a semigroup taking the minimum value (T must support `PartialOrd`)
//! - `Max<T>`: Forms a semigroup taking the maximum value (T must support `PartialOrd`)
//! - `Predicate<T>`: Forms a monoid of intensional sets under logical union
//!
//! ### Option-Based Wrappers
//!
//! These wrappers provide special handling for `Option` types:
//!
//! - `First<T>`: Takes the first `Some` value when combining multiple `Option<T>` values
//! - `Last<T>`: Takes the last `Some` value when combining multiple `Option<T>` values
//!

//! ## Usage Patterns
//!
//! Wrapper types are typically used in these ways:
//!
//! ```rust
//! use rustica::datatypes::wrapper::sum::Sum;
//! use rustica::datatypes::wrapper::product::Product;
//! use rustica::traits::semigroup::Semigroup;
//!
//! // 1. Arithmetic with Sum/Product wrappers
//! let sum1: Sum<i32> = Sum(5);
//! let sum2: Sum<i32> = Sum(7);
//! let combined = sum1.combine(sum2);
//! assert_eq!(combined.into_inner(), 12); // 5 + 7 = 12
//!
//! // 2. Combining multiple values into one
//! let values = vec![Sum(1), Sum(2), Sum(3)];
//! let sum: i32 = values.into_iter()
//!     .fold(Sum(0), |acc, x| acc.combine(x))
//!     .into_inner();
//! assert_eq!(sum, 6); // 1 + 2 + 3 = 6
//!
//! ```
//!
//! ## When to Use Wrapper Types
//!
//! - Use `Sum`/`Product` when working with numeric collections that need to be combined
//! - Use `Min`/`Max` for finding extremes in collections
//! - Use `First`/`Last` when dealing with optional values that need to be combined with precedence rules
//!
//! ## Implementation Note
//!
//! Most wrapper types follow a simple pattern:
//!
//! 1. They store a single value of type T
//! 2. They implement relevant traits (Semigroup, Monoid, Functor, etc.)
//! 3. They provide methods to access the inner value
//!
//! This consistent interface makes it easy to understand and use these wrappers
//! in your own code.

pub mod first;
pub mod last;
pub mod max;
pub mod min;
pub mod predicate;
pub mod product;
pub mod sum;

#[cfg(test)]
mod unit_tests {
    use super::{
        first::First, last::Last, max::Max, min::Min, predicate::Predicate, product::Product,
        sum::Sum,
    };
    use crate::prelude::*;

    #[test]
    fn wrappers_satisfy_their_algebraic_operations() {
        assert_eq!(First(Some(1)).combine(First(Some(2))), First(Some(1)));
        assert_eq!(Last(Some(1)).combine(Last(Some(2))), Last(Some(2)));
        assert_eq!(First::<i32>::empty(), First(None));
        assert_eq!(Min(10).combine(Min(5)), Min(5));
        assert_eq!(Max(10).combine(Max(5)), Max(10));
        assert_eq!(Sum(10).combine(Sum(5)), Sum(15));
        assert_eq!(Product(10).combine(Product(5)), Product(50));
        assert_eq!(Product::<i32>::empty(), Product(1));

        let even = Predicate::new(|x: &i32| x % 2 == 0);
        let positive = Predicate::new(|x: &i32| *x > 0);
        assert!(even.union(&positive).contains(&3));
        assert!(even.intersection(&positive).contains(&2));
        assert!(!even.intersection(&positive).contains(&3));
        assert!(even.negate().contains(&3));
    }

    #[test]
    fn wrappers_are_functors() {
        assert_eq!(Sum(42).fmap(|x| x.to_string()), Sum("42".to_string()));
        assert_eq!(First(Some(10)).fmap(|x| x * 2), First(Some(20)));
    }
}

#[cfg(test)]
mod law_tests {
    use super::{
        first::First, last::Last, max::Max, min::Min, predicate::Predicate, product::Product,
        sum::Sum,
    };
    use crate::traits::{functor::Functor, monoid::Monoid, semigroup::Semigroup};

    #[test]
    fn wrappers_preserve_associativity_identity_and_functor_structure() {
        let sum = Sum(2).combine(Sum(3)).combine(Sum(4));
        assert_eq!(sum, Sum(2).combine(Sum(3).combine(Sum(4))));
        assert_eq!(Sum(2).combine(Sum::empty()), Sum(2));
        assert_eq!(
            Product(2).combine(Product(3)).combine(Product(4)),
            Product(2).combine(Product(3).combine(Product(4)))
        );
        assert_eq!(Min(1).combine(Min(3)).combine(Min(2)), Min(1));
        assert_eq!(Max(1).combine(Max(3)).combine(Max(2)), Max(3));
        assert_eq!(
            First(Some(1)).combine(First(None)).combine(First(Some(2))),
            First(Some(1))
        );
        assert_eq!(
            Last(Some(1)).combine(Last(None)).combine(Last(Some(2))),
            Last(Some(2))
        );
        assert_eq!(Sum(4).fmap(|x| x), Sum(4));
        assert_eq!(Product(4).fmap(|x| x), Product(4));
        assert_eq!(First(Some(4)).fmap(|x| x), First(Some(4)));
        assert_eq!(Last::<i32>(None).fmap(|x| x), Last(None));
    }

    #[test]
    fn predicate_monoid_laws_hold_and_predicates_are_thread_safe() {
        let even = Predicate::new(|value: &i32| value % 2 == 0);
        let positive = Predicate::new(|value: &i32| *value > 0);
        let negative = Predicate::new(|value: &i32| *value < 0);
        let left = even
            .clone()
            .combine(positive.clone())
            .combine(negative.clone());
        let right = even.clone().combine(positive.combine(negative));
        let empty = Predicate::<i32>::empty();

        for value in [-2, 0, 3] {
            assert_eq!(left.contains(&value), right.contains(&value));
            assert_eq!(
                empty.clone().combine(even.clone()).contains(&value),
                even.contains(&value)
            );
            assert_eq!(
                even.clone().combine(empty.clone()).contains(&value),
                even.contains(&value)
            );
        }

        fn assert_send_sync<T: Send + Sync>() {}
        assert_send_sync::<Predicate<i32>>();
    }
}
