//! # Predicate
//!
//! This module provides the `Predicate` type, representing intensional sets as predicate functions.
//!
//! ## Overview
//!
//! A `Predicate<A>` wraps a function that determines whether a value of type `A` satisfies a certain condition.
//! Predicates are composable and support logical operations such as AND, OR, NOT, and difference, making them
//! useful for representing and manipulating sets defined by conditions.
//!
//! ## Features
//!
//! - Functional, composable representation of sets
//! - Logical operations: union, intersection, difference, and negation
//! - Operator overloading for expressive predicate composition
//! - Implements `Semigroup` and `Monoid` traits for algebraic composition
//!
//! ## Functional Programming Context
//!
//! `Predicate<A>` implements several functional programming type classes:
//!
//! - **Semigroup**: Predicates can be combined using logical OR via `combine`
//! - **Monoid**: Provides an identity element (`empty`) that always returns false
//! - **Functor**: Allows mapping over the input type while preserving the predicate behavior
//!
//! These implementations enable predicates to work seamlessly with other functional abstractions in Rustica.
//!
//! ## Type Class Laws
//!
//! ### Semigroup Laws
//!
//! - **Associativity**: `(a.combine(b)).combine(c) == a.combine(b.combine(c))`
//!   - The order in which predicates are combined using logical OR doesn't matter.
//!
//! ### Monoid Laws
//!
//! - **Left Identity**: `empty().combine(a) == a`
//!   - Combining a predicate with the empty predicate (always returns false) using OR
//!     yields the original predicate.
//!
//! - **Right Identity**: `a.combine(empty()) == a`
//!   - The identity property holds regardless of the order of combination.
//!
//! ### Set Operation Laws
//!
//! - **Commutativity of Union**: `a.union(b) == b.union(a)`
//!   - The order of operands in a union operation doesn't matter.
//!
//! - **Associativity of Intersection**: `a.intersection(b).intersection(c) == a.intersection(b.intersection(c))`
//!   - The order of operations for intersection doesn't affect the result.
//!
//! - **Distributivity**: `a.intersection(b.union(c)) == a.intersection(b).union(a.intersection(c))`
//!   - Intersection distributes over union, similar to multiplication over addition.
//!
//! - **Complement Laws**: `a.negate().negate() == a`
//!   - Double negation yields the original predicate.
//!
//! ## Type Class Implementations
//!
//! - **Semigroup**: `combine` creates a union of predicates (logical OR)
//! - **Monoid**: `empty` creates a predicate that always returns false
//! - **HKT**: Higher-kinded type representation for advanced type-level operations
//!
//! ## Quick Start
//!
//! ```rust
//! use rustica::datatypes::wrapper::predicate::Predicate;
//! use rustica::traits::{semigroup::Semigroup, monoid::Monoid};
//!
//! // Create predicates for different conditions
//! let is_positive = Predicate::new(|&x: &i32| x > 0);
//! let is_even = Predicate::new(|&x: &i32| x % 2 == 0);
//!
//! // Test values against predicates
//! assert!(is_positive.contains(&5));
//! assert!(!is_positive.contains(&-3));
//! assert!(is_even.contains(&4));
//! assert!(!is_even.contains(&3));
//!
//! // Combine predicates with logical operations
//! let is_positive_or_even = is_positive.union(&is_even); // OR
//! let is_positive_and_even = is_positive.intersection(&is_even); // AND
//!
//! assert!(is_positive_or_even.contains(&6)); // positive and even
//! assert!(is_positive_and_even.contains(&6)); // both conditions
//! assert!(!is_positive_and_even.contains(&3)); // positive but odd
//! ```
//!
//! ## Usage
//!
//! This module is ideal for use cases where sets are defined by properties or conditions rather than explicit enumeration.

use crate::traits::hkt::HKT;
use crate::traits::monoid::Monoid;
use crate::traits::semigroup::Semigroup;
use std::ops::{BitAnd, BitOr, Not, Sub};
use std::rc::Rc;

/// An intensional set, defined by a predicate function.
///
/// A `Predicate<A>` wraps a function that determines whether a value of type `A`
/// satisfies some condition. Predicates can be combined using logical operations
/// like AND, OR, NOT, and difference.
#[repr(transparent)]
#[derive(Clone)]
pub struct Predicate<A> {
    func: Rc<dyn Fn(&A) -> bool>,
}

impl<A> Predicate<A> {
    /// Create a new predicate from a closure.
    ///
    /// # Parameters
    ///
    /// * `f`: A function that evaluates whether a value of type `A` satisfies the predicate.
    ///
    /// # Returns
    ///
    /// A new `Predicate<A>` wrapping the provided function.
    ///
    /// # Example
    ///
    /// ```
    /// use rustica::datatypes::wrapper::predicate::Predicate;
    ///
    /// let is_even = Predicate::new(|x: &i32| *x % 2 == 0);
    /// assert!(is_even.contains(&2));
    /// assert!(!is_even.contains(&3));
    /// ```
    ///
    /// # Performance
    ///
    /// - Time Complexity: O(1) - Simply wraps the function in an Rc
    /// - Memory Usage: O(1) - Stores a single Rc pointer to the function
    #[inline]
    pub fn new<F>(f: F) -> Self
    where
        F: Fn(&A) -> bool + 'static,
    {
        Predicate { func: Rc::new(f) }
    }

    /// Returns true if the value satisfies the predicate.
    ///
    /// # Arguments
    ///
    /// * `a` - The value to test against the predicate
    ///
    /// # Returns
    ///
    /// `true` if the value satisfies the predicate; `false` otherwise.
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::datatypes::wrapper::predicate::Predicate;
    ///
    /// let is_positive = Predicate::new(|x: &i32| *x > 0);
    /// assert!(is_positive.contains(&5));
    /// assert!(!is_positive.contains(&-3));
    /// ```
    ///
    /// # Performance
    ///
    /// - Time Complexity: O(f) where f is the complexity of the wrapped function
    /// - Memory Usage: O(1) - No additional memory allocated during evaluation
    #[inline]
    pub fn contains(&self, a: &A) -> bool {
        (self.func)(a)
    }

    /// Returns a predicate which is the union of this predicate and another.
    ///
    /// The union predicate evaluates to `true` if either this predicate or the `other` predicate
    /// evaluates to `true` for a given input.
    ///
    /// # Arguments
    ///
    /// * `other` - Another predicate to union with this one
    ///
    /// # Returns
    ///
    /// A new `Predicate<A>` representing the union of both predicates
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::datatypes::wrapper::predicate::Predicate;
    ///
    /// let is_even = Predicate::new(|x: &i32| *x % 2 == 0);
    /// let is_positive = Predicate::new(|x: &i32| *x > 0);
    /// let even_or_positive = is_even.union(&is_positive);
    ///
    /// assert!(even_or_positive.contains(&2));  // Even and positive
    /// assert!(even_or_positive.contains(&-4)); // Even but not positive
    /// assert!(even_or_positive.contains(&3));  // Positive but not even
    /// assert!(!even_or_positive.contains(&-5)); // Neither even nor positive
    /// ```
    ///
    /// # Performance
    ///
    /// - Time Complexity: O(1) for creation, O(f1 + f2) for evaluation where f1 and f2 are the
    ///   complexities of the component predicates
    /// - Memory Usage: O(1) - Creates a new predicate with references to existing ones
    /// - Short-circuit Evaluation: Returns early if the first predicate evaluates to true
    pub fn union(&self, other: &Predicate<A>) -> Predicate<A>
    where
        A: 'static,
    {
        Predicate::new({
            let f1 = self.func.clone();
            let f2 = other.func.clone();
            move |a| f1(a) || f2(a)
        })
    }

    /// Returns a predicate which is the intersection of this predicate and another.
    ///
    /// The intersection predicate evaluates to `true` only if both this predicate and the `other` predicate
    /// evaluate to `true` for a given input.
    ///
    /// # Arguments
    ///
    /// * `other` - Another predicate to intersect with this one
    ///
    /// # Returns
    ///
    /// A new `Predicate<A>` representing the intersection of both predicates
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::datatypes::wrapper::predicate::Predicate;
    ///
    /// let is_even = Predicate::new(|x: &i32| *x % 2 == 0);
    /// let is_positive = Predicate::new(|x: &i32| *x > 0);
    /// let even_and_positive = is_even.intersection(&is_positive);
    ///
    /// assert!(even_and_positive.contains(&2));  // Even and positive
    /// assert!(!even_and_positive.contains(&-4)); // Even but not positive
    /// assert!(!even_and_positive.contains(&3));  // Positive but not even
    /// assert!(!even_and_positive.contains(&-5)); // Neither even nor positive
    /// ```
    ///
    /// # Performance
    ///
    /// - Time Complexity: O(1) for creation, O(f1 + f2) for evaluation where f1 and f2 are the
    ///   complexities of the component predicates
    /// - Memory Usage: O(1) - Creates a new predicate with references to existing ones
    /// - Short-circuit Evaluation: Returns early if the first predicate evaluates to false
    pub fn intersection(&self, other: &Predicate<A>) -> Predicate<A>
    where
        A: 'static,
    {
        Predicate::new({
            let f1 = self.func.clone();
            let f2 = other.func.clone();
            move |a| f1(a) && f2(a)
        })
    }

    /// Returns a predicate which is the set difference of this predicate and another.
    ///
    /// The resulting predicate evaluates to `true` for inputs that satisfy this predicate
    /// but do not satisfy the `remove` predicate.
    ///
    /// # Arguments
    ///
    /// * `remove` - The predicate to subtract from this one
    ///
    /// # Returns
    ///
    /// A new `Predicate<A>` representing the set difference
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::datatypes::wrapper::predicate::Predicate;
    ///
    /// let is_integer = Predicate::new(|x: &f64| x.fract() == 0.0);
    /// let is_negative = Predicate::new(|x: &f64| *x < 0.0);
    /// let positive_integers = is_integer.diff(&is_negative);
    ///
    /// assert!(positive_integers.contains(&2.0));  // Integer and not negative
    /// assert!(!positive_integers.contains(&-3.0)); // Integer but negative
    /// assert!(!positive_integers.contains(&1.5));  // Not an integer
    /// ```
    ///
    /// # Performance
    ///
    /// - Time Complexity: O(1) for creation, O(f1 + f2) for evaluation where f1 and f2 are the
    ///   complexities of the component predicates
    /// - Memory Usage: O(1) - Creates a new predicate with references to existing ones
    /// - Short-circuit Evaluation: Returns early if the first predicate evaluates to false
    pub fn diff(&self, remove: &Predicate<A>) -> Predicate<A>
    where
        A: 'static,
    {
        Predicate::new({
            let f1 = self.func.clone();
            let f2 = remove.func.clone();
            move |a| f1(a) && !f2(a)
        })
    }

    /// Returns a predicate that is the negation of this predicate.
    ///
    /// The resulting predicate evaluates to `true` for inputs where this predicate
    /// evaluates to `false`, and vice versa.
    ///
    /// # Returns
    ///
    /// A new `Predicate<A>` representing the logical negation
    ///
    /// # Examples
    ///
    /// ```
    /// use rustica::datatypes::wrapper::predicate::Predicate;
    ///
    /// let is_even = Predicate::new(|x: &i32| *x % 2 == 0);
    /// let is_odd = is_even.negate();
    ///
    /// assert!(!is_odd.contains(&2));
    /// assert!(is_odd.contains(&3));
    /// ```
    ///
    /// # Performance
    ///
    /// - Time Complexity: O(1) for creation, O(f) for evaluation where f is the
    ///   complexity of the original predicate
    /// - Memory Usage: O(1) - Creates a new predicate with a reference to the existing one
    pub fn negate(&self) -> Predicate<A>
    where
        A: 'static,
    {
        Predicate::new({
            let f = self.func.clone();
            move |a| !f(a)
        })
    }
}

// Operator overloads
impl<A> BitOr for Predicate<A>
where
    A: 'static,
{
    type Output = Predicate<A>;
    #[inline]
    fn bitor(self, rhs: Predicate<A>) -> Predicate<A> {
        self.union(&rhs)
    }
}

impl<A> BitAnd for Predicate<A>
where
    A: 'static,
{
    type Output = Predicate<A>;
    #[inline]
    fn bitand(self, rhs: Predicate<A>) -> Predicate<A> {
        self.intersection(&rhs)
    }
}

impl<A> Sub for Predicate<A>
where
    A: 'static,
{
    type Output = Predicate<A>;
    #[inline]
    fn sub(self, rhs: Predicate<A>) -> Predicate<A> {
        self.diff(&rhs)
    }
}

impl<A> Not for Predicate<A>
where
    A: 'static,
{
    type Output = Predicate<A>;
    #[inline]
    fn not(self) -> Predicate<A> {
        self.negate()
    }
}

impl<A: 'static> Semigroup for Predicate<A> {
    /// Combines two predicates using logical OR operation (union).
    ///
    /// The resulting predicate will evaluate to `true` for an input if either
    /// this predicate or the `other` predicate evaluates to `true` for that input.
    /// This is equivalent to the union of the two sets defined by these predicates.
    ///
    /// # Performance
    ///
    /// - **Time Complexity**: O(1) for creation, O(f1 + f2) for evaluation where f1 and f2 are the
    ///   complexities of the component predicates
    /// - **Memory Usage**: O(1) - Creates a new predicate with references to existing predicates
    /// - **Short-circuit Evaluation**: Returns early if the first predicate evaluates to true
    /// - **Cloning**: Only the Rc pointers are cloned, not the underlying functions
    ///
    /// # Type Class Laws
    ///
    /// ## Associativity: (a `combine` b) `combine` c = a `combine` (b `combine` c)
    ///
    /// ```rust
    /// use rustica::datatypes::wrapper::predicate::Predicate;
    /// use rustica::traits::semigroup::Semigroup;
    ///
    /// // Define three simple predicates
    /// let is_even = Predicate::new(|x: &i32| *x % 2 == 0);
    /// let is_positive = Predicate::new(|x: &i32| *x > 0);
    /// let is_multiple_of_3 = Predicate::new(|x: &i32| *x % 3 == 0);
    ///
    /// // Test values
    /// let test_values = [-6, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 9, 12];
    ///
    /// // Verify associativity
    /// fn verify_associativity(a: &Predicate<i32>, b: &Predicate<i32>, c: &Predicate<i32>, x: &i32) -> bool {
    ///     let left = a.combine(&b).combine(c).contains(x);
    ///     let right = a.combine(&b.combine(c)).contains(x);
    ///     left == right
    /// }
    ///
    /// // Verify the law for all test values
    /// for &val in test_values.iter() {
    ///     assert!(verify_associativity(&is_even, &is_positive, &is_multiple_of_3, &val));
    /// }
    /// ```
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::wrapper::predicate::Predicate;
    /// use rustica::traits::semigroup::Semigroup;
    ///
    /// let is_even = Predicate::new(|x: &i32| *x % 2 == 0);
    /// let is_large = Predicate::new(|x: &i32| *x > 100);
    ///
    /// // Combine predicates using Semigroup trait
    /// let is_even_or_large = is_even.combine(&is_large);
    ///
    /// assert!(is_even_or_large.contains(&2));      // Even but not large
    /// assert!(is_even_or_large.contains(&200));    // Both even and large
    /// assert!(is_even_or_large.contains(&101));    // Large but not even
    /// assert!(!is_even_or_large.contains(&51));    // Neither even nor large
    /// ```
    #[inline]
    fn combine(&self, other: &Self) -> Self {
        self.union(other)
    }

    /// Combines two predicates by consuming them, using logical OR operation (union).
    ///
    /// This is the ownership-consuming variant of `combine`. The resulting predicate
    /// will evaluate to `true` for an input if either of the original predicates
    /// would evaluate to `true` for that input.
    ///
    /// # Performance
    ///
    /// - **Time Complexity**: O(1) for creation, O(f1 + f2) for evaluation
    /// - **Memory Usage**: More efficient than `combine` when both predicates are
    ///   no longer needed separately
    /// - **Ownership**: Consumes both predicates rather than cloning references
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::wrapper::predicate::Predicate;
    /// use rustica::traits::semigroup::Semigroup;
    ///
    /// let is_divisible_by_2 = Predicate::new(|x: &i32| *x % 2 == 0);
    /// let is_divisible_by_3 = Predicate::new(|x: &i32| *x % 3 == 0);
    ///
    /// // Consume both predicates to create a new one
    /// let is_divisible_by_2_or_3 = is_divisible_by_2.combine_owned(is_divisible_by_3);
    ///
    /// assert!(is_divisible_by_2_or_3.contains(&6));   // Divisible by both 2 and 3
    /// assert!(is_divisible_by_2_or_3.contains(&4));   // Divisible by 2 only
    /// assert!(is_divisible_by_2_or_3.contains(&9));   // Divisible by 3 only
    /// assert!(!is_divisible_by_2_or_3.contains(&5));  // Divisible by neither
    /// ```
    fn combine_owned(self, other: Self) -> Self {
        Predicate::new({
            let f1 = self.func;
            let f2 = other.func;
            move |a| f1(a) || f2(a)
        })
    }
}

impl<A> HKT for Predicate<A> {
    type Output<B> = Predicate<B>;
    type Source = A;
}

impl<A: 'static> Monoid for Predicate<A> {
    /// Returns the identity element for the `combine` operation: a predicate that always returns `false`.
    ///
    /// This represents the empty set in set theory, which when unioned with any other set,
    /// yields that other set unchanged. Similarly, when this empty predicate is combined with
    /// any other predicate using `combine` (logical OR), the result is equivalent to the other predicate.
    ///
    /// # Performance
    ///
    /// - **Time Complexity**: O(1) for both creation and evaluation
    /// - **Memory Usage**: Minimal, just stores an Rc to a trivial function
    /// - **Evaluation**: Always returns false regardless of input
    ///
    /// # Type Class Laws
    ///
    /// ## Left Identity: `empty().combine(a) = a`
    ///
    /// ```rust
    /// use rustica::datatypes::wrapper::predicate::Predicate;
    /// use rustica::traits::monoid::Monoid;
    /// use rustica::traits::semigroup::Semigroup;
    ///
    /// let is_even = Predicate::new(|x: &i32| *x % 2 == 0);
    /// let test_values = [-10, -5, -2, -1, 0, 1, 2, 5, 10];
    ///
    /// // Verify left identity law
    /// fn verify_left_identity(a: &Predicate<i32>, x: i32) -> bool {
    ///     let empty = Predicate::<i32>::empty();
    ///     empty.combine(a).contains(&x) == a.contains(&x)
    /// }
    ///
    /// // Test with multiple values
    /// for &val in test_values.iter() {
    ///     assert!(verify_left_identity(&is_even, val));
    /// }
    /// ```
    ///
    /// ## Right Identity: `a.combine(empty()) = a`
    ///
    /// ```rust
    /// use rustica::datatypes::wrapper::predicate::Predicate;
    /// use rustica::traits::monoid::Monoid;
    /// use rustica::traits::semigroup::Semigroup;
    ///
    /// let is_positive = Predicate::new(|x: &i32| *x > 0);
    /// let test_values = [-10, -5, -2, -1, 0, 1, 2, 5, 10];
    ///
    /// // Verify right identity law
    /// fn verify_right_identity(a: &Predicate<i32>, x: i32) -> bool {
    ///     let empty = Predicate::<i32>::empty();
    ///     a.combine(&empty).contains(&x) == a.contains(&x)
    /// }
    ///
    /// // Test with multiple values
    /// for &val in test_values.iter() {
    ///     assert!(verify_right_identity(&is_positive, val));
    /// }
    /// ```
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::datatypes::wrapper::predicate::Predicate;
    /// use rustica::traits::monoid::Monoid;
    /// use rustica::traits::semigroup::Semigroup;
    ///
    /// // Create the empty predicate
    /// let empty_pred = Predicate::<i32>::empty();
    ///
    /// // It always returns false
    /// assert!(!empty_pred.contains(&42));
    /// assert!(!empty_pred.contains(&-7));
    /// assert!(!empty_pred.contains(&0));
    ///
    /// // Combining with other predicates
    /// let is_positive = Predicate::new(|x: &i32| *x > 0);
    /// let combined = empty_pred.combine(&is_positive);
    ///
    /// // The result is equivalent to the non-empty predicate
    /// assert!(combined.contains(&5));
    /// assert!(!combined.contains(&-5));
    /// ```
    #[inline]
    fn empty() -> Self {
        Predicate::new(|_| false)
    }
}
