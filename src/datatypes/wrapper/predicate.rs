//! Module: predicate
//!
//! This module provides the `Predicate` type, representing intensional sets as predicate functions.
//!
//! # Overview
//!
//! A `Predicate<A>` wraps a function that determines whether a value of type `A` satisfies a certain condition.
//! Predicates are composable and support logical operations such as AND, OR, NOT, and difference, making them
//! useful for representing and manipulating sets defined by conditions.
//!
//! # Features
//!
//! - Functional, composable representation of sets
//! - Logical operations: union, intersection, difference, and negation
//! - Operator overloading for expressive predicate composition
//! - Implements `Semigroup` and `Monoid` traits for algebraic composition
//!
//! # Examples
//!
//! ```rust
//! use rustica::datatypes::wrapper::predicate::Predicate;
//!
//! // Create basic predicates
//! let is_even = Predicate::new(|x: &i32| *x % 2 == 0);
//! let is_positive = Predicate::new(|x: &i32| *x > 0);
//! let is_large = Predicate::new(|x: &i32| *x > 10);
//!
//! // Combine with operators
//! let even_and_positive = is_even.clone() & is_positive.clone();
//! let positive_or_large = is_positive.clone() | is_large.clone();
//! let not_even = !is_even;
//! let positive_but_not_large = is_positive - is_large;
//!
//! // Test the predicates
//! assert!(even_and_positive.contains(&2));
//! assert!(!even_and_positive.contains(&-2));
//! assert!(positive_or_large.contains(&15));
//! assert!(not_even.contains(&3));
//! assert!(positive_but_not_large.contains(&5));
//! ```
//!
//! # Usage
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
    #[inline]
    fn combine(&self, other: &Self) -> Self {
        self.union(other)
    }

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
    #[inline]
    fn empty() -> Self {
        Predicate::new(|_| false)
    }
}
