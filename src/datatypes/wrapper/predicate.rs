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
//! # Example
//!
//! ```rust
//! use rustica::datatypes::wrapper::predicate::Predicate;
//!
//! let is_even = Predicate::new(|x: &i32| *x % 2 == 0);
//! let is_positive = Predicate::new(|x: &i32| *x > 0);
//! let even_and_positive = is_even & is_positive;
//! assert!(even_and_positive.contains(&2));
//! assert!(!even_and_positive.contains(&-2));
//! ```
//!
//! # Usage
//!
//! This module is ideal for use cases where sets are defined by properties or conditions rather than explicit enumeration.

use std::rc::Rc;
use std::ops::{BitOr, BitAnd, Sub, Not};
use crate::traits::semigroup::Semigroup;
use crate::traits::monoid::Monoid;
use crate::traits::hkt::HKT;

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
    #[inline]
    pub fn new<F>(f: F) -> Self
    where
        F: Fn(&A) -> bool + 'static,
    {
        Predicate { func: Rc::new(f) }
    }

    /// Returns true if the value satisfies the predicate.
    #[inline]
    pub fn contains(&self, a: &A) -> bool {
        (self.func)(a)
    }

    /// Returns a predicate which is the union of this predicate and another.
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

    /// Returns the predicate which is the difference of another predicate removed from this predicate.
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

    /// Return the opposite predicate.
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