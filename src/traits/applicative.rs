//! # Applicative Functors
//!
//! Applicative functors are a concept from category theory that provide a way
//! to apply functions inside a functor context. They sit between functors and monads
//! in the hierarchy of abstractions:
//!
//! ```text
//! Functor -> Applicative -> Monad
//! ```
//!
//! An applicative functor extends a regular functor with the ability to:
//! - Lift a value into the functor context (`pure`)
//! - Apply a function in a context to a value in a context (`apply`)
//!
//! ## Mathematical Definition
//!
//! Applicative functors are functors with additional structure:
//! - `pure`: A -> F A
//! - `apply`: F (A -> B) -> F A -> F B
//!
//! ## Laws
//!
//! For a valid Applicative implementation, the following laws must hold:
//!
//! 1. Identity:
//! ```text
//!    pure(id).apply(v) == v
//! ```
//!
//! 2. Homomorphism:
//! ```text
//!    pure(f).apply(pure(x)) == pure(f(x))
//! ```
//!
//! 3. Interchange:
//! ```text
//!    u.apply(pure(y)) == pure(|f| f(y)).apply(u)
//! ```
//!
//! 4. Composition:
//! ```text
//!    pure(compose).apply(u).apply(v).apply(w) == u.apply(v.apply(w))
//! ```
//!
//! ## Practical Use Cases
//!
//! ### 1. Combining Independent Computations
//!
//! Applicative functors excel at combining independent computations that share a context:
//!
//! ```rust
//! use rustica::traits::applicative::Applicative;
//! use rustica::traits::pure::Pure;
//! use rustica::datatypes::validated::Validated;
//!
//! // Two independent validations
//! let v1: Validated<String, i32> = Validated::valid(5);
//! let v2: Validated<String, i32> = Validated::valid(10);
//!
//! // Combine them with a function
//! let result = v1.lift2(&v2, |a, b| a + b);
//! ```
//!
//! ### 2. Sequencing Operations
//!
//! Applicatives allow sequencing operations while preserving the context:
//!
//! ```rust
//! use rustica::traits::applicative::Applicative;
//! use rustica::traits::pure::Pure;
//!
//! // Operations that return Option<T>
//! let step1: Option<i32> = Some(10);
//! let step2: Option<i32> = Some(20);
//!
//! // Keep only the result of step2, but both must succeed
//! let result = step1.sequence_right(&step2);
//! ```
//!
//! ## Relationship to Other Traits
//!
//! - **Functor**: Every Applicative is a Functor. Applicatives can do everything
//!   Functors can, plus more.
//!
//! - **Monad**: Monads are more powerful than Applicatives. Every Monad is an
//!   Applicative, but not every Applicative is a Monad. Applicatives can combine
//!   independent effects, while Monads can sequence dependent effects.
//!
//! ## When to Use Applicative vs Monad
//!
//! - Use **Applicative** when operations are independent of each other and
//!   can be performed in any order, but share a common context.
//!
//! - Use **Monad** when operations depend on the results of previous operations.
//!
use crate::traits::functor::Functor;
use crate::traits::pure::Pure;
use std::marker::PhantomData;

/// A trait for applicative functors, which allow function application within a context.
///
/// Applicative functors extend regular functors by allowing:
/// 1. Lifting of pure values into the context (via `Pure`)
/// 2. Application of functions that are themselves wrapped in the context
/// 3. Sequential application of multiple wrapped values
///
/// ## Examples
///
/// Using applicative to combine validated values:
///
/// ```rust
/// use rustica::traits::applicative::Applicative;
/// use rustica::traits::pure::Pure;
/// use rustica::datatypes::validated::Validated;
///
/// // Validating multiple fields
/// let name: Validated<String, &str> = Validated::valid("John");
/// let age: Validated<String, i32> = Validated::valid(30);
///
/// // Combine them to create a user record
/// let user = name.lift2(&age, |n, a| {
///     format!("User: {}, Age: {}", n, a)
/// });
///
/// assert!(matches!(user, Validated::Valid(_)));
/// ```
pub trait Applicative: Functor + Pure {
    /// Applies a function wrapped in the applicative context to a value.
    ///
    /// This is the core operation of Applicative, allowing us to apply a wrapped 
    /// function to a wrapped value, sequencing operations in a context.
    ///
    /// # Type Parameters
    ///
    /// * `B`: The result type after applying the function
    /// * `F`: The function type that transforms a reference to `Source` into `B`
    ///
    /// # Arguments
    ///
    /// * `f`: A reference to the applicative containing the function
    ///
    /// # Returns
    ///
    /// An applicative containing the result of applying the function to the value
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::traits::applicative::Applicative;
    /// use rustica::traits::pure::Pure;
    ///
    /// let x: Option<i32> = Some(5);
    /// let f: Option<fn(&i32) -> i32> = Some(|a: &i32| a + 1);
    ///
    /// let result = x.apply(&f);
    /// assert_eq!(result, Some(6));
    /// ```
    fn apply<B, F>(&self, f: &Self::Output<F>) -> Self::Output<B>
    where
        F: Fn(&Self::Source) -> B,
        B: Clone;

    /// Lifts a binary function to work with two applicative values.
    ///
    /// This method combines two applicative values using a binary function.
    /// It allows you to apply a function that takes two regular values to two
    /// wrapped values, handling the context automatically.
    ///
    /// # Type Parameters
    ///
    /// * `B`: The type of the second applicative value
    /// * `C`: The result type after applying the function
    /// * `F`: The function type that transforms references to `Source` and `B` into `C`
    ///
    /// # Arguments
    ///
    /// * `b`: A reference to the second applicative value
    /// * `f`: A function to apply to both values
    ///
    /// # Returns
    ///
    /// An applicative containing the result of applying the function to both values
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::traits::applicative::Applicative;
    /// use rustica::traits::pure::Pure;
    ///
    /// let x: Option<i32> = Some(5);
    /// let y: Option<i32> = Some(3);
    ///
    /// let result = x.lift2(&y, |a: &i32, b: &i32| a + b);
    /// assert_eq!(result, Some(8));
    ///
    /// // If any value is None, the result is None
    /// let none_result: Option<i32> = None.lift2(&y, |a: &i32, b: &i32| a + b);
    /// assert_eq!(none_result, None);
    /// ```
    fn lift2<B, C, F>(
        &self,
        b: &Self::Output<B>,
        f: F,
    ) -> Self::Output<C>
    where
        F: Fn(&Self::Source, &B) -> C,
        Self::Source: Clone,
        B: Clone,
        C: Clone;

    /// Lifts a ternary function to work with three applicative values.
    ///
    /// This method combines three applicative values using a ternary function.
    /// It's an extension of `lift2` for functions that take three arguments.
    ///
    /// # Type Parameters
    ///
    /// * `B`: The type of the second applicative value
    /// * `C`: The type of the third applicative value
    /// * `D`: The result type after applying the function
    /// * `F`: The function type that transforms references to `Source`, `B`, and `C` into `D`
    ///
    /// # Arguments
    ///
    /// * `b`: A reference to the second applicative value
    /// * `c`: A reference to the third applicative value
    /// * `f`: A function to apply to all three values
    ///
    /// # Returns
    ///
    /// An applicative containing the result of applying the function to all three values
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::traits::applicative::Applicative;
    /// use rustica::traits::pure::Pure;
    ///
    /// let x: Option<i32> = Some(2);
    /// let y: Option<i32> = Some(3);
    /// let z: Option<i32> = Some(5);
    ///
    /// let result = x.lift3(&y, &z, |a: &i32, b: &i32, c: &i32| a + b + c);
    /// assert_eq!(result, Some(10));
    /// ```
    fn lift3<B, C, D, F>(
        &self,
        b: &Self::Output<B>,
        c: &Self::Output<C>,
        f: F,
    ) -> Self::Output<D>
    where
        F: Fn(&Self::Source, &B, &C) -> D,
        Self::Source: Clone,
        B: Clone,
        C: Clone,
        D: Clone;

    /// Sequences a list of applicative actions, discarding the values.
    ///
    /// This method applies a list of applicative actions in sequence,
    /// keeping only the value of the final action.
    ///
    /// # Type Parameters
    ///
    /// * `B`: The type of the second applicative value
    ///
    /// # Arguments
    ///
    /// * `other`: A reference to the second applicative value
    ///
    /// # Returns
    ///
    /// An applicative containing the value from `other`
    #[inline]
    fn sequence_right<B>(
        &self,
        other: &Self::Output<B>,
    ) -> Self::Output<B>
    where
        Self::Source: Clone,
        B: Clone,
    {
        self.lift2(other, |_, b| b.clone())
    }

    /// Sequences a list of applicative actions, discarding the final value.
    ///
    /// This method applies a list of applicative actions in sequence,
    /// keeping only the value of the first action.
    ///
    /// # Type Parameters
    ///
    /// * `B`: The type of the second applicative value
    ///
    /// # Arguments
    ///
    /// * `other`: A reference to the second applicative value
    ///
    /// # Returns
    ///
    /// An applicative containing the value from `self`
    #[inline]
    fn sequence_left<B>(
        &self,
        other: &Self::Output<B>,
    ) -> Self::Output<Self::Source>
    where
        Self::Source: Clone,
        B: Clone,
    {
        self.lift2(other, |a, _| a.clone())
    }

    /// Applies a binary function to two applicative values.
    ///
    /// This is an alias for `lift2` that may be more intuitive in some contexts.
    ///
    /// # Type Parameters
    ///
    /// * `B`: The type of the second applicative value
    /// * `C`: The result type after applying the function
    /// * `F`: The function type that transforms references to `Source` and `B` into `C`
    ///
    /// # Arguments
    ///
    /// * `b`: A reference to the second applicative value
    /// * `f`: A function to apply to both values
    ///
    /// # Returns
    ///
    /// An applicative containing the result of applying the function to both values
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::traits::applicative::Applicative;
    /// use rustica::traits::pure::Pure;
    /// use rustica::datatypes::validated::Validated;
    ///
    /// let v1: Validated<String, i32> = Validated::valid(5);
    /// let v2: Validated<String, i32> = Validated::valid(3);
    ///
    /// let result = v1.ap2(&v2, |a: &i32, b: &i32| a * b);
    /// assert!(matches!(result, Validated::Valid(15)));
    /// ```
    #[inline]
    fn ap2<B, C, F>(
        &self,
        b: &Self::Output<B>,
        f: F,
    ) -> Self::Output<C>
    where
        F: Fn(&Self::Source, &B) -> C,
        Self::Source: Clone,
        B: Clone,
        C: Clone,
    {
        self.lift2(b, f)
    }

    /// Applies a function to a value, with both wrapped in an applicative context, taking
    /// ownership of both values.
    ///
    /// This is an ownership-based version of `apply` that avoids unnecessary cloning
    /// when the applicative values are no longer needed.
    ///
    /// # Type Parameters
    ///
    /// * `B`: The result type after applying the function
    /// * `F`: The function type that transforms `Source` into `B`
    ///
    /// # Arguments
    ///
    /// * `f`: An applicative containing a function to apply (takes ownership)
    ///
    /// # Returns
    ///
    /// An applicative containing the result of applying the function to the value
    fn apply_owned<B, F>(self, f: Self::Output<F>) -> Self::Output<B>
    where
        F: Fn(Self::Source) -> B,
        Self: Sized,
        B: Clone;

    /// Lifts a binary function to work with two applicative values, taking
    /// ownership of both values.
    ///
    /// This is an ownership-based version of `lift2` that avoids unnecessary cloning
    /// when the applicative values are no longer needed.
    ///
    /// # Type Parameters
    ///
    /// * `B`: The type of the second applicative value
    /// * `C`: The result type after applying the function
    /// * `F`: The function type that transforms `Source` and `B` into `C`
    ///
    /// # Arguments
    ///
    /// * `b`: A second applicative value (takes ownership)
    /// * `f`: A function to apply to both values
    ///
    /// # Returns
    ///
    /// An applicative containing the result of applying the function to both values
    fn lift2_owned<B, C, F>(
        self,
        b: Self::Output<B>,
        f: F,
    ) -> Self::Output<C>
    where
        F: Fn(Self::Source, B) -> C,
        Self: Sized,
        B: Clone,
        C: Clone;

    /// Lifts a ternary function to work with three applicative values, taking
    /// ownership of all values.
    ///
    /// This is an ownership-based version of `lift3` that avoids unnecessary cloning
    /// when the applicative values are no longer needed.
    ///
    /// # Type Parameters
    ///
    /// * `B`: The type of the second applicative value
    /// * `C`: The type of the third applicative value
    /// * `D`: The result type after applying the function
    /// * `F`: The function type that transforms `Source`, `B`, and `C` into `D`
    ///
    /// # Arguments
    ///
    /// * `b`: A second applicative value (takes ownership)
    /// * `c`: A third applicative value (takes ownership)
    /// * `f`: A function to apply to all three values
    ///
    /// # Returns
    ///
    /// An applicative containing the result of applying the function to all three values
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
        D: Clone;

    /// Sequences two applicative actions, keeping only the result of the right one
    /// (discarding the left result).
    ///
    /// This is an ownership-based version of `sequence_right` that avoids unnecessary cloning
    /// when the applicative values are no longer needed.
    ///
    /// # Type Parameters
    ///
    /// * `B`: The type of the second applicative value
    ///
    /// # Arguments
    ///
    /// * `other`: The second applicative value (takes ownership)
    ///
    /// # Returns
    ///
    /// An applicative containing the value from `other`
    #[inline]
    fn sequence_right_owned<B>(
        self,
        other: Self::Output<B>,
    ) -> Self::Output<B>
    where
        Self: Sized,
        B: Clone,
    {
        self.lift2_owned(other, |_, b| b)
    }

    /// Sequences two applicative actions, keeping only the result of the left one
    /// (discarding the right result).
    ///
    /// This is an ownership-based version of `sequence_left` that avoids unnecessary cloning
    /// when the applicative values are no longer needed.
    ///
    /// # Type Parameters
    ///
    /// * `B`: The type of the second applicative value
    ///
    /// # Arguments
    ///
    /// * `other`: The second applicative value (takes ownership)
    ///
    /// # Returns
    ///
    /// An applicative containing the value from `self`
    #[inline]
    fn sequence_left_owned<B>(
        self,
        other: Self::Output<B>,
    ) -> Self::Output<Self::Source>
    where
        Self: Sized,
        B: Clone,
        Self::Source: Clone,
    {
        self.lift2_owned(other, |a, _| a)
    }
}

// Implementation for Option
impl<A> Applicative for Option<A> {
    #[inline]
    fn apply<B, F>(&self, f: &Self::Output<F>) -> Self::Output<B>
    where
        F: Fn(&Self::Source) -> B,
    {
        match (self, f) {
            (Some(a), Some(func)) => Some(func(a)),
            _ => None,
        }
    }

    #[inline]
    fn lift2_owned<B, C, F>(
            self,
            b: Self::Output<B>,
            f: F,
        ) -> Self::Output<C>
        where
            F: FnOnce(Self::Source, B) -> C,
            Self: Sized {
        match (self, b) {
            (Some(a), Some(b)) => Some(f(a, b)),
            _ => None,
        }
    }

    #[inline]
    fn lift2<B, C, F>(
            &self,
            b: &Self::Output<B>,
            f: F,
        ) -> Self::Output<C>
        where
            F: FnOnce(&Self::Source, &B) -> C,
            Self::Source: Clone,
            B: Clone,
            C: Clone {
        match (self, b) {
            (Some(a), Some(b)) => Some(f(a, b)),
            _ => None,
        }
    }

    #[inline]
    fn lift3_owned<B, C, D, F>(
            self,
            b: Self::Output<B>,
            c: Self::Output<C>,
            f: F,
        ) -> Self::Output<D>
        where
            F: FnOnce(Self::Source, B, C) -> D,
            Self: Sized {
        match (self, b, c) {
            (Some(a), Some(b), Some(c)) => Some(f(a, b, c)),
            _ => None,
        }
    }

    #[inline]
    fn lift3<B, C, D, F>(
            &self,
            b: &Self::Output<B>,
            c: &Self::Output<C>,
            f: F,
        ) -> Self::Output<D>
        where
            F: FnOnce(&Self::Source, &B, &C) -> D,
            Self::Source: Clone,
            B: Clone,
            C: Clone,
            D: Clone {
        match (self, b, c) {
            (Some(a), Some(b), Some(c)) => Some(f(a, b, c)),
            _ => None,
        }
    }

    #[inline]
    fn apply_owned<B, F>(self, f: Self::Output<F>) -> Self::Output<B>
        where
            F: FnOnce(Self::Source) -> B,
            Self: Sized,
    {
        match (self, f) {
            (Some(a), Some(func)) => Some(func(a)),
            _ => None,
        }
    }
}

// Implementation for Result
impl<A: Clone, E: std::fmt::Debug + Clone> Applicative for Result<A, E> {
    #[inline]
    fn apply<B, F>(&self, f: &Self::Output<F>) -> Self::Output<B>
    where
        F: Fn(&Self::Source) -> B,
    {
        match (self, f) {
            (Ok(a), Ok(func)) => Ok(func(a)),
            (Err(e), _) => Err(e.clone()),
            (_, Err(e)) => Err(e.clone()),
        }
    }

    #[inline]
    fn lift2<B, C, F>(&self, b: &Self::Output<B>, f: F) -> Self::Output<C>
    where
        F: FnOnce(&Self::Source, &B) -> C,
    {
        match (self, b) {
            (Ok(a), Ok(b_val)) => Ok(f(a, b_val)),
            (Err(e), _) => Err(e.clone()),
            (_, Err(e)) => Err(e.clone()),
        }
    }

    #[inline]
    fn lift3<B, C, D, F>(
        &self,
        b: &Self::Output<B>,
        c: &Self::Output<C>,
        f: F,
    ) -> Self::Output<D>
    where
        F: FnOnce(&Self::Source, &B, &C) -> D,
    {
        match (self, b, c) {
            (Ok(a), Ok(b_val), Ok(c_val)) => Ok(f(a, b_val, c_val)),
            (Err(e), _, _) => Err(e.clone()),
            (_, Err(e), _) => Err(e.clone()),
            (_, _, Err(e)) => Err(e.clone()),
        }
    }

    #[inline]
    fn sequence_right<B>(
        &self,
        other: &Self::Output<B>,
    ) -> Self::Output<B>
    where
        B: Clone,
    {
        match (self, other) {
            (Ok(_), Ok(b)) => Ok(b.clone()),
            (Err(e), _) => Err(e.clone()),
            (_, Err(e)) => Err(e.clone()),
        }
    }

    #[inline]
    fn sequence_left<B>(
        &self,
        other: &Self::Output<B>,
    ) -> Self::Output<Self::Source>
    where
        Self::Source: Clone,
    {
        match (self, other) {
            (Ok(a), Ok(_)) => Ok(a.clone()),
            (Err(e), _) => Err(e.clone()),
            (_, Err(e)) => Err(e.clone()),
        }
    }

    #[inline]
    fn apply_owned<B, F>(self, f: Self::Output<F>) -> Self::Output<B>
    where
        F: FnOnce(Self::Source) -> B,
        Self: Sized,
    {
        match (self, f) {
            (Ok(a), Ok(func)) => Ok(func(a)),
            (Err(e), _) => Err(e),
            (_, Err(e)) => Err(e),
        }
    }

    #[inline]
    fn lift2_owned<B, C, F>(
        self,
        b: Self::Output<B>,
        f: F,
    ) -> Self::Output<C>
    where
        F: FnOnce(Self::Source, B) -> C,
        Self: Sized,
    {
        match (self, b) {
            (Ok(a), Ok(b_val)) => Ok(f(a, b_val)),
            (Err(e), _) => Err(e),
            (_, Err(e)) => Err(e),
        }
    }

    #[inline]
    fn lift3_owned<B, C, D, F>(
        self,
        b: Self::Output<B>,
        c: Self::Output<C>,
        f: F,
    ) -> Self::Output<D>
    where
        F: FnOnce(Self::Source, B, C) -> D,
        Self: Sized,
    {
        match (self, b, c) {
            (Ok(a), Ok(b_val), Ok(c_val)) => Ok(f(a, b_val, c_val)),
            (Err(e), _, _) => Err(e),
            (_, Err(e), _) => Err(e),
            (_, _, Err(e)) => Err(e),
        }
    }

    #[inline]
    fn sequence_right_owned<B>(
        self,
        other: Self::Output<B>,
    ) -> Self::Output<B>
    where
        Self: Sized,
    {
        match (self, other) {
            (Ok(_), Ok(b)) => Ok(b),
            (Err(e), _) => Err(e),
            (_, Err(e)) => Err(e),
        }
    }

    #[inline]
    fn sequence_left_owned<B>(
        self,
        other: Self::Output<B>,
    ) -> Self::Output<Self::Source>
    where
        Self: Sized,
    {
        match (self, other) {
            (Ok(a), Ok(_)) => Ok(a),
            (Err(e), _) => Err(e),
            (_, Err(e)) => Err(e),
        }
    }
}

/// PhantomData implementation of Applicative, does nothing but satisfies trait bounds for Zero-cost abstractions
impl<T> Applicative for PhantomData<T> {
    /// does nothing but satisfies trait bounds
    #[inline]
    fn apply<B, F>(&self, _: &Self::Output<F>) -> Self::Output<B>
        where
            F: Fn(&Self::Source) -> B,
            B: Clone,
    {
        PhantomData
    }

    /// does nothing but satisfies trait bounds
    #[inline]
    fn lift2<B, C, F>(
        &self,
        _: &Self::Output<B>,
        _: F,
    ) -> Self::Output<C>
    where
        F: Fn(&Self::Source, &B) -> C,
        Self::Source: Clone,
        B: Clone,
        C: Clone,
    {
        PhantomData
    }

    /// does nothing but satisfies trait bounds
    #[inline]
    fn lift3<B, C, D, F>(
        &self,
        _: &Self::Output<B>,
        _: &Self::Output<C>,
        _: F,
    ) -> Self::Output<D>
    where
        F: Fn(&Self::Source, &B, &C) -> D,
        Self::Source: Clone,
        B: Clone,
        C: Clone,
        D: Clone,
    {
        PhantomData
    }

    /// does nothing but satisfies trait bounds
    #[inline]
    fn apply_owned<B, F>(self, _: Self::Output<F>) -> Self::Output<B>
    where
        F: Fn(Self::Source) -> B,
        Self: Sized,
        B: Clone,
    {
        PhantomData
    }

    /// does nothing but satisfies trait bounds
    #[inline]
    fn lift2_owned<B, C, F>(
        self,
        _: Self::Output<B>,
        _: F,
    ) -> Self::Output<C>
    where
        F: Fn(Self::Source, B) -> C,
        Self: Sized,
        B: Clone,
        C: Clone,
    {
        PhantomData
    }

    /// does nothing but satisfies trait bounds
    #[inline]
    fn lift3_owned<B, C, D, F>(
        self,
        _: Self::Output<B>,
        _: Self::Output<C>,
        _: F,
    ) -> Self::Output<D>
    where
        F: Fn(Self::Source, B, C) -> D,
        Self: Sized,
        B: Clone,
        C: Clone,
        D: Clone,
    {
        PhantomData
    }
}

// Implementation for Vec
impl<A: Clone> Applicative for Vec<A> {
    #[inline]
    fn apply<B, F>(&self, f: &Self::Output<F>) -> Self::Output<B>
    where
        F: Fn(&Self::Source) -> B,
    {
        let mut result = Vec::with_capacity(self.len() * f.len());
        for func in f {
            for x in self {
                // We need to clone a since we're using it multiple times
                result.push(func(&x));
            }
        }
        result
    }

    #[inline]
    fn lift2<B, C, F>(
        &self,
        b: &Self::Output<B>,
        f: F,
    ) -> Self::Output<C>
    where
        F: Fn(&Self::Source, &B) -> C,
        Self::Source: Clone,
        B: Clone,
        C: Clone,
    {
        let mut result = Vec::with_capacity(self.len() * b.len());
        for a in self {
            for b_val in b {
                // Clone b_val for each use
                result.push(f(&a, &b_val));
            }
        }
        result
    }

    #[inline]
    fn lift3<B, C, D, F>(
        &self,
        b: &Self::Output<B>,
        c: &Self::Output<C>,
        f: F,
    ) -> Self::Output<D>
    where
        F: Fn(&Self::Source, &B, &C) -> D,
        Self::Source: Clone,
        B: Clone,
        C: Clone,
        D: Clone,
    {
        let mut result = Vec::with_capacity(self.len() * b.len() * c.len());
        for a in self {
            for b_val in b {
                for c_val in c {
                    result.push(f(&a, &b_val, &c_val));
                }
            }
        }
        result
    }

    #[inline]
    fn sequence_right<B>(
        &self,
        other: &Self::Output<B>,
    ) -> Self::Output<B>
    where
        Self::Source: Clone,
        B: Clone,
    {
        self.lift2(other, |_, b| b.clone())
    }
    
    #[inline]
    fn sequence_left<B>(
        &self,
        other: &Self::Output<B>,
    ) -> Self::Output<Self::Source>
    where
        Self::Source: Clone,
        B: Clone,
    {
        let mut result = Vec::with_capacity(self.len() * other.len());
        for a in self {
            for _ in other {
                result.push(a.clone());
            }
        }
        result
    }

    // Ownership-based implementations for better performance
    #[inline]
    fn apply_owned<B, F>(self, f: Self::Output<F>) -> Self::Output<B>
    where
        F: Fn(Self::Source) -> B,
        Self: Sized,
    {
        let mut result = Vec::with_capacity(self.len() * f.len());
        for func in f {
            for a in &self {
                // We need to clone a since we're using it multiple times
                result.push(func(a.clone()));
            }
        }
        result
    }

    #[inline]
    fn lift2_owned<B, C, F>(
        self,
        b: Self::Output<B>,
        f: F,
    ) -> Self::Output<C>
    where
        F: Fn(Self::Source, B) -> C,
        Self: Sized,
        B: Clone,
    {
        let mut result = Vec::with_capacity(self.len() * b.len());
        for a in self {
            for b_val in b.clone() {
                result.push(f(a.clone(), b_val));
            }
        }
        result
    }

    #[inline]
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
        let mut result = Vec::with_capacity(self.len() * b.len() * c.len());
        for a in self {
            for b_val in b.clone() {
                for c_val in c.clone() {
                    result.push(f(a.clone(), b_val.clone(), c_val));
                }
            }
        }
        result
    }

    #[inline]
    fn sequence_right_owned<B>(
        self,
        other: Self::Output<B>,
    ) -> Self::Output<B>
    where
        Self: Sized,
        B: Clone,
    {
        let mut result = Vec::with_capacity(self.len() * other.len());
        let other_ref = &other; // Create a reference to avoid moving 'other'
        for _ in self {
            for b in other_ref {
                result.push(b.clone());
            }
        }
        result
    }

    #[inline]
    fn sequence_left_owned<B>(
        self,
        other: Self::Output<B>,
    ) -> Self::Output<Self::Source>
    where
        Self: Sized,
        Self::Source: Clone,
    {
        let mut result = Vec::with_capacity(self.len() * other.len());
        for a in &self {
            for _ in &other {
                result.push(a.clone());
            }
        }
        result
    }
}
