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
//! let result = Validated::<String, i32>::lift2(|a, b| a + b, &v1, &v2);
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
//! let result: Option<i32> = Option::<i32>::sequence_right(&step1, &step2);
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

/// A trait for applicative functors, which allow function application within a context.
///
/// Applicative functors extend regular functors by providing:
/// 1. Lifting of pure values into the context (via `Pure`)
/// 2. Application of functions that are themselves wrapped in the context (`apply`)
/// 3. Sequential combination of multiple wrapped values (`lift2`, `lift3`)
///
/// ## Mathematical Definition
///
/// Applicative functors are functors with additional structure:
/// - `pure`: A -> F\<A\> (provided by the `Pure` trait)
/// - `apply`: F\<A -> B\> -> F\<A\> -> F\<B\> (the fundamental operation)
///
/// ## Laws
///
/// For a valid Applicative implementation, the following laws must hold:
///
/// ### 1. Identity Law
/// ```text
/// pure(id).apply(v) ≡ v
/// ```
/// Applying the identity function wrapped in the context should be equivalent to the original value.
///
/// ### 2. Homomorphism Law
/// ```text
/// pure(f).apply(pure(x)) ≡ pure(f(x))
/// ```
/// Applying a pure function to a pure value should be equivalent to applying the function directly and then wrapping the result.
///
/// ### 3. Interchange Law
/// ```text
/// u.apply(pure(y)) ≡ pure(|f| f(y)).apply(u)
/// ```
/// The order of evaluation doesn't matter when one operand is pure.
///
/// ### 4. Composition Law
/// ```text
/// pure(compose).apply(u).apply(v).apply(w) ≡ u.apply(v.apply(w))
/// ```
/// Function composition should be associative.
///
/// ## Examples
///
/// ### Basic Usage
/// ```rust
/// use rustica::traits::applicative::Applicative;
/// use rustica::traits::pure::Pure;
///
/// // Apply a function in context to a value in context
/// let func: Option<fn(&i32) -> i32> = Some(|x| x * 2);
/// let value: Option<i32> = Some(5);
/// let result = func.apply(&value);
/// assert_eq!(result, Some(10));
/// ```
///
/// ### Combining Multiple Values
/// ```rust
/// use rustica::traits::applicative::Applicative;
/// use rustica::traits::pure::Pure;
///
/// let x: Option<i32> = Some(2);
/// let y: Option<i32> = Some(3);
/// let z: Option<i32> = Some(4);
///
/// // Function-first style (mathematical convention)
/// let result = Option::<i32>::lift2(|a, b| a + b, &x, &y);
/// assert_eq!(result, Some(5));
///
/// let result3 = Option::<i32>::lift3(|a, b, c| a + b + c, &x, &y, &z);
/// assert_eq!(result3, Some(9));
/// ```
///
/// ### Validation Example
/// ```rust
/// use rustica::traits::applicative::Applicative;
/// use rustica::traits::pure::Pure;
/// use rustica::datatypes::validated::Validated;
///
/// let name: Validated<String, &str> = Validated::valid("John");
/// let age: Validated<String, i32> = Validated::valid(30);
///
/// // Combine validations - all must succeed
/// let user = Validated::<String, String>::lift2(
///     |n: &&str, a: &i32| format!("User: {}, Age: {}", n, a),
///     &name,
///     &age
/// );
/// assert!(matches!(user, Validated::Valid(_)));
/// ```
pub trait Applicative: Functor + Pure {
    /// Applies a function wrapped in the applicative context to a value.
    ///
    /// This is the fundamental operation of Applicative functors, with signature:
    /// `F\<A -> B\> -> F\<A\> -> F\<B\>`
    ///
    /// The function is contained within `self` (the applicative context), and is applied
    /// to the value contained within the `value` parameter.
    ///
    /// # Type Parameters
    ///
    /// * `T`: The input type of the value being transformed
    /// * `B`: The result type after applying the function
    ///
    /// # Arguments
    ///
    /// * `value`: A reference to the applicative containing the value to transform
    ///
    /// # Returns
    ///
    /// An applicative containing the result of applying the function to the value
    ///
    /// # Laws
    ///
    /// This method must satisfy the applicative laws:
    /// - Identity: `pure(id).apply(v) ≡ v`
    /// - Homomorphism: `pure(f).apply(pure(x)) ≡ pure(f(x))`
    /// - Interchange: `u.apply(pure(y)) ≡ pure(|f| f(y)).apply(u)`
    /// - Composition: `pure(compose).apply(u).apply(v).apply(w) ≡ u.apply(v.apply(w))`
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::traits::applicative::Applicative;
    /// use rustica::traits::pure::Pure;
    ///
    /// // Function wrapped in Option
    /// let func: Option<fn(&i32) -> i32> = Some(|x| x * 2);
    /// let value: Option<i32> = Some(5);
    ///
    /// let result = func.apply(&value);
    /// assert_eq!(result, Some(10));
    ///
    /// // If either is None, result is None
    /// let none_func: Option<fn(&i32) -> i32> = None;
    /// let result2 = none_func.apply(&value);
    /// assert_eq!(result2, None);
    /// ```
    fn apply<T, B>(&self, value: &Self::Output<T>) -> Self::Output<B>
    where
        Self::Source: Fn(&T) -> B,
        B: Clone;

    /// Lifts a binary function to work with two applicative values.
    ///
    /// This method follows the mathematical convention where the function comes first,
    /// matching the curried style used in functional programming languages like Haskell.
    /// It combines two applicative values using a binary function.
    ///
    /// # Type Parameters
    ///
    /// * `A`: The type of the first applicative value
    /// * `B`: The type of the second applicative value  
    /// * `C`: The result type after applying the function
    /// * `F`: The function type that transforms references to `A` and `B` into `C`
    ///
    /// # Arguments
    ///
    /// * `f`: A function to apply to both values (function-first, curried style)
    /// * `fa`: A reference to the first applicative value
    /// * `fb`: A reference to the second applicative value
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
    /// // Function-first style (mathematical convention)
    /// let result: Option<i32> = Option::<i32>::lift2(|a: &i32, b: &i32| a + b, &x, &y);
    /// assert_eq!(result, Some(8));
    ///
    /// // If any value is None, the result is None
    /// let none_x: Option<i32> = None;
    /// let result2: Option<i32> = Option::<i32>::lift2(|a: &i32, b: &i32| a + b, &none_x, &y);
    /// assert_eq!(result2, None);
    /// ```
    fn lift2<A, B, C, F>(f: F, fa: &Self::Output<A>, fb: &Self::Output<B>) -> Self::Output<C>
    where
        F: Fn(&A, &B) -> C,
        A: Clone,
        B: Clone,
        C: Clone;

    /// Lifts a ternary function to work with three applicative values.
    ///
    /// This method follows the mathematical convention where the function comes first,
    /// matching the curried style used in functional programming languages like Haskell.
    /// It combines three applicative values using a ternary function.
    ///
    /// # Type Parameters
    ///
    /// * `A`: The type of the first applicative value
    /// * `B`: The type of the second applicative value
    /// * `C`: The type of the third applicative value
    /// * `D`: The result type after applying the function
    /// * `F`: The function type that transforms references to `A`, `B`, and `C` into `D`
    ///
    /// # Arguments
    ///
    /// * `f`: A function to apply to all three values (function-first, curried style)
    /// * `fa`: A reference to the first applicative value
    /// * `fb`: A reference to the second applicative value
    /// * `fc`: A reference to the third applicative value
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
    /// // Function-first style (mathematical convention)
    /// let result: Option<i32> = Option::<i32>::lift3(
    ///     |a: &i32, b: &i32, c: &i32| a + b + c,
    ///     &x, &y, &z
    /// );
    /// assert_eq!(result, Some(10));
    /// ```
    fn lift3<A, B, C, D, F>(
        f: F, fa: &Self::Output<A>, fb: &Self::Output<B>, fc: &Self::Output<C>,
    ) -> Self::Output<D>
    where
        F: Fn(&A, &B, &C) -> D,
        A: Clone,
        B: Clone,
        C: Clone,
        D: Clone;

    /// Sequences two applicative actions, discarding the left value and keeping the right.
    ///
    /// This method applies two applicative actions in sequence, discarding the result
    /// of the first action and keeping only the result of the second action.
    /// Equivalent to `*>` in Haskell.
    ///
    /// # Type Parameters
    ///
    /// * `A`: The type of the first applicative value
    /// * `B`: The type of the second applicative value
    ///
    /// # Arguments
    ///
    /// * `fa`: A reference to the first applicative value
    /// * `fb`: A reference to the second applicative value
    ///
    /// # Returns
    ///
    /// An applicative containing the value from `fb`
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::traits::applicative::Applicative;
    ///
    /// let x: Option<i32> = Some(1);
    /// let y: Option<i32> = Some(2);
    ///
    /// let result: Option<i32> = Option::<i32>::sequence_right(&x, &y);
    /// assert_eq!(result, Some(2));
    ///
    /// // If either fails, the whole operation fails
    /// let none_x: Option<i32> = None;
    /// let result2: Option<i32> = Option::<i32>::sequence_right(&none_x, &y);
    /// assert_eq!(result2, None);
    /// ```
    #[inline]
    fn sequence_right<A, B>(fa: &Self::Output<A>, fb: &Self::Output<B>) -> Self::Output<B>
    where
        A: Clone,
        B: Clone,
    {
        Self::lift2(|_, b| b.clone(), fa, fb)
    }

    /// Sequences two applicative actions, keeping the left value and discarding the right.
    ///
    /// This method applies two applicative actions in sequence, keeping the result
    /// of the first action and discarding the result of the second action.
    /// Equivalent to `<*` in Haskell.
    ///
    /// # Type Parameters
    ///
    /// * `A`: The type of the first applicative value
    /// * `B`: The type of the second applicative value
    ///
    /// # Arguments
    ///
    /// * `fa`: A reference to the first applicative value
    /// * `fb`: A reference to the second applicative value
    ///
    /// # Returns
    ///
    /// An applicative containing the value from `fa`
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::traits::applicative::Applicative;
    ///
    /// let x: Option<i32> = Some(1);
    /// let y: Option<i32> = Some(2);
    ///
    /// let result: Option<i32> = Option::<i32>::sequence_left(&x, &y);
    /// assert_eq!(result, Some(1));
    ///
    /// // If either fails, the whole operation fails
    /// let none_y: Option<i32> = None;
    /// let result2: Option<i32> = Option::<i32>::sequence_left(&x, &none_y);
    /// assert_eq!(result2, None);
    /// ```
    #[inline]
    fn sequence_left<A, B>(fa: &Self::Output<A>, fb: &Self::Output<B>) -> Self::Output<A>
    where
        A: Clone,
        B: Clone,
    {
        Self::lift2(|a, _| a.clone(), fa, fb)
    }

    /// Applies a binary function to two applicative values.
    ///
    /// This is an alias for `lift2` that may be more intuitive in some contexts.
    /// It follows the same function-first convention as `lift2`.
    ///
    /// # Type Parameters
    ///
    /// * `A`: The type of the first applicative value
    /// * `B`: The type of the second applicative value
    /// * `C`: The result type after applying the function
    /// * `F`: The function type that transforms references to `A` and `B` into `C`
    ///
    /// # Arguments
    ///
    /// * `f`: A function to apply to both values (function-first style)
    /// * `fa`: A reference to the first applicative value
    /// * `fb`: A reference to the second applicative value
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
    /// let result: Validated<String, i32> = Validated::<String, i32>::ap2(|a: &i32, b: &i32| a * b, &v1, &v2);
    /// assert!(matches!(result, Validated::Valid(15)));
    /// ```
    #[inline]
    fn ap2<A, B, C, F>(f: F, fa: &Self::Output<A>, fb: &Self::Output<B>) -> Self::Output<C>
    where
        F: Fn(&A, &B) -> C,
        A: Clone,
        B: Clone,
        C: Clone,
    {
        Self::lift2(f, fa, fb)
    }

    /// Applies a function to a value, with both wrapped in an applicative context, taking
    /// ownership of both values.
    ///
    /// This is an ownership-based version of `apply` that avoids unnecessary cloning
    /// when the applicative values are no longer needed. The signature matches the
    /// mathematical definition: F\<A -> B\> -> F\<A\> -> F\<B\>.
    ///
    /// # Type Parameters
    ///
    /// * `T`: The input type of the value being transformed
    /// * `B`: The result type after applying the function
    ///
    /// # Arguments
    ///
    /// * `value`: An applicative containing the value to transform (takes ownership)
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
    /// let func: Option<fn(i32) -> i32> = Some(|x| x * 2);
    /// let value: Option<i32> = Some(5);
    ///
    /// let result = func.apply_owned(value);
    /// assert_eq!(result, Some(10));
    /// ```
    fn apply_owned<T, B>(self, value: Self::Output<T>) -> Self::Output<B>
    where
        Self::Source: Fn(T) -> B,
        T: Clone,
        B: Clone;

    /// Lifts a binary function to work with two applicative values, taking
    /// ownership of both values.
    ///
    /// This is an ownership-based version of `lift2` that avoids unnecessary cloning
    /// when the applicative values are no longer needed. It follows the same
    /// function-first convention as `lift2`.
    ///
    /// # Type Parameters
    ///
    /// * `A`: The type of the first applicative value
    /// * `B`: The type of the second applicative value
    /// * `C`: The result type after applying the function
    /// * `F`: The function type that transforms `A` and `B` into `C`
    ///
    /// # Arguments
    ///
    /// * `f`: A function to apply to both values (function-first style)
    /// * `fa`: First applicative value (takes ownership)
    /// * `fb`: Second applicative value (takes ownership)
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
    /// let result: Option<i32> = Option::<i32>::lift2_owned(|a, b| a + b, x, y);
    /// assert_eq!(result, Some(8));
    /// ```
    fn lift2_owned<A, B, C, F>(f: F, fa: Self::Output<A>, fb: Self::Output<B>) -> Self::Output<C>
    where
        F: Fn(A, B) -> C,
        A: Clone,
        B: Clone,
        C: Clone;

    /// Lifts a ternary function to work with three applicative values, taking
    /// ownership of all values.
    ///
    /// This is an ownership-based version of `lift3` that avoids unnecessary cloning
    /// when the applicative values are no longer needed. It follows the same
    /// function-first convention as `lift3`.
    ///
    /// # Type Parameters
    ///
    /// * `A`: The type of the first applicative value
    /// * `B`: The type of the second applicative value
    /// * `C`: The type of the third applicative value
    /// * `D`: The result type after applying the function
    /// * `F`: The function type that transforms `A`, `B`, and `C` into `D`
    ///
    /// # Arguments
    ///
    /// * `f`: A function to apply to all three values (function-first style)
    /// * `fa`: First applicative value (takes ownership)
    /// * `fb`: Second applicative value (takes ownership)
    /// * `fc`: Third applicative value (takes ownership)
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
    /// let z: Option<i32> = Some(4);
    ///
    /// let result: Option<i32> = Option::<i32>::lift3_owned(|a, b, c| a + b + c, x, y, z);
    /// assert_eq!(result, Some(9));
    /// ```
    fn lift3_owned<A, B, C, D, F>(
        f: F, fa: Self::Output<A>, fb: Self::Output<B>, fc: Self::Output<C>,
    ) -> Self::Output<D>
    where
        F: Fn(A, B, C) -> D,
        A: Clone,
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
    /// * `A`: The type of the first applicative value
    /// * `B`: The type of the second applicative value
    ///
    /// # Arguments
    ///
    /// * `fa`: The first applicative value (takes ownership)
    /// * `fb`: The second applicative value (takes ownership)
    ///
    /// # Returns
    ///
    /// An applicative containing the value from `fb`
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::traits::applicative::Applicative;
    ///
    /// let x: Option<i32> = Some(1);
    /// let y: Option<i32> = Some(2);
    ///
    /// let result: Option<i32> = Option::<i32>::sequence_right_owned(x, y);
    /// assert_eq!(result, Some(2));
    /// ```
    #[inline]
    fn sequence_right_owned<A, B>(fa: Self::Output<A>, fb: Self::Output<B>) -> Self::Output<B>
    where
        A: Clone,
        B: Clone,
    {
        Self::lift2_owned(|_, b| b, fa, fb)
    }

    /// Sequences two applicative actions, keeping only the result of the left one
    /// (discarding the right result).
    ///
    /// This is an ownership-based version of `sequence_left` that avoids unnecessary cloning
    /// when the applicative values are no longer needed.
    ///
    /// # Type Parameters
    ///
    /// * `A`: The type of the first applicative value
    /// * `B`: The type of the second applicative value
    ///
    /// # Arguments
    ///
    /// * `fa`: The first applicative value (takes ownership)
    /// * `fb`: The second applicative value (takes ownership)
    ///
    /// # Returns
    ///
    /// An applicative containing the value from `fa`
    ///
    /// # Examples
    ///
    /// ```rust
    /// use rustica::traits::applicative::Applicative;
    ///
    /// let x: Option<i32> = Some(1);
    /// let y: Option<i32> = Some(2);
    ///
    /// let result: Option<i32> = Option::<i32>::sequence_left_owned(x, y);
    /// assert_eq!(result, Some(1));
    /// ```
    #[inline]
    fn sequence_left_owned<A, B>(fa: Self::Output<A>, fb: Self::Output<B>) -> Self::Output<A>
    where
        A: Clone,
        B: Clone,
        Self: Sized,
    {
        Self::lift2_owned(|a, _| a, fa, fb)
    }
}

// Implementation for Option
impl<A> Applicative for Option<A> {
    #[inline]
    fn apply<T, B>(&self, value: &Self::Output<T>) -> Self::Output<B>
    where
        Self::Source: Fn(&T) -> B,
        B: Clone,
    {
        match (self, value) {
            (Some(func), Some(a)) => Some(func(a)),
            _ => None,
        }
    }

    #[inline]
    fn lift2<T, U, V, F>(f: F, fa: &Self::Output<T>, fb: &Self::Output<U>) -> Self::Output<V>
    where
        F: Fn(&T, &U) -> V,
        T: Clone,
        U: Clone,
        V: Clone,
        Self: Sized,
    {
        match (fa, fb) {
            (Some(a), Some(b)) => Some(f(a, b)),
            _ => None,
        }
    }

    #[inline]
    fn lift3<T, U, V, Q, F>(
        f: F, fa: &Self::Output<T>, fb: &Self::Output<U>, fc: &Self::Output<V>,
    ) -> Self::Output<Q>
    where
        F: Fn(&T, &U, &V) -> Q,
        T: Clone,
        U: Clone,
        V: Clone,
        Q: Clone,
        Self: Sized,
    {
        match (fa, fb, fc) {
            (Some(a), Some(b), Some(c)) => Some(f(a, b, c)),
            _ => None,
        }
    }

    #[inline]
    fn apply_owned<T, B>(self, value: Self::Output<T>) -> Self::Output<B>
    where
        Self::Source: Fn(T) -> B,
        T: Clone,
        B: Clone,
    {
        match (self, value) {
            (Some(func), Some(a)) => Some(func(a)),
            _ => None,
        }
    }

    #[inline]
    fn lift2_owned<T, U, V, F>(f: F, fa: Self::Output<T>, fb: Self::Output<U>) -> Self::Output<V>
    where
        F: Fn(T, U) -> V,
        T: Clone,
        U: Clone,
        V: Clone,
        Self: Sized,
    {
        match (fa, fb) {
            (Some(a), Some(b)) => Some(f(a, b)),
            _ => None,
        }
    }

    #[inline]
    fn lift3_owned<T, U, V, Q, F>(
        f: F, fa: Self::Output<T>, fb: Self::Output<U>, fc: Self::Output<V>,
    ) -> Self::Output<Q>
    where
        F: Fn(T, U, V) -> Q,
        T: Clone,
        U: Clone,
        V: Clone,
        Q: Clone,
        Self: Sized,
    {
        match (fa, fb, fc) {
            (Some(a), Some(b), Some(c)) => Some(f(a, b, c)),
            _ => None,
        }
    }
}

// Implementation for Result
impl<A: Clone, E: std::fmt::Debug + Clone> Applicative for Result<A, E> {
    #[inline]
    fn apply<T, B>(&self, value: &Self::Output<T>) -> Self::Output<B>
    where
        Self::Source: Fn(&T) -> B,
        B: Clone,
    {
        match (self, value) {
            (Ok(func), Ok(a)) => Ok(func(a)),
            (Err(e), _) => Err(e.clone()),
            (_, Err(e)) => Err(e.clone()),
        }
    }

    #[inline]
    fn lift2<T, U, V, F>(f: F, fa: &Self::Output<T>, fb: &Self::Output<U>) -> Self::Output<V>
    where
        F: Fn(&T, &U) -> V,
        T: Clone,
        U: Clone,
        V: Clone,
        Self: Sized,
    {
        match (fa, fb) {
            (Ok(a), Ok(b)) => Ok(f(a, b)),
            (Err(e), _) => Err(e.clone()),
            (_, Err(e)) => Err(e.clone()),
        }
    }

    #[inline]
    fn lift3<T, U, V, Q, F>(
        f: F, fa: &Self::Output<T>, fb: &Self::Output<U>, fc: &Self::Output<V>,
    ) -> Self::Output<Q>
    where
        F: Fn(&T, &U, &V) -> Q,
        T: Clone,
        U: Clone,
        V: Clone,
        Q: Clone,
        Self: Sized,
    {
        match (fa, fb, fc) {
            (Ok(a), Ok(b), Ok(c)) => Ok(f(a, b, c)),
            (Err(e), _, _) => Err(e.clone()),
            (_, Err(e), _) => Err(e.clone()),
            (_, _, Err(e)) => Err(e.clone()),
        }
    }

    #[inline]
    fn apply_owned<T, B>(self, value: Self::Output<T>) -> Self::Output<B>
    where
        Self::Source: Fn(T) -> B,
        T: Clone,
        B: Clone,
    {
        match (self, value) {
            (Ok(func), Ok(a)) => Ok(func(a)),
            (Err(e), _) => Err(e),
            (_, Err(e)) => Err(e),
        }
    }

    #[inline]
    fn lift2_owned<T, U, V, F>(f: F, fa: Self::Output<T>, fb: Self::Output<U>) -> Self::Output<V>
    where
        F: Fn(T, U) -> V,
        T: Clone,
        U: Clone,
        V: Clone,
        Self: Sized,
    {
        match (fa, fb) {
            (Ok(a), Ok(b)) => Ok(f(a, b)),
            (Err(e), _) => Err(e),
            (_, Err(e)) => Err(e),
        }
    }

    #[inline]
    fn lift3_owned<T, U, V, Q, F>(
        f: F, fa: Self::Output<T>, fb: Self::Output<U>, fc: Self::Output<V>,
    ) -> Self::Output<Q>
    where
        F: Fn(T, U, V) -> Q,
        T: Clone,
        U: Clone,
        V: Clone,
        Q: Clone,
        Self: Sized,
    {
        match (fa, fb, fc) {
            (Ok(a), Ok(b), Ok(c)) => Ok(f(a, b, c)),
            (Err(e), _, _) => Err(e),
            (_, Err(e), _) => Err(e),
            (_, _, Err(e)) => Err(e),
        }
    }
}

// Implementation for Vec
impl<A: Clone> Applicative for Vec<A> {
    #[inline]
    fn apply<T, B>(&self, value: &Self::Output<T>) -> Self::Output<B>
    where
        Self::Source: Fn(&T) -> B,
        B: Clone,
    {
        let mut result = Vec::new();
        for func in self {
            for val in value {
                result.push(func(val));
            }
        }
        result
    }

    #[inline]
    fn lift2<T, U, V, F>(f: F, fa: &Self::Output<T>, fb: &Self::Output<U>) -> Self::Output<V>
    where
        F: Fn(&T, &U) -> V,
        T: Clone,
        U: Clone,
        V: Clone,
        Self: Sized,
    {
        let mut result = Vec::with_capacity(fa.len() * fb.len());
        for a in fa {
            for b in fb {
                result.push(f(a, b));
            }
        }
        result
    }

    #[inline]
    fn lift3<T, U, V, Q, F>(
        f: F, fa: &Self::Output<T>, fb: &Self::Output<U>, fc: &Self::Output<V>,
    ) -> Self::Output<Q>
    where
        F: Fn(&T, &U, &V) -> Q,
        T: Clone,
        U: Clone,
        V: Clone,
        Q: Clone,
        Self: Sized,
    {
        let mut result = Vec::with_capacity(fa.len() * fb.len() * fc.len());
        for a in fa {
            for b in fb {
                for c in fc {
                    result.push(f(a, b, c));
                }
            }
        }
        result
    }

    // Ownership-based implementations for better performance
    #[inline]
    fn apply_owned<T, B>(self, value: Self::Output<T>) -> Self::Output<B>
    where
        Self::Source: Fn(T) -> B,
        T: Clone,
        B: Clone,
    {
        let mut result = Vec::new();
        for func in self {
            for val in value.clone() {
                result.push(func(val));
            }
        }
        result
    }

    #[inline]
    fn lift2_owned<T, U, V, F>(f: F, fa: Self::Output<T>, fb: Self::Output<U>) -> Self::Output<V>
    where
        F: Fn(T, U) -> V,
        T: Clone,
        U: Clone,
        V: Clone,
        Self: Sized,
    {
        let mut result = Vec::with_capacity(fa.len() * fb.len());
        for a in fa {
            for b in fb.clone() {
                result.push(f(a.clone(), b));
            }
        }
        result
    }

    #[inline]
    fn lift3_owned<T, U, V, Q, F>(
        f: F, fa: Self::Output<T>, fb: Self::Output<U>, fc: Self::Output<V>,
    ) -> Self::Output<Q>
    where
        F: Fn(T, U, V) -> Q,
        T: Clone,
        U: Clone,
        V: Clone,
        Q: Clone,
        Self: Sized,
    {
        let mut result = Vec::with_capacity(fa.len() * fb.len() * fc.len());
        for a in fa {
            for b in fb.clone() {
                for c in fc.clone() {
                    result.push(f(a.clone(), b.clone(), c));
                }
            }
        }
        result
    }
}
