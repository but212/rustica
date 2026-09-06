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
//! let result = Validated::<String, i32>::lift2(|a: i32, b: i32| a + b, v1, v2);
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
//! let result: Option<i32> = Option::<i32>::sequence_right(step1, step2);
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
/// A minimal application example appears in the module documentation; the individual
/// combinators document their own idiomatic usage. Law checks belong in tests rather than
/// in this trait's documentation.
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
    /// let func: Option<fn(&i32) -> i32> = Some(|x: &i32| *x * 2);
    /// let value: Option<i32> = Some(5);
    ///
    fn apply<T, B>(self, value: Self::Output<T>) -> Self::Output<B>
    where
        Self::Source: Fn(T) -> B,
        T: Clone;

    /// Lifts a binary function to work with two applicative values.
    fn lift2<A, B, C, F>(f: F, fa: Self::Output<A>, fb: Self::Output<B>) -> Self::Output<C>
    where
        F: Fn(A, B) -> C,
        A: Clone,
        B: Clone;

    /// Lifts a ternary function to work with three applicative values.
    fn lift3<A, B, C, D, F>(
        f: F, fa: Self::Output<A>, fb: Self::Output<B>, fc: Self::Output<C>,
    ) -> Self::Output<D>
    where
        F: Fn(A, B, C) -> D,
        A: Clone,
        B: Clone,
        C: Clone;

    /// Sequences two applicative actions, discarding the left value and keeping the right.
    #[inline]
    fn sequence_right<A, B>(fa: Self::Output<A>, fb: Self::Output<B>) -> Self::Output<B>
    where
        A: Clone,
        B: Clone,
    {
        Self::lift2(|_, b| b, fa, fb)
    }

    /// Sequences two applicative actions, keeping the left value and discarding the right.
    #[inline]
    fn sequence_left<A, B>(fa: Self::Output<A>, fb: Self::Output<B>) -> Self::Output<A>
    where
        A: Clone,
        B: Clone,
    {
        Self::lift2(|a, _| a, fa, fb)
    }

    /// Deprecated alias for `lift2`.
    #[deprecated(since = "0.15.0", note = "use `lift2()` instead")]
    #[inline]
    fn ap2<A, B, C, F>(f: F, fa: Self::Output<A>, fb: Self::Output<B>) -> Self::Output<C>
    where
        F: Fn(A, B) -> C,
        A: Clone,
        B: Clone,
    {
        Self::lift2(f, fa, fb)
    }
}

// Implementation for Option
impl<A> Applicative for Option<A> {
    #[inline]
    fn apply<T, B>(self, value: Self::Output<T>) -> Self::Output<B>
    where
        Self::Source: Fn(T) -> B,
        T: Clone,
    {
        match (self, value) {
            (Some(func), Some(a)) => Some(func(a)),
            _ => None,
        }
    }

    #[inline]
    fn lift2<T, U, V, F>(f: F, fa: Self::Output<T>, fb: Self::Output<U>) -> Self::Output<V>
    where
        F: Fn(T, U) -> V,
        T: Clone,
        U: Clone,
    {
        match (fa, fb) {
            (Some(a), Some(b)) => Some(f(a, b)),
            _ => None,
        }
    }

    #[inline]
    fn lift3<T, U, V, Q, F>(
        f: F, fa: Self::Output<T>, fb: Self::Output<U>, fc: Self::Output<V>,
    ) -> Self::Output<Q>
    where
        F: Fn(T, U, V) -> Q,
        T: Clone,
        U: Clone,
        V: Clone,
    {
        match (fa, fb, fc) {
            (Some(a), Some(b), Some(c)) => Some(f(a, b, c)),
            _ => None,
        }
    }
}

// Implementation for Result
impl<A, E: std::fmt::Debug + Clone> Applicative for Result<A, E> {
    #[inline]
    fn apply<T, B>(self, value: Self::Output<T>) -> Self::Output<B>
    where
        Self::Source: Fn(T) -> B,
        T: Clone,
    {
        match (self, value) {
            (Ok(func), Ok(a)) => Ok(func(a)),
            (Err(e), _) => Err(e),
            (_, Err(e)) => Err(e),
        }
    }

    #[inline]
    fn lift2<T, U, V, F>(f: F, fa: Self::Output<T>, fb: Self::Output<U>) -> Self::Output<V>
    where
        F: Fn(T, U) -> V,
        T: Clone,
        U: Clone,
    {
        match (fa, fb) {
            (Ok(a), Ok(b)) => Ok(f(a, b)),
            (Err(e), _) => Err(e),
            (_, Err(e)) => Err(e),
        }
    }

    #[inline]
    fn lift3<T, U, V, Q, F>(
        f: F, fa: Self::Output<T>, fb: Self::Output<U>, fc: Self::Output<V>,
    ) -> Self::Output<Q>
    where
        F: Fn(T, U, V) -> Q,
        T: Clone,
        U: Clone,
        V: Clone,
    {
        match (fa, fb, fc) {
            (Ok(a), Ok(b), Ok(c)) => Ok(f(a, b, c)),
            (Err(e), _, _) => Err(e),
            (_, Err(e), _) => Err(e),
            (_, _, Err(e)) => Err(e),
        }
    }
}

// The `Vec` operations share the same Cartesian-product traversal. The
// helpers keep the ownership bookkeeping out of the trait implementation while
// retaining the last-use move optimization for each input.
#[inline]
fn vec_apply<F, T, B>(functions: Vec<F>, values: Vec<T>) -> Vec<B>
where
    F: Fn(T) -> B,
    T: Clone,
{
    let function_count = functions.len();
    let mut result = Vec::with_capacity(function_count.saturating_mul(values.len()));
    let mut functions = functions.into_iter();
    for _ in 0..function_count.saturating_sub(1) {
        let function = functions.next().expect("function count matches iterator");
        result.extend(values.iter().cloned().map(function));
    }
    if let Some(function) = functions.next() {
        result.extend(values.into_iter().map(function));
    }
    result
}

#[inline]
fn vec_lift2<T, U, V, F>(f: F, fa: Vec<T>, fb: Vec<U>) -> Vec<V>
where
    F: Fn(T, U) -> V,
    T: Clone,
    U: Clone,
{
    let fa_len = fa.len();
    let fb_len = fb.len();
    let mut result = Vec::with_capacity(fa_len.saturating_mul(fb_len));
    let mut fa = fa.into_iter();
    for _ in 0..fa_len.saturating_sub(1) {
        let a = fa.next().expect("fa length matches iterator");
        let mut a = Some(a);
        for (bi, b) in fb.iter().enumerate() {
            let a_arg = if bi + 1 == fb_len {
                a.take().expect("last combination consumes a")
            } else {
                a.as_ref().expect("a retained for combinations").clone()
            };
            result.push(f(a_arg, b.clone()));
        }
    }
    if let Some(a) = fa.next() {
        let mut a = Some(a);
        for (bi, b) in fb.into_iter().enumerate() {
            let a_arg = if bi + 1 == fb_len {
                a.take().expect("last combination consumes a")
            } else {
                a.as_ref().expect("a retained for combinations").clone()
            };
            result.push(f(a_arg, b));
        }
    }
    result
}

#[inline]
fn vec_lift3<T, U, V, Q, F>(f: F, fa: Vec<T>, fb: Vec<U>, fc: Vec<V>) -> Vec<Q>
where
    F: Fn(T, U, V) -> Q,
    T: Clone,
    U: Clone,
    V: Clone,
{
    let fa_len = fa.len();
    let fb_len = fb.len();
    let fc_len = fc.len();
    let mut fa = fa.into_iter().map(Some).collect::<Vec<_>>();
    let mut fb = fb.into_iter().map(Some).collect::<Vec<_>>();
    let mut fc = fc.into_iter().map(Some).collect::<Vec<_>>();
    let mut result = Vec::with_capacity(fa_len.saturating_mul(fb_len).saturating_mul(fc_len));

    for (ai, a_slot) in fa.iter_mut().enumerate() {
        for (bi, b_slot) in fb.iter_mut().enumerate() {
            for (ci, c_slot) in fc.iter_mut().enumerate() {
                let a_arg = if bi + 1 == fb_len && ci + 1 == fc_len {
                    a_slot.take().expect("last use of a")
                } else {
                    a_slot.as_ref().expect("a retained").clone()
                };
                let b_arg = if ai + 1 == fa_len && ci + 1 == fc_len {
                    b_slot.take().expect("last use of b")
                } else {
                    b_slot.as_ref().expect("b retained").clone()
                };
                let c_arg = if ai + 1 == fa_len && bi + 1 == fb_len {
                    c_slot.take().expect("last use of c")
                } else {
                    c_slot.as_ref().expect("c retained").clone()
                };
                result.push(f(a_arg, b_arg, c_arg));
            }
        }
    }
    result
}

// Implementation for Vec
impl<A> Applicative for Vec<A> {
    #[inline]
    fn apply<T, B>(self, value: Self::Output<T>) -> Self::Output<B>
    where
        Self::Source: Fn(T) -> B,
        T: Clone,
    {
        vec_apply(self, value)
    }

    #[inline]
    fn lift2<T, U, V, F>(f: F, fa: Self::Output<T>, fb: Self::Output<U>) -> Self::Output<V>
    where
        F: Fn(T, U) -> V,
        T: Clone,
        U: Clone,
    {
        vec_lift2(f, fa, fb)
    }

    #[inline]
    fn lift3<T, U, V, Q, F>(
        f: F, fa: Self::Output<T>, fb: Self::Output<U>, fc: Self::Output<V>,
    ) -> Self::Output<Q>
    where
        F: Fn(T, U, V) -> Q,
        T: Clone,
        U: Clone,
        V: Clone,
    {
        vec_lift3(f, fa, fb, fc)
    }
}

#[cfg(test)]
mod unit_tests {
    use super::Applicative;
    use crate::traits::{functor::Functor, pure::Pure};
    use quickcheck_macros::quickcheck;

    #[quickcheck]
    fn option_applicative_laws(v: Option<i32>, x: i32, has_function: bool) -> bool {
        let f: fn(i32) -> i32 = |n| n.saturating_add(1);
        let id: fn(i32) -> i32 = |n| n;
        let pure_f = Option::<fn(i32) -> i32>::pure(f);
        let pure_x = Option::<i32>::pure(x);
        let functions = if has_function { Some(f) } else { None };
        Applicative::apply(Option::<fn(i32) -> i32>::pure(id), v) == v
            && Applicative::apply(pure_f, pure_x) == Option::<i32>::pure(f(x))
            && Applicative::apply(functions, pure_x)
                == Option::<i32>::lift2(|f, x| f(x), functions, pure_x)
            && v.fmap(f) == Applicative::apply(pure_f, v)
    }

    #[quickcheck]
    fn result_applicative_laws(v: Result<i32, i8>, x: i32, is_ok: bool, err: i8) -> bool {
        let f: fn(i32) -> i32 = |n| n.saturating_add(1);
        let id: fn(i32) -> i32 = |n| n;
        let pure_f = Result::<fn(i32) -> i32, i8>::pure(f);
        let pure_x = Result::<i32, i8>::pure(x);
        let functions = if is_ok { Ok(f) } else { Err(err) };
        Applicative::apply(Result::<fn(i32) -> i32, i8>::pure(id), v) == v
            && Applicative::apply(pure_f, pure_x) == Result::<i32, i8>::pure(f(x))
            && Applicative::apply(functions, pure_x)
                == Result::<i32, i8>::lift2(|f, x| f(x), functions, pure_x)
    }

    #[quickcheck]
    fn vec_applicative_laws(v: Vec<i32>, x: i32) -> bool {
        let f: fn(i32) -> i32 = |n| n.saturating_add(1);
        let id: fn(i32) -> i32 = |n| n;
        Applicative::apply(Vec::<fn(i32) -> i32>::pure(id), v.clone()) == v
            && Applicative::apply(Vec::<fn(i32) -> i32>::pure(f), Vec::<i32>::pure(x))
                == Vec::<i32>::pure(f(x))
    }

    #[quickcheck]
    fn standard_composition_law(w_opt: Option<i32>, w_res: Result<i32, i8>) -> bool {
        let f: fn(i32) -> i32 = |x| x.saturating_add(1);
        let g: fn(i32) -> i32 = |x| x.saturating_mul(2);
        let u_opt = Some(f);
        let v_opt = Some(g);
        let u_res: Result<_, i8> = Ok(f);
        let v_res: Result<_, i8> = Ok(g);
        let left_opt = Option::<i32>::lift3(|f, g, x| f(g(x)), u_opt, v_opt, w_opt);
        let right_opt = Applicative::apply(u_opt, Applicative::apply(v_opt, w_opt));
        let left_res = Result::<i32, i8>::lift3(|f, g, x| f(g(x)), u_res, v_res, w_res);
        let right_res = Applicative::apply(u_res, Applicative::apply(v_res, w_res));
        left_opt == right_opt && left_res == right_res
    }
}
