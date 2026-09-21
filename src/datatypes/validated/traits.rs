//! Trait implementations for `Validated`.
//!
//! `Validated<T, E>` represents either a `Valid(T)` or an `Invalid(NonEmptyErrors<E>)`.
//! Like `Result<T, E>`, the success value is the first type parameter and the error
//! collection is the second type parameter.

use crate::datatypes::validated::{
    NonEmptyErrors,
    core::{ErrorVec, Validated},
};
use crate::traits::applicative::Applicative;
use crate::traits::foldable::Foldable;
use crate::traits::functor::Functor;
use crate::traits::hkt::HKT;
use crate::traits::pure::Pure;
use crate::traits::semigroup::Semigroup;
#[cfg(any(test, feature = "quickcheck"))]
use quickcheck::{Arbitrary, Gen};

impl<T, E> HKT for Validated<T, E> {
    type Source = T;
    type Output<U> = Validated<U, E>;
}

/// # Examples for `Pure` on `Validated`
///
/// `Pure` provides a way to lift a simple value into the `Validated` context, always resulting
/// in a `Valid` instance.
///
/// ## `pure`
///
/// ```rust
/// use rustica::datatypes::validated::Validated;
/// use rustica::traits::pure::Pure;
///
/// let valid: Validated<i32, &str> = <Validated<i32, &str> as Pure>::pure(10);
/// assert_eq!(valid, Validated::valid(10));
/// ```
impl<T, E> Pure for Validated<T, E> {
    #[inline]
    fn pure<U>(x: U) -> Self::Output<U> {
        Validated::Valid(x)
    }
}

/// # Examples for `Functor` on `Validated`
///
/// ## `fmap`
///
/// Mapping over a `Valid` value:
/// ```rust
/// use rustica::datatypes::validated::Validated;
/// use rustica::traits::functor::Functor;
///
/// let valid: Validated<i32, &str> = Validated::valid(10);
/// let mapped = valid.fmap(|x: i32| x * 2);
/// assert_eq!(mapped, Validated::valid(20));
/// ```
///
/// Mapping over an `Invalid` value:
/// ```rust
/// use rustica::datatypes::validated::Validated;
/// use rustica::traits::functor::Functor;
///
/// let invalid: Validated<i32, &str> = Validated::invalid("error");
/// let mapped = invalid.fmap(|x: i32| x * 2);
/// assert_eq!(mapped, Validated::invalid("error"));
/// ```
impl<T, E> Functor for Validated<T, E> {
    #[inline]
    fn fmap<B, F>(self, mut f: F) -> Self::Output<B>
    where
        F: FnMut(Self::Source) -> B,
    {
        match self {
            Validated::Valid(x) => Validated::Valid(f(x)),
            Validated::Invalid(e) => Validated::Invalid(e),
        }
    }
}

/// # Examples for `Applicative` on `Validated`
///
/// `Validated`'s `Applicative` instance accumulates errors.
///
/// Concretely, this implementation accumulates errors by **concatenating** the two error
/// collections (left-to-right): errors from the function side (`self`) come first, then
/// errors from the value side (`value`).
///
/// ## `apply`
///
/// ### Valid function, Valid value
/// ```rust
/// use rustica::datatypes::validated::Validated;
/// use rustica::traits::applicative::Applicative;
/// use rustica::traits::pure::Pure;
///
/// let valid_fn: Validated<fn(i32) -> i32, &str> = Validated::valid(|x: i32| x * 2);
/// let valid_val: Validated<i32, &str> = Validated::valid(10);
/// assert_eq!(Applicative::apply(valid_fn, valid_val), Validated::valid(20));
/// ```
///
/// ### Invalid function, Valid value
/// ```rust
/// use rustica::datatypes::validated::Validated;
/// use rustica::traits::applicative::Applicative;
/// use rustica::traits::pure::Pure;
///
/// let invalid_fn: Validated<fn(i32) -> i32, &str> = Validated::invalid("fn_error");
/// let valid_val: Validated<i32, &str> = Validated::valid(10);
/// assert_eq!(Applicative::apply(invalid_fn, valid_val), Validated::invalid("fn_error"));
/// ```
///
/// ### Valid function, Invalid value
/// ```rust
/// use rustica::datatypes::validated::Validated;
/// use rustica::traits::applicative::Applicative;
/// use rustica::traits::pure::Pure;
///
/// let valid_fn: Validated<fn(i32) -> i32, &str> = Validated::valid(|x: i32| x * 2);
/// let invalid_val: Validated<i32, &str> = Validated::invalid("val_error");
/// assert_eq!(Applicative::apply(valid_fn, invalid_val), Validated::invalid("val_error"));
/// ```
///
/// ### Invalid function, Invalid value (Error Accumulation)
/// ```rust
/// use rustica::datatypes::validated::Validated;
/// use rustica::traits::applicative::Applicative;
/// use rustica::traits::pure::Pure;
///
/// let invalid_fn: Validated<fn(i32) -> i32, String> = Validated::invalid("fn_error".to_string());
/// let invalid_val: Validated<i32, String> = Validated::invalid("val_error".to_string());
/// let expected_errors = Validated::invalid_many(["fn_error".to_string(), "val_error".to_string()]);
/// assert_eq!(Applicative::apply(invalid_fn, invalid_val), expected_errors);
///
/// // lift2
/// let v1: Validated<i32, &str> = Validated::valid(10);
/// let v2: Validated<i32, &str> = Validated::valid(20);
/// let result = <Validated<i32, &str> as Applicative>::lift2(|a: i32, b: i32| a + b, v1, v2);
/// assert_eq!(result, Validated::valid(30));
/// ```
///
/// Combining `Valid` and `Invalid` (error accumulation):
/// ```rust
/// use rustica::datatypes::validated::Validated;
/// use rustica::traits::applicative::Applicative;
///
/// let v1: Validated<i32, &str> = Validated::valid(10);
/// let v2: Validated<i32, &str> = Validated::invalid("error_b");
/// let result = <Validated<i32, &str> as Applicative>::lift2(|a: i32, b: i32| a + b, v1, v2);
/// assert_eq!(result, Validated::invalid("error_b"));
///
/// let v3: Validated<i32, &str> = Validated::invalid("error_a");
/// let v4: Validated<i32, &str> = Validated::valid(20);
/// let result2 = <Validated<i32, &str> as Applicative>::lift2(|a: i32, b: i32| a + b, v3, v4);
/// assert_eq!(result2, Validated::invalid("error_a"));
///
/// // Combining two `Invalid` values (error accumulation)
/// let v1: Validated<i32, &str> = Validated::invalid("error1");
/// let v2: Validated<i32, &str> = Validated::invalid("error2");
/// let result = <Validated<i32, &str> as Applicative>::lift2(|a: i32, b: i32| a + b, v1, v2);
/// assert_eq!(result, Validated::invalid_many(["error1", "error2"]));
/// ```
impl<T, E> Applicative for Validated<T, E> {
    fn apply<U, B>(self, value: Self::Output<U>) -> Self::Output<B>
    where
        Self::Source: Fn(U) -> B,
        U: Clone,
    {
        match (self, value) {
            (Validated::Valid(f), Validated::Valid(x)) => Validated::Valid(f(x)),
            (a, b) => {
                let mut errors = ErrorVec::new();

                if let Validated::Invalid(e) = a {
                    errors.extend(e);
                }
                if let Validated::Invalid(e) = b {
                    errors.extend(e);
                }

                Validated::Invalid(
                    NonEmptyErrors::try_from_vec(errors).expect("Validated errors cannot be empty"),
                )
            },
        }
    }

    fn lift2<U, V, C, F>(f: F, fa: Self::Output<U>, fb: Self::Output<V>) -> Self::Output<C>
    where
        F: Fn(U, V) -> C,
        U: Clone,
        V: Clone,
    {
        match (fa, fb) {
            (Validated::Valid(a), Validated::Valid(b)) => Validated::Valid(f(a, b)),
            (a, b) => {
                let mut errors = ErrorVec::new();

                if let Validated::Invalid(e) = a {
                    errors.extend(e);
                }
                if let Validated::Invalid(e) = b {
                    errors.extend(e);
                }

                Validated::Invalid(
                    NonEmptyErrors::try_from_vec(errors).expect("Validated errors cannot be empty"),
                )
            },
        }
    }

    fn lift3<U, V, W, C, F>(
        f: F, fa: Self::Output<U>, fb: Self::Output<V>, fc: Self::Output<W>,
    ) -> Self::Output<C>
    where
        F: Fn(U, V, W) -> C,
        U: Clone,
        V: Clone,
        W: Clone,
    {
        match (fa, fb, fc) {
            (Validated::Valid(a), Validated::Valid(b_val), Validated::Valid(c_val)) => {
                Validated::Valid(f(a, b_val, c_val))
            },
            (Validated::Invalid(e1), Validated::Invalid(e2), Validated::Invalid(e3)) => {
                let mut errors = ErrorVec::with_capacity(e1.len() + e2.len() + e3.len());
                errors.extend(e1);
                errors.extend(e2);
                errors.extend(e3);
                Validated::Invalid(
                    NonEmptyErrors::try_from_vec(errors).expect("Validated errors cannot be empty"),
                )
            },
            (a, b, c) => {
                let mut errors = ErrorVec::new();

                if let Validated::Invalid(e) = a {
                    errors.extend(e);
                }
                if let Validated::Invalid(e) = b {
                    errors.extend(e);
                }
                if let Validated::Invalid(e) = c {
                    errors.extend(e);
                }

                Validated::Invalid(
                    NonEmptyErrors::try_from_vec(errors).expect("Validated errors cannot be empty"),
                )
            },
        }
    }
}

/// # Examples for `Foldable` on `Validated`
///
/// ```rust
/// use rustica::datatypes::validated::Validated;
/// use rustica::traits::foldable::Foldable;
///
/// // Folding a Valid value with fold_left
/// let valid = Validated::<i32, &str>::valid(42);
/// let doubled = valid.fold_left(0, |_, x| x * 2);
/// assert_eq!(doubled, 84);
///
/// // Folding an Invalid value with fold_left returns the initial value
/// let invalid = Validated::<i32, &str>::invalid("error");
/// let result = invalid.fold_left(100, |_, x| x + 1);
/// assert_eq!(result, 100);
///
/// // Folding a Valid value with fold_right
/// let valid = Validated::<i32, &str>::valid(42);
/// let doubled = valid.fold_right(0, |x, _| x * 2);
/// assert_eq!(doubled, 84);
///
/// // Folding an Invalid value with fold_right returns the initial value
/// let invalid = Validated::<i32, &str>::invalid("error");
/// let result = invalid.fold_right(100, |x, _| x + 1);
/// assert_eq!(result, 100);
/// ```
impl<T, E> Foldable for Validated<T, E> {
    #[inline]
    fn fold_left<U, F>(&self, init: U, mut f: F) -> U
    where
        F: FnMut(U, &Self::Source) -> U,
    {
        match self {
            Validated::Valid(a) => f(init, a),
            _ => init,
        }
    }

    #[inline]
    fn fold_right<U, F>(&self, init: U, mut f: F) -> U
    where
        F: FnMut(&Self::Source, U) -> U,
    {
        match self {
            Validated::Valid(a) => f(a, init),
            _ => init,
        }
    }
}

/// # Semigroup for `Validated`
///
/// Combines two `Validated` values:
/// - If both are `Valid`, their inner values are combined using `T::combine`.
/// - If one is `Invalid` and one is `Valid`, the `Invalid` is returned (errors take precedence).
/// - If both are `Invalid`, their error collections are concatenated.
impl<T: Semigroup, E> Semigroup for Validated<T, E> {
    fn combine(self, other: Self) -> Self {
        match (self, other) {
            (Validated::Valid(a1), Validated::Valid(a2)) => Validated::Valid(a1.combine(a2)),
            (Validated::Valid(_), o @ Validated::Invalid(_)) => o,
            (s @ Validated::Invalid(_), Validated::Valid(_)) => s,
            (Validated::Invalid(mut e1), Validated::Invalid(e2)) => {
                e1.extend(e2);
                Validated::Invalid(e1)
            },
        }
    }
}

#[cfg(any(test, feature = "quickcheck"))]
impl<T, E> Arbitrary for Validated<T, E>
where
    T: Arbitrary,
    E: Arbitrary,
{
    fn arbitrary(g: &mut Gen) -> Self {
        let x = T::arbitrary(g);
        let y = E::arbitrary(g);
        if bool::arbitrary(g) {
            Validated::valid(x)
        } else {
            Validated::invalid(y)
        }
    }
}
