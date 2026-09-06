//! Trait implementations for `Validated`.
//!
//! `Validated<E, A>` represents either a `Valid(A)` or an `Invalid(NonEmptyErrors<E>)`.
//! In other words, an invalid value carries a *collection* of errors (often used to
//! accumulate multiple validation failures).

use crate::datatypes::validated::{
    NonEmptyErrors,
    core::{ErrorAccumulator, Validated},
};
use crate::traits::applicative::Applicative;
use crate::traits::bifunctor::Bifunctor;
use crate::traits::foldable::Foldable;
use crate::traits::functor::Functor;
use crate::traits::hkt::{BinaryHKT, HKT};
use crate::traits::monad::Monad;
use crate::traits::pure::Pure;
use crate::traits::semigroup::Semigroup;
#[cfg(any(test, feature = "quickcheck"))]
use quickcheck::{Arbitrary, Gen};

impl<E, A> HKT for Validated<E, A> {
    type Source = A;
    type Output<T> = Validated<E, T>;
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
/// let valid: Validated<&str, i32> = <Validated<&str, i32> as Pure>::pure(10);
/// assert_eq!(valid, Validated::valid(10));
/// ```
impl<E, A> Pure for Validated<E, A> {
    #[inline]
    fn pure<T>(x: T) -> Self::Output<T> {
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
/// let valid: Validated<&str, i32> = Validated::valid(10);
/// let mapped = valid.fmap(|x: i32| x * 2);
/// assert_eq!(mapped, Validated::valid(20));
/// ```
///
/// Mapping over an `Invalid` value:
/// ```rust
/// use rustica::datatypes::validated::Validated;
/// use rustica::traits::functor::Functor;
///
/// let invalid: Validated<&str, i32> = Validated::invalid("error");
/// let mapped = invalid.fmap(|x: i32| x * 2);
/// assert_eq!(mapped, Validated::invalid("error"));
/// ```
///
/// The functor identity and composition laws are verified by unit tests.
impl<E, A> Functor for Validated<E, A> {
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

impl<E, A> BinaryHKT for Validated<E, A> {
    type Source2 = E;
    type BinaryOutput<U, V> = Validated<V, U>;
}

/// # Examples for `Bifunctor` on `Validated`
///
/// `Validated<E, A>` is a two-parameter type, but its `Invalid` case stores a *collection*
/// of errors (`NonEmptyErrors<E>`), not a single `E`.
///
/// In Rustica's `BinaryHKT` encoding for `Validated<E, A>`:
///
/// - `Source` is the valid value type `A` (so `first` maps the `Valid` value)
/// - `Source2` is the error element type `E` (so `second` maps *each* error)
///
/// `bimap(f, g)` therefore means:
///
/// - Apply `f` to the `Valid(A)` value
/// - Apply `g` to each error element inside `Invalid(errors)`
///
/// ## `bimap`
///
/// ### Mapping over a `Valid` value (applies `f`)
/// ```rust
/// use rustica::datatypes::validated::Validated;
/// use rustica::traits::bifunctor::Bifunctor;
///
/// let valid: Validated<&str, i32> = Validated::valid(10);
/// // `f` is applied to the `Valid` value.
/// let result = valid.bimap(|v: i32| v * 2, |e: &str| format!("Error: {}", e));
/// assert_eq!(result, Validated::valid(20));
/// ```
///
/// ### Mapping over an `Invalid` value (applies `g` to each error)
/// ```rust
/// use rustica::datatypes::validated::Validated;
/// use rustica::traits::bifunctor::Bifunctor;
///
/// let invalid: Validated<&str, i32> = Validated::invalid_many(vec!["e1", "e2"]);
/// // `g` is applied to each error element inside `Invalid(errors)`.
/// let result = invalid.bimap(|v: i32| v * 2, |e: &str| format!("New-{}", e));
/// assert_eq!(result, Validated::invalid_many(vec!["New-e1".to_string(), "New-e2".to_string()]));
/// ```
impl<E, A> Bifunctor for Validated<E, A> {
    fn bimap<C, D, F, G>(self, mut f: F, g: G) -> Self::BinaryOutput<C, D>
    where
        F: FnMut(Self::Source) -> C,
        G: FnMut(Self::Source2) -> D,
    {
        match self {
            Validated::Valid(x) => Validated::Valid(f(x)),
            Validated::Invalid(es) => {
                let mut transformed = es.into_iter().map(g);
                let first = transformed.next().expect("invalid values have errors");
                Validated::Invalid(NonEmptyErrors::from_first_and_iter(first, transformed))
            },
        }
    }

    fn first<C, F>(self, mut f: F) -> Self::BinaryOutput<C, Self::Source2>
    where
        F: FnMut(Self::Source) -> C,
    {
        match self {
            Validated::Valid(x) => Validated::Valid(f(x)),
            Validated::Invalid(e) => Validated::Invalid(e),
        }
    }

    fn second<D, G>(self, g: G) -> Self::BinaryOutput<Self::Source, D>
    where
        G: FnMut(Self::Source2) -> D,
    {
        match self {
            Validated::Valid(x) => Validated::Valid(x),
            Validated::Invalid(es) => {
                let mut transformed = es.into_iter().map(g);
                let first = transformed.next().expect("invalid values have errors");
                Validated::Invalid(NonEmptyErrors::from_first_and_iter(first, transformed))
            },
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
/// let valid_fn: Validated<&str, fn(i32) -> i32> = Validated::valid(|x: i32| x * 2);
/// let valid_val: Validated<&str, i32> = Validated::valid(10);
/// assert_eq!(Applicative::apply(valid_fn, valid_val), Validated::valid(20));
/// ```
///
/// ### Invalid function, Valid value
/// ```rust
/// use rustica::datatypes::validated::Validated;
/// use rustica::traits::applicative::Applicative;
/// use rustica::traits::pure::Pure;
///
/// let invalid_fn: Validated<&str, fn(i32) -> i32> = Validated::invalid("fn_error");
/// let valid_val: Validated<&str, i32> = Validated::valid(10);
/// assert_eq!(Applicative::apply(invalid_fn, valid_val), Validated::invalid("fn_error"));
/// ```
///
/// ### Valid function, Invalid value
/// ```rust
/// use rustica::datatypes::validated::Validated;
/// use rustica::traits::applicative::Applicative;
/// use rustica::traits::pure::Pure;
///
/// let valid_fn: Validated<&str, fn(i32) -> i32> = Validated::valid(|x: i32| x * 2);
/// let invalid_val: Validated<&str, i32> = Validated::invalid("val_error");
/// assert_eq!(Applicative::apply(valid_fn, invalid_val), Validated::invalid("val_error"));
/// ```
///
/// ### Invalid function, Invalid value (error accumulation)
/// ```rust
/// use rustica::datatypes::validated::Validated;
/// use rustica::traits::applicative::Applicative;
/// use rustica::traits::pure::Pure;
/// use smallvec::smallvec;
///
/// let invalid_fn: Validated<String, fn(i32) -> i32> = Validated::invalid("fn_error".to_string());
/// let invalid_val: Validated<String, i32> = Validated::invalid("val_error".to_string());
/// // The apply implementation accumulates errors in this order:
/// // first the errors from the function (self), then the errors from the value (value)
/// let expected_errors = Validated::invalid_many(["fn_error".to_string(), "val_error".to_string()]);
/// assert_eq!(Applicative::apply(invalid_fn, invalid_val), expected_errors);
///
/// // lift2
/// let v1: Validated<&str, i32> = Validated::valid(10);
/// let v2: Validated<&str, i32> = Validated::valid(20);
/// let result = <Validated<&str, i32> as Applicative>::lift2(|a: i32, b: i32| a + b, v1, v2);
/// assert_eq!(result, Validated::valid(30));
/// ```
///
/// Combining `Valid` and `Invalid` (error accumulation):
/// ```rust
/// use rustica::datatypes::validated::Validated;
/// use rustica::traits::applicative::Applicative;
/// use smallvec::smallvec;
///
/// let v1: Validated<&str, i32> = Validated::valid(10);
/// let v2: Validated<&str, i32> = Validated::invalid("error_b");
/// let result = <Validated<&str, i32> as Applicative>::lift2(|a: i32, b: i32| a + b, v1, v2);
/// assert_eq!(result, Validated::invalid("error_b"));
///
/// let v3: Validated<&str, i32> = Validated::invalid("error_a");
/// let v4: Validated<&str, i32> = Validated::valid(20);
/// let result2 = <Validated<&str, i32> as Applicative>::lift2(|a: i32, b: i32| a + b, v3, v4);
/// assert_eq!(result2, Validated::invalid("error_a"));
///
/// // Combining two `Invalid` values (error accumulation)
/// let v1: Validated<&str, i32> = Validated::invalid("error1");
/// let v2: Validated<&str, i32> = Validated::invalid("error2");
/// let result = <Validated<&str, i32> as Applicative>::lift2(|a: i32, b: i32| a + b, v1, v2);
/// // The order of errors in lift2 is left argument's errors then right argument's errors.
/// assert_eq!(result, Validated::invalid_many(["error1", "error2"]));
/// ```
///
///
/// Applicative laws and error ordering are verified by unit tests.
impl<E, A> Applicative for Validated<E, A> {
    fn apply<T, B>(self, value: Self::Output<T>) -> Self::Output<B>
    where
        Self::Source: Fn(T) -> B,
        T: Clone,
    {
        match (self, value) {
            (Validated::Valid(f), Validated::Valid(x)) => Validated::Valid(f(x)),
            (a, b) => {
                let mut errors = ErrorAccumulator::new();

                if let Validated::Invalid(e) = a {
                    errors.extend_owned(e);
                }
                if let Validated::Invalid(e) = b {
                    errors.extend_owned(e);
                }

                Validated::invalid_from_accumulator(errors)
            },
        }
    }

    fn lift2<T, U, C, F>(f: F, fa: Self::Output<T>, fb: Self::Output<U>) -> Self::Output<C>
    where
        F: Fn(T, U) -> C,
        T: Clone,
        U: Clone,
    {
        match (fa, fb) {
            (Validated::Valid(a), Validated::Valid(b)) => Validated::Valid(f(a, b)),
            (a, b) => {
                let mut errors = ErrorAccumulator::new();

                if let Validated::Invalid(e) = a {
                    errors.extend_owned(e);
                }
                if let Validated::Invalid(e) = b {
                    errors.extend_owned(e);
                }

                Validated::invalid_from_accumulator(errors)
            },
        }
    }

    fn lift3<T, U, V, C, F>(
        f: F, fa: Self::Output<T>, fb: Self::Output<U>, fc: Self::Output<V>,
    ) -> Self::Output<C>
    where
        F: Fn(T, U, V) -> C,
        T: Clone,
        U: Clone,
        V: Clone,
    {
        match (fa, fb, fc) {
            (Validated::Valid(a), Validated::Valid(b_val), Validated::Valid(c_val)) => {
                Validated::Valid(f(a, b_val, c_val))
            },
            (Validated::Invalid(e1), Validated::Invalid(e2), Validated::Invalid(e3)) => {
                let mut errors = ErrorAccumulator::with_capacity(e1.len() + e2.len() + e3.len());
                errors.extend_owned(e1);
                errors.extend_owned(e2);
                errors.extend_owned(e3);
                Validated::invalid_from_accumulator(errors)
            },
            (a, b, c) => {
                let mut errors = ErrorAccumulator::new();

                if let Validated::Invalid(e) = a {
                    errors.extend_owned(e);
                }
                if let Validated::Invalid(e) = b {
                    errors.extend_owned(e);
                }
                if let Validated::Invalid(e) = c {
                    errors.extend_owned(e);
                }

                Validated::invalid_from_accumulator(errors)
            },
        }
    }
}

/// # Examples for `Monad` on `Validated`
///
/// Unlike `Applicative`, the `Monad` instance for `Validated` is fail-fast. It does not
/// accumulate errors. It's useful for sequencing operations where any failure should
/// halt the entire chain.
///
/// ## `bind`
///
/// ### Chaining `Valid` computations
/// ```rust
/// use rustica::datatypes::validated::Validated;
/// use rustica::traits::monad::Monad;
///
/// let v: Validated<&str, i32> = Validated::valid(10);
/// let result = v.bind(|x: i32| Validated::valid(x + 5));
/// assert_eq!(result, Validated::valid(15));
/// ```
///
/// ### A `Valid` value bound with a function that returns `Invalid`
/// ```rust
/// use rustica::datatypes::validated::Validated;
/// use rustica::traits::monad::Monad;
///
/// let v: Validated<&str, i32> = Validated::valid(10);
/// let result = v.bind(|_x: i32| Validated::<&str, i32>::invalid("computation_failed"));
/// assert_eq!(result, Validated::invalid("computation_failed"));
/// ```
///
/// ### An `Invalid` value (short-circuiting)
/// ```rust
/// use rustica::datatypes::validated::Validated;
/// use rustica::traits::monad::Monad;
///
/// let v: Validated<&str, i32> = Validated::invalid("original_error");
/// // The closure is never executed because `v` is Invalid.
/// let result = v.bind(|x: i32| Validated::valid(x + 5));
/// assert_eq!(result, Validated::invalid("original_error"));
/// ```
///
///
/// Monad laws are verified by unit tests.
impl<E, A> Monad for Validated<E, A> {
    #[inline]
    fn bind<U, F>(self, mut f: F) -> Self::Output<U>
    where
        F: FnMut(Self::Source) -> Self::Output<U>,
    {
        match self {
            Validated::Valid(a) => f(a),
            Validated::Invalid(e) => Validated::Invalid(e),
        }
    }

    #[inline]
    fn join<U>(self) -> Self::Output<U>
    where
        Self::Source: Into<Self::Output<U>>,
    {
        match self {
            Validated::Valid(inner) => inner.into(),
            Validated::Invalid(e) => Validated::Invalid(e),
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
/// let valid = Validated::<&str, i32>::valid(42);
/// let doubled = valid.fold_left(0, |_, x| x * 2);
/// assert_eq!(doubled, 84);
///
/// // Folding an Invalid value with fold_left returns the initial value
/// let invalid = Validated::<&str, i32>::invalid("error");
/// let result = invalid.fold_left(100, |_, x| x + 1);
/// assert_eq!(result, 100);
///
/// // Folding a Valid value with fold_right
/// let valid = Validated::<&str, i32>::valid(42);
/// let doubled = valid.fold_right(0, |x, _| x * 2);
/// assert_eq!(doubled, 84);
///
/// // Folding an Invalid value with fold_right returns the initial value
/// let invalid = Validated::<&str, i32>::invalid("error");
/// let result = invalid.fold_right(100, |x, _| x + 1);
/// assert_eq!(result, 100);
/// ```
impl<E, A> Foldable for Validated<E, A> {
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
/// - If both are `Valid`, their inner values are combined using `A::combine`.
/// - If one is `Invalid` and one is `Valid`, the `Invalid` is returned (errors take precedence).
/// - If both are `Invalid`, their error collections are concatenated.
impl<E, A: Semigroup> Semigroup for Validated<E, A> {
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
impl<E, A> Arbitrary for Validated<E, A>
where
    E: Arbitrary,
    A: Arbitrary,
{
    fn arbitrary(g: &mut Gen) -> Self {
        let x = A::arbitrary(g);
        let y = E::arbitrary(g);
        if bool::arbitrary(g) {
            Validated::valid(x)
        } else {
            Validated::invalid(y)
        }
    }
}
