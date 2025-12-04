use smallvec::SmallVec;

use crate::datatypes::validated::core::Validated;
use crate::traits::applicative::Applicative;
use crate::traits::bifunctor::Bifunctor;
use crate::traits::foldable::Foldable;
use crate::traits::functor::Functor;
use crate::traits::hkt::{BinaryHKT, HKT};
use crate::traits::monoid::Monoid;
use crate::traits::pure::Pure;
use crate::traits::semigroup::Semigroup;
use quickcheck::{Arbitrary, Gen};

impl<E, A> AsRef<A> for Validated<E, A> {
    #[inline]
    fn as_ref(&self) -> &A {
        match self {
            Validated::Valid(x) => x,
            _ => panic!("called `as_ref()` on an invalid value"),
        }
    }
}

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
/// let valid: Validated<&str, i32> = <Validated<&str, i32> as Pure>::pure(&10);
/// assert_eq!(valid, Validated::valid(10));
/// ```
///
/// ## `pure_owned`
///
/// ```rust
/// use rustica::datatypes::validated::Validated;
/// use rustica::traits::pure::Pure;
///
/// let valid: Validated<String, i32> = <Validated<String, i32> as Pure>::pure_owned(10);
/// assert_eq!(valid, Validated::valid(10));
/// ```
impl<E: Clone, A: Clone> Pure for Validated<E, A> {
    #[inline]
    fn pure<T: Clone>(x: &T) -> Self::Output<T> {
        Validated::Valid(x.clone())
    }

    #[inline]
    fn pure_owned<T: Clone>(x: T) -> Self::Output<T> {
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
/// let mapped = valid.fmap(|x: &i32| x * 2);
/// assert_eq!(mapped, Validated::valid(20));
/// ```
///
/// Mapping over an `Invalid` value:
/// ```rust
/// use rustica::datatypes::validated::Validated;
/// use rustica::traits::functor::Functor;
///
/// let invalid: Validated<&str, i32> = Validated::invalid("error");
/// let mapped = invalid.fmap(|x: &i32| x * 2);
/// assert_eq!(mapped, Validated::invalid("error"));
/// ```
///
/// ## `fmap_owned`
///
/// Mapping over a `Valid` value with ownership:
/// ```rust
/// use rustica::datatypes::validated::Validated;
/// use rustica::traits::functor::Functor;
///
/// let valid: Validated<String, i32> = Validated::valid(10);
/// let mapped = valid.fmap_owned(|x: i32| x * 2);
/// assert_eq!(mapped, Validated::valid(20));
/// ```
///
/// Mapping over an `Invalid` value with ownership:
/// ```rust
/// use rustica::datatypes::validated::Validated;
/// use rustica::traits::functor::Functor;
///
/// let invalid: Validated<String, i32> = Validated::invalid("error".to_string());
/// let mapped = invalid.fmap_owned(|x: i32| x * 2);
/// assert_eq!(mapped, Validated::invalid("error".to_string()));
/// ```
///
/// ## Functor Laws
///
/// ### Identity Law: `v.fmap(|x| x.clone()) == v`
/// ```rust
/// use rustica::datatypes::validated::Validated;
/// use rustica::traits::functor::Functor;
///
/// let valid: Validated<&str, i32> = Validated::valid(10);
/// assert_eq!(valid.fmap(|x: &i32| *x), valid);
///
/// let invalid: Validated<&str, i32> = Validated::invalid("error");
/// assert_eq!(invalid.fmap(|x: &i32| *x), invalid);
/// ```
impl<E: Clone, A: Clone> Functor for Validated<E, A> {
    #[inline]
    fn fmap<B, F>(&self, f: F) -> Self::Output<B>
    where
        F: Fn(&Self::Source) -> B,
        B: Clone,
    {
        match self {
            Validated::Valid(x) => Validated::Valid(f(x)),
            Validated::Invalid(e) => Validated::Invalid(e.clone()),
        }
    }

    #[inline]
    fn fmap_owned<B, F>(self, f: F) -> Self::Output<B>
    where
        Self: Sized,
        F: FnOnce(Self::Source) -> B,
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

    fn map_second<F, C>(&self, f: F) -> Self::BinaryOutput<A, C>
    where
        F: Fn(&Self::Source2) -> C,
        Self::Source: Clone,
        Self::Source2: Clone,
        C: Clone,
    {
        match self {
            Validated::Valid(x) => Validated::Valid(x.clone()),
            Validated::Invalid(es) => {
                let transformed: SmallVec<[C; 8]> = es.iter().map(f).collect();
                Validated::Invalid(transformed)
            },
        }
    }

    fn map_second_owned<F, C>(self, f: F) -> Self::BinaryOutput<A, C>
    where
        F: Fn(Self::Source2) -> C,
        C: Clone,
    {
        match self {
            Validated::Valid(x) => Validated::Valid(x),
            Validated::Invalid(es) => {
                let transformed: SmallVec<[C; 8]> = es.into_iter().map(f).collect();
                Validated::Invalid(transformed)
            },
        }
    }
}

/// # Examples for `Bifunctor` on `Validated`
///
/// `Bifunctor` allows mapping over either the `Invalid` (left) or `Valid` (right) side.
///
/// ## `bimap`
///
/// ### Mapping over a `Valid` value (applies the first function)
/// ```rust
/// use rustica::datatypes::validated::Validated;
/// use rustica::traits::bifunctor::Bifunctor;
///
/// let valid: Validated<&str, i32> = Validated::valid(10);
/// // The first function `|v| v * 2` is applied to the `Valid` value.
/// let result = valid.bimap(|v: &i32| v * 2, |e: &&str| format!("Error: {}", e));
/// assert_eq!(result, Validated::valid(20));
/// ```
///
/// ### Mapping over an `Invalid` value (applies the second function)
/// ```rust
/// use rustica::datatypes::validated::Validated;
/// use rustica::traits::bifunctor::Bifunctor;
///
/// let invalid: Validated<&str, i32> = Validated::invalid_many(vec!["e1", "e2"]);
/// // The second function `|e| format!("New-{}", e)` is applied to the `Invalid` errors.
/// let result = invalid.bimap(|v: &i32| v * 2, |e: &&str| format!("New-{}", e));
/// assert_eq!(result, Validated::invalid_many(vec!["New-e1".to_string(), "New-e2".to_string()]));
impl<E: Clone, A: Clone> Bifunctor for Validated<E, A> {
    fn bimap<C, D, F, G>(&self, f: F, g: G) -> Self::BinaryOutput<C, D>
    where
        F: Fn(&Self::Source) -> C,
        G: Fn(&Self::Source2) -> D,
        C: Clone,
        D: Clone,
    {
        match self {
            Validated::Valid(x) => Validated::Valid(f(x)),
            Validated::Invalid(es) => {
                let transformed: SmallVec<[D; 8]> = es.iter().map(g).collect();
                Validated::Invalid(transformed)
            },
        }
    }

    fn first<C, F>(&self, f: F) -> Self::BinaryOutput<C, Self::Source2>
    where
        F: Fn(&Self::Source) -> C,
        C: Clone,
    {
        match self {
            Validated::Valid(x) => Validated::Valid(f(x)),
            Validated::Invalid(e) => Validated::Invalid(e.clone()),
        }
    }

    fn second<D, G>(&self, g: G) -> Self::BinaryOutput<Self::Source, D>
    where
        G: Fn(&Self::Source2) -> D,
        D: Clone,
    {
        match self {
            Validated::Valid(x) => Validated::Valid(x.clone()),
            Validated::Invalid(es) => {
                let transformed: SmallVec<[D; 8]> = es.iter().map(g).collect();
                Validated::Invalid(transformed)
            },
        }
    }
}

/// # Examples for `Applicative` on `Validated`
///
/// `Validated`'s `Applicative` instance accumulates errors.
///
/// ## `apply`
///
/// ### Valid function, Valid value
/// ```rust
/// use rustica::datatypes::validated::Validated;
/// use rustica::traits::applicative::Applicative;
/// use rustica::traits::pure::Pure;
///
/// let valid_fn: Validated<&str, fn(&i32) -> i32> = Validated::valid(|x: &i32| x * 2);
/// let valid_val: Validated<&str, i32> = Validated::valid(10);
/// assert_eq!(Applicative::apply(&valid_fn, &valid_val), Validated::valid(20));
/// ```
///
/// ### Invalid function, Valid value
/// ```rust
/// use rustica::datatypes::validated::Validated;
/// use rustica::traits::applicative::Applicative;
/// use rustica::traits::pure::Pure;
///
/// let invalid_fn: Validated<&str, fn(&i32) -> i32> = Validated::invalid("fn_error");
/// let valid_val: Validated<&str, i32> = Validated::valid(10);
/// assert_eq!(Applicative::apply(&invalid_fn, &valid_val), Validated::invalid("fn_error"));
/// ```
///
/// ### Valid function, Invalid value
/// ```rust
/// use rustica::datatypes::validated::Validated;
/// use rustica::traits::applicative::Applicative;
/// use rustica::traits::pure::Pure;
///
/// let valid_fn: Validated<&str, fn(&i32) -> i32> = Validated::valid(|x: &i32| x * 2);
/// let invalid_val: Validated<&str, i32> = Validated::invalid("val_error");
/// assert_eq!(Applicative::apply(&valid_fn, &invalid_val), Validated::invalid("val_error"));
/// ```
///
/// ### Invalid function, Invalid value (error accumulation)
/// ```rust
/// use rustica::datatypes::validated::Validated;
/// use rustica::traits::applicative::Applicative;
/// use rustica::traits::pure::Pure;
/// use smallvec::smallvec;
///
/// let invalid_fn: Validated<String, fn(&i32) -> i32> = Validated::invalid("fn_error".to_string());
/// let invalid_val: Validated<String, i32> = Validated::invalid("val_error".to_string());
/// // The apply implementation accumulates errors in this order:
/// // first the errors from the function (self), then the errors from the value (rf)
/// let expected_errors = smallvec!["fn_error".to_string(), "val_error".to_string()];
/// assert_eq!(Applicative::apply(&invalid_fn, &invalid_val), Validated::Invalid(expected_errors));
///
/// // lift2
/// let v1: Validated<&str, i32> = Validated::valid(10);
/// let v2: Validated<&str, i32> = Validated::valid(20);
/// let result = <Validated<&str, i32> as Applicative>::lift2(|a: &i32, b: &i32| a + b, &v1, &v2);
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
/// let result = <Validated<&str, i32> as Applicative>::lift2(|a: &i32, b: &i32| a + b, &v1, &v2);
/// assert_eq!(result, Validated::Invalid(smallvec!["error_b"]));
///
/// let v3: Validated<&str, i32> = Validated::invalid("error_a");
/// let v4: Validated<&str, i32> = Validated::valid(20);
/// let result2 = <Validated<&str, i32> as Applicative>::lift2(|a: &i32, b: &i32| a + b, &v3, &v4);
/// assert_eq!(result2, Validated::Invalid(smallvec!["error_a"]));
///
/// // Combining two `Invalid` values (error accumulation)
/// let v1: Validated<&str, i32> = Validated::invalid("error1");
/// let v2: Validated<&str, i32> = Validated::invalid("error2");
/// let result = <Validated<&str, i32> as Applicative>::lift2(|a: &i32, b: &i32| a + b, &v1, &v2);
/// // The order of errors in lift2 is self's errors then rb's errors.
/// assert_eq!(result, Validated::Invalid(smallvec!["error1", "error2"]));
/// ```
///
/// ## Applicative Laws
///
/// ### Homomorphism: `Applicative::apply(&Validated::pure(f), &Validated::pure(x)) == Validated::pure(f(x))`
/// ```rust
/// use rustica::datatypes::validated::Validated;
/// use rustica::traits::applicative::Applicative;
/// use rustica::traits::pure::Pure;
///
/// let f = |x: &i32| *x * 2; // Note: Using a reference parameter to match apply's expected Fn(&T) signature
/// let x = 10;
///
/// // Left side: Applicative::apply(&Validated::pure(f), &Validated::pure(x))
/// let pure_f: Validated<String, fn(&i32) -> i32> = Validated::<String, fn(&i32) -> i32>::pure_owned(f);
/// let pure_x: Validated<String, i32> = Validated::<String, i32>::pure_owned(x);
/// let left_side = <Validated<String, fn(&i32) -> i32> as Applicative>::apply(&pure_f, &pure_x); // This works because f is a Fn(&i32) -> i32
///
/// // Right side: Validated::pure(f(x))
/// let right_side = Validated::<String, i32>::pure_owned(f(&x));
///
/// // Both sides are equal
/// assert_eq!(left_side, right_side);
/// assert_eq!(left_side, Validated::valid(20));
/// ```
impl<E: Clone, A: Clone> Applicative for Validated<E, A> {
    fn apply<T, B>(&self, value: &Self::Output<T>) -> Self::Output<B>
    where
        Self::Source: Fn(&T) -> B,
        B: Clone,
    {
        match (self, value) {
            (Validated::Valid(f), Validated::Valid(a)) => Validated::Valid(f(a)),
            (Validated::Valid(_), Validated::Invalid(e)) => Validated::Invalid(e.clone()),
            (Validated::Invalid(e), Validated::Valid(_)) => Validated::Invalid(e.clone()),
            (Validated::Invalid(e1), Validated::Invalid(e2)) => {
                let mut errors = SmallVec::<[E; 8]>::with_capacity(e1.len() + e2.len());
                errors.extend(e1.iter().chain(e2.iter()).cloned());
                Validated::Invalid(errors)
            },
        }
    }

    fn apply_owned<T, B>(self, value: Self::Output<T>) -> Self::Output<B>
    where
        Self::Source: Fn(T) -> B,
        T: Clone,
        B: Clone,
    {
        match (self, value) {
            (Validated::Valid(f), Validated::Valid(x)) => Validated::Valid(f(x)),
            (a, b) => {
                let mut errors = SmallVec::<[E; 8]>::new();

                if let Validated::Invalid(e) = a {
                    errors.extend(e);
                }
                if let Validated::Invalid(e) = b {
                    errors.extend(e);
                }

                Validated::Invalid(errors)
            },
        }
    }

    fn lift2<T, U, C, F>(f: F, fa: &Self::Output<T>, fb: &Self::Output<U>) -> Self::Output<C>
    where
        F: Fn(&T, &U) -> C,
        T: Clone,
        U: Clone,
        C: Clone,
        Self: Sized,
    {
        match (fa, fb) {
            (Validated::Valid(a), Validated::Valid(b)) => Validated::Valid(f(a, b)),
            _ => {
                let mut errors = SmallVec::<[E; 8]>::new();

                if let Validated::Invalid(es) = fa {
                    errors.extend(es.iter().cloned());
                }

                if let Validated::Invalid(es) = fb {
                    errors.extend(es.iter().cloned());
                }

                Validated::Invalid(errors)
            },
        }
    }

    fn lift2_owned<T, U, C, F>(f: F, fa: Self::Output<T>, fb: Self::Output<U>) -> Self::Output<C>
    where
        F: Fn(T, U) -> C,
        T: Clone,
        U: Clone,
        C: Clone,
        Self: Sized,
    {
        match (fa, fb) {
            (Validated::Valid(a), Validated::Valid(b)) => Validated::Valid(f(a, b)),
            (a, b) => {
                let mut errors = SmallVec::<[E; 8]>::new();

                if let Validated::Invalid(e) = a {
                    errors.extend(e);
                }
                if let Validated::Invalid(e) = b {
                    errors.extend(e);
                }

                Validated::Invalid(errors)
            },
        }
    }

    #[inline]
    fn lift3<T, U, V, C, F>(
        f: F, fa: &Self::Output<T>, fb: &Self::Output<U>, fc: &Self::Output<V>,
    ) -> Self::Output<C>
    where
        F: Fn(&T, &U, &V) -> C,
        T: Clone,
        U: Clone,
        V: Clone,
        C: Clone,
        Self: Sized,
    {
        match (fa, fb, fc) {
            (Validated::Valid(a), Validated::Valid(b), Validated::Valid(c)) => {
                Validated::Valid(f(a, b, c))
            },
            _ => {
                let mut errors = SmallVec::<[E; 8]>::new();

                if let Validated::Invalid(es) = fa {
                    errors.extend(es.iter().cloned());
                }
                if let Validated::Invalid(es) = fb {
                    errors.extend(es.iter().cloned());
                }
                if let Validated::Invalid(es) = fc {
                    errors.extend(es.iter().cloned());
                }

                Validated::Invalid(errors)
            },
        }
    }

    fn lift3_owned<T, U, V, C, F>(
        f: F, fa: Self::Output<T>, fb: Self::Output<U>, fc: Self::Output<V>,
    ) -> Self::Output<C>
    where
        F: Fn(T, U, V) -> C,
        T: Clone,
        U: Clone,
        V: Clone,
        C: Clone,
        Self: Sized,
    {
        match (fa, fb, fc) {
            (Validated::Valid(a), Validated::Valid(b_val), Validated::Valid(c_val)) => {
                Validated::Valid(f(a, b_val, c_val))
            },
            (Validated::Invalid(e1), Validated::Invalid(e2), Validated::Invalid(e3)) => {
                let mut errors = SmallVec::<[E; 8]>::with_capacity(e1.len() + e2.len() + e3.len());
                errors.extend(e1);
                errors.extend(e2);
                errors.extend(e3);
                Validated::Invalid(errors)
            },
            (a, b, c) => {
                let mut errors = SmallVec::<[E; 8]>::new();

                if let Validated::Invalid(e) = a {
                    errors.extend(e);
                }
                if let Validated::Invalid(e) = b {
                    errors.extend(e);
                }
                if let Validated::Invalid(e) = c {
                    errors.extend(e);
                }

                Validated::Invalid(errors)
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
/// let valid = Validated::<&str, i32>::valid(42);
/// let doubled = valid.fold_left(&0, |_, x| *x * 2);
/// assert_eq!(doubled, 84);
///
/// // Folding an Invalid value with fold_left returns the initial value
/// let invalid = Validated::<&str, i32>::invalid("error");
/// let result = invalid.fold_left(&100, |_, x| *x + 1);
/// assert_eq!(result, 100);
///
/// // Folding a Valid value with fold_right
/// let valid = Validated::<&str, i32>::valid(42);
/// let doubled = valid.fold_right(&0, |x, _| *x * 2);
/// assert_eq!(doubled, 84);
///
/// // Folding an Invalid value with fold_right returns the initial value
/// let invalid = Validated::<&str, i32>::invalid("error");
/// let result = invalid.fold_right(&100, |x, _| *x + 1);
/// assert_eq!(result, 100);
/// ```
impl<E, A> Foldable for Validated<E, A> {
    #[inline]
    fn fold_left<U, F>(&self, init: &U, f: F) -> U
    where
        F: Fn(&U, &Self::Source) -> U,
        U: Clone,
    {
        match self {
            Validated::Valid(a) => f(init, a),
            _ => init.clone(),
        }
    }

    #[inline]
    fn fold_right<U, F>(&self, init: &U, f: F) -> U
    where
        F: Fn(&Self::Source, &U) -> U,
        U: Clone,
    {
        match self {
            Validated::Valid(a) => f(a, init),
            _ => init.clone(),
        }
    }
}

impl<E: Clone, A: Clone> Semigroup for Validated<E, A> {
    fn combine(&self, other: &Self) -> Self {
        match (self, other) {
            (Validated::Valid(_), _) => self.clone(),
            (Validated::Invalid(_), Validated::Valid(_)) => other.clone(),
            (Validated::Invalid(e1), Validated::Invalid(e2)) => {
                let mut errors = SmallVec::<[E; 8]>::with_capacity(e1.len() + e2.len());
                errors.extend(e1.iter().chain(e2.iter()).cloned());
                Validated::Invalid(errors)
            },
        }
    }

    fn combine_owned(self, other: Self) -> Self {
        match (self, other) {
            (s @ Validated::Valid(_), _) => s,
            (Validated::Invalid(_), o @ Validated::Valid(_)) => o,
            (Validated::Invalid(mut e1), Validated::Invalid(e2)) => {
                e1.extend(e2);
                Validated::Invalid(e1)
            },
        }
    }
}

impl<E: Clone, A: Clone> Monoid for Validated<E, A> {
    fn empty() -> Self {
        Validated::Invalid(SmallVec::new())
    }
}

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
