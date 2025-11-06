use smallvec::SmallVec;

use crate::datatypes::validated::core::Validated;
use crate::traits::alternative::Alternative;
use crate::traits::applicative::Applicative;
use crate::traits::bifunctor::Bifunctor;
use crate::traits::foldable::Foldable;
use crate::traits::functor::Functor;
use crate::traits::hkt::{BinaryHKT, HKT};
use crate::traits::identity::Identity;
use crate::traits::monad::Monad;
use crate::traits::monad_plus::MonadPlus;
use crate::traits::monoid::Monoid;
use crate::traits::pure::Pure;
use crate::traits::semigroup::Semigroup;

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
/// # Performance
///
/// The `pure` operation is constant time, O(1).
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
/// # Performance
///
/// The `fmap` operation is constant time, O(1), as it only affects the `Valid` variant.
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
/// ```
///
/// # Performance
///
/// The `apply` and `lift2` operations exhibit the following performance characteristics:
/// - `Valid` + `Valid` -> `Valid`: Constant time, O(1).
/// - `Valid` + `Invalid` -> `Invalid`: Constant time, O(1).
/// - `Invalid` + `Valid` -> `Invalid`: Constant time, O(1).
/// - `Invalid` + `Invalid` -> `Invalid`: Linear time, O(n + m), where `n` and `m` are the
///   number of errors in the respective instances. This is due to the concatenation of error lists.
///
/// ## `lift2`
///
/// Combining two `Valid` values:
/// ```rust
/// use rustica::datatypes::validated::Validated;
/// use rustica::traits::applicative::Applicative;
///
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
/// ```
///
/// Combining two `Invalid` values (error accumulation):
/// ```rust
/// use rustica::datatypes::validated::Validated;
/// use rustica::traits::applicative::Applicative;
/// use smallvec::smallvec;
///
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
/// let result = v.bind(|x: &i32| Validated::valid(*x + 5));
/// assert_eq!(result, Validated::valid(15));
/// ```
///
/// ### A `Valid` value bound with a function that returns `Invalid`
/// ```rust
/// use rustica::datatypes::validated::Validated;
/// use rustica::traits::monad::Monad;
///
/// let v: Validated<&str, i32> = Validated::valid(10);
/// let result = v.bind(|_x: &i32| Validated::<&str, i32>::invalid("computation_failed"));
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
/// let result = v.bind(|x: &i32| Validated::valid(*x + 5));
/// assert_eq!(result, Validated::invalid("original_error"));
/// ```
///
/// # Performance
///
/// The `bind` operation is constant time, O(1), as it only affects the `Valid` variant.
///
/// ## Monad Laws
///
/// ### Left Identity: `Pure::pure_owned(a).bind_owned(f) == f(a)`
/// ```rust
/// use rustica::datatypes::validated::Validated;
/// use rustica::traits::monad::Monad;
/// use rustica::traits::pure::Pure;
///
/// let f = |x: i32| -> Validated<String, i32> { Validated::valid(x * 2) };
/// let x = 21;
///
/// let lhs = <Validated<String, i32> as Pure>::pure_owned(x).bind_owned(f);
/// let rhs = f(x);
///
/// assert_eq!(lhs, rhs);
/// assert_eq!(lhs, Validated::valid(42));
/// ```
impl<E: Clone, A: Clone> Monad for Validated<E, A> {
    #[inline]
    fn bind<U, F>(&self, f: F) -> Self::Output<U>
    where
        U: Clone,
        F: Fn(&Self::Source) -> Self::Output<U>,
    {
        match self {
            Validated::Valid(a) => f(a),
            Validated::Invalid(e) => Validated::Invalid(e.clone()),
        }
    }

    #[inline]
    fn join<U>(&self) -> Self::Output<U>
    where
        Self::Source: Clone + Into<Self::Output<U>>,
        U: Clone,
        E: Clone,
    {
        match self {
            Validated::Valid(inner) => inner.clone().into(),
            Validated::Invalid(e) => Validated::Invalid(e.clone()),
        }
    }

    #[inline]
    fn bind_owned<U, F>(self, f: F) -> Self::Output<U>
    where
        U: Clone,
        F: FnOnce(Self::Source) -> Self::Output<U>,
    {
        match self {
            Validated::Valid(a) => f(a),
            Validated::Invalid(e) => Validated::Invalid(e),
        }
    }

    #[inline]
    fn join_owned<U>(self) -> Self::Output<U>
    where
        Self::Source: Into<Self::Output<U>>,
    {
        match self {
            Validated::Valid(inner) => inner.into(),
            Validated::Invalid(e) => Validated::Invalid(e),
        }
    }
}

impl<E: Clone, A: Clone> Identity for Validated<E, A> {
    #[inline]
    fn value(&self) -> &Self::Source {
        match self {
            Validated::Valid(a) => a,
            _ => panic!("Cannot extract value from invalid Validated"),
        }
    }

    #[inline]
    fn into_value(self) -> Self::Source {
        match self {
            Validated::Valid(x) => x,
            _ => panic!("Cannot extract value from invalid Validated"),
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
///
/// # Performance
///
/// The `fold_left` and `fold_right` operations are constant time, O(1), as they only affect the `Valid` variant.
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

/// # Examples for `Alternative` on `Validated`
///
/// `Alternative` provides a way to express choice and failure. For `Validated`, it
/// provides a fallback mechanism. The error type `E` must implement `Default`.
///
/// ## `alt`
///
/// `alt` returns the first `Valid` instance, otherwise it returns the second argument.
///
/// ### First value is `Valid`
/// ```rust
/// use rustica::datatypes::validated::Validated;
/// use rustica::traits::alternative::Alternative;
///
/// let v1: Validated<String, i32> = Validated::valid(1);
/// let v2: Validated<String, i32> = Validated::valid(2);
/// assert_eq!(v1.alt(&v2), Validated::valid(1));
/// ```
///
/// ### First value is `Invalid`, second is `Valid`
/// ```rust
/// use rustica::datatypes::validated::Validated;
/// use rustica::traits::alternative::Alternative;
///
/// let v1: Validated<String, i32> = Validated::invalid("error".to_string());
/// let v2: Validated<String, i32> = Validated::valid(2);
/// assert_eq!(v1.alt(&v2), Validated::valid(2));
/// ```
///
/// ### Both values are `Invalid`
/// ```rust
/// use rustica::datatypes::validated::Validated;
/// use rustica::traits::alternative::Alternative;
///
/// let v1: Validated<String, i32> = Validated::invalid("error1".to_string());
/// let v2: Validated<String, i32> = Validated::invalid("error2".to_string());
/// assert_eq!(v1.alt(&v2), Validated::invalid("error2".to_string()));
/// ```
///
/// # Performance
///
/// The `alt` operation is constant time, O(1), as it only checks the first variant.
///
/// ## `empty_alt`
///
/// `empty_alt` creates an `Invalid` instance with a default error value.
///
/// ```rust
/// use rustica::datatypes::validated::Validated;
/// use rustica::traits::alternative::Alternative;
///
/// let empty: Validated<String, i32> = <Validated<String, i32> as Alternative>::empty_alt();
/// assert!(empty.is_invalid());
/// // It contains a single default error
/// assert_eq!(empty.errors(), vec![String::default()]);
/// ```
///
/// ## `guard`
///
/// `guard` creates a `Valid(())` if the condition is true, otherwise an `Invalid`
/// instance with a default error.
///
/// ### Condition is true
/// ```rust
/// use rustica::datatypes::validated::Validated;
/// use rustica::traits::alternative::Alternative;
///
/// let result: Validated<String, ()> = <Validated<String, ()> as Alternative>::guard(true);
/// assert_eq!(result, Validated::valid(()));
/// ```
///
/// ### Condition is false
/// ```rust
/// use rustica::datatypes::validated::Validated;
/// use rustica::traits::alternative::Alternative;
///
/// let result: Validated<String, ()> = <Validated<String, ()> as Alternative>::guard(false);
/// assert!(result.is_invalid());
/// assert_eq!(result.errors().as_slice(), &[String::default()]);
/// ```
///
/// ## `many`
///
/// `many` collects one or more occurrences. For `Validated`, this means if the value is
/// `Valid`, it returns a `Valid` `Vec` with one element. If it's `Invalid`, it
/// returns an `Invalid` with a default error, discarding original errors.
///
/// ### On a `Valid` value
/// ```rust
/// use rustica::datatypes::validated::Validated;
/// use rustica::traits::alternative::Alternative;
///
/// let v: Validated<String, i32> = Validated::valid(42);
/// assert_eq!(v.many(), Validated::valid(vec![42]));
/// ```
///
/// ### On an `Invalid` value
/// ```rust
/// use rustica::datatypes::validated::Validated;
/// use rustica::traits::alternative::Alternative;
///
/// let v: Validated<String, i32> = Validated::invalid("original error".to_string());
/// let result = v.many();
/// assert!(result.is_invalid());
/// // Note: original errors are discarded.
/// assert_eq!(result.errors().as_slice(), &[String::default()]);
/// ```
impl<E: Clone + Default, A: Clone> Alternative for Validated<E, A> {
    fn empty_alt<B: Clone>() -> Self::Output<B> {
        Validated::invalid(E::default())
    }

    fn alt(&self, other: &Self) -> Self {
        match self {
            Validated::Valid(_) => self.clone(),
            Validated::Invalid(_) => other.clone(),
        }
    }

    fn guard(condition: bool) -> Self::Output<()> {
        if condition {
            Validated::valid(())
        } else {
            Validated::invalid(E::default())
        }
    }

    fn many(&self) -> Self::Output<Vec<Self::Source>>
    where
        Self::Source: Clone,
    {
        match self {
            Validated::Valid(x) => Validated::valid(vec![x.clone()]),
            Validated::Invalid(_) => Validated::invalid(E::default()),
        }
    }
}

/// # Examples for `MonadPlus` on `Validated`
///
/// `MonadPlus` extends `Monad` with additional operations for combining values.
///
/// ## `mzero`
///
/// ```rust
/// use rustica::datatypes::validated::Validated;
/// use rustica::traits::monad_plus::MonadPlus;
///
/// // Create a zero value using mzero
/// let zero: Validated<&str, i32> = Validated::<&str, i32>::mzero();
/// assert!(zero.is_invalid());
///
/// // Check that it's invalid with empty errors
/// assert_eq!(zero.errors().len(), 0);
///
/// // mzero is the identity element for mplus
/// let valid = Validated::valid(42);
/// assert_eq!(zero.mplus(&valid), valid);
/// assert_eq!(valid.mplus(&zero), valid);
/// ```
///
/// # Performance
///
/// The `mplus` operation has the same performance characteristics as `Applicative::apply`.
/// It is O(n + m) when combining two `Invalid` instances.
///
/// ## `mplus`
///
/// `mplus` returns the first `Valid` instance, or combines errors if both are `Invalid`.
///
/// ### Combining with first value valid
/// ```rust
/// use rustica::datatypes::validated::Validated;
/// use rustica::traits::monad_plus::MonadPlus;
///
/// let a: Validated<&str, i32> = Validated::valid(42);
/// let b: Validated<&str, i32> = Validated::invalid("error");
/// let result = a.mplus(&b);
/// assert_eq!(result, Validated::valid(42));
/// ```
///
/// ### Combining with second value valid
/// ```rust
/// use rustica::datatypes::validated::Validated;
/// use rustica::traits::monad_plus::MonadPlus;
///
/// let a: Validated<&str, i32> = Validated::invalid("error1");
/// let b: Validated<&str, i32> = Validated::valid(42);
/// let result = a.mplus(&b);
/// assert_eq!(result, Validated::valid(42));
/// ```
///
/// ### Combining with both values invalid
/// ```rust
/// use rustica::datatypes::validated::Validated;
/// use rustica::traits::monad_plus::MonadPlus;
///
/// let a: Validated<&str, i32> = Validated::invalid("error1");
/// let b: Validated<&str, i32> = Validated::invalid("error2");
/// let result = a.mplus(&b);
/// assert!(result.is_invalid());
/// assert_eq!(result.iter_errors().collect::<Vec<_>>(), vec![&"error1", &"error2"]);
/// ```
impl<E: Clone, A: Clone> MonadPlus for Validated<E, A> {
    fn mzero<U: Clone>() -> Self::Output<U> {
        Monoid::empty()
    }

    fn mplus(&self, other: &Self) -> Self {
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

    fn mplus_owned(self, other: Self) -> Self
    where
        Self: Sized,
    {
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
