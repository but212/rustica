use quickcheck::{TestResult, quickcheck};
use rustica::datatypes::maybe::{Maybe, Maybe::*};
use rustica::traits::applicative::Applicative;
use rustica::traits::functor::Functor;
use rustica::traits::monad::Monad;
use rustica::traits::monad_plus::MonadPlus;
use rustica::traits::pure::Pure;

// Functor Laws
#[test]
fn test_functor_identity() {
    fn functor_identity(m: Maybe<i32>) -> TestResult {
        if m.is_nothing() {
            return TestResult::discard();
        }
        TestResult::from_bool(m.fmap(|x| *x) == m)
    }
    quickcheck(functor_identity as fn(Maybe<i32>) -> TestResult);
}

#[test]
fn test_functor_composition() {
    fn functor_composition(m: Maybe<i32>) -> TestResult {
        if m.is_nothing() {
            return TestResult::discard();
        }
        let f = |x: &i32| x.saturating_add(1);
        let g = |x: &i32| x.saturating_mul(2);
        TestResult::from_bool(m.fmap(|x| g(&f(x))) == m.fmap(f).fmap(g))
    }
    quickcheck(functor_composition as fn(Maybe<i32>) -> TestResult);
}

// Applicative Laws

#[test]
fn test_applicative_identity() {
    fn applicative_identity(v: Maybe<i32>) -> TestResult {
        if v.is_nothing() {
            return TestResult::discard();
        }
        let id_fn = |x: &i32| *x;
        let pure_id = Maybe::<fn(&i32) -> i32>::pure(&id_fn);
        TestResult::from_bool(pure_id.apply(&v) == v)
    }
    quickcheck(applicative_identity as fn(Maybe<i32>) -> TestResult);
}

#[test]
fn test_applicative_homomorphism() {
    fn applicative_homomorphism(x: i32) -> bool {
        let f = |val: &i32| val.saturating_add(1);
        let pure_f = Maybe::<fn(&i32) -> i32>::pure(&f);
        let pure_x = Maybe::<i32>::pure(&x);
        pure_f.apply(&pure_x) == Maybe::<i32>::pure(&f(&x))
    }
    quickcheck(applicative_homomorphism as fn(i32) -> bool);
}

#[test]
fn test_applicative_interchange() {
    fn applicative_interchange(y: i32) -> bool {
        fn f(x: &i32) -> i32 {
            x.saturating_mul(2)
        }
        let u: Maybe<fn(&i32) -> i32> = Maybe::Just(f);
        let pure_y = Maybe::<i32>::pure(&y);
        let left = u.apply(&pure_y);

        let apply_to_y = |g: &fn(&i32) -> i32| g(&y);
        let pure_apply_to_y = Maybe::<fn(&fn(&i32) -> i32) -> i32>::pure(&apply_to_y);
        let right = pure_apply_to_y.apply(&u);

        left == right
    }
    quickcheck(applicative_interchange as fn(i32) -> bool);
}

// Monad Laws

#[test]
fn test_monad_left_identity() {
    fn monad_left_identity(x: i32) -> bool {
        let f = |val: &i32| Just(val.saturating_mul(2));
        Maybe::<i32>::pure(&x).bind(f) == f(&x)
    }
    quickcheck(monad_left_identity as fn(i32) -> bool);
}

#[test]
fn test_monad_right_identity() {
    fn monad_right_identity(m: Maybe<i32>) -> TestResult {
        if m.is_nothing() {
            return TestResult::discard();
        }
        TestResult::from_bool(m.bind::<i32, _>(Maybe::<i32>::pure) == m)
    }
    quickcheck(monad_right_identity as fn(Maybe<i32>) -> TestResult);
}

#[test]
fn test_monad_associativity() {
    fn monad_associativity(m: Maybe<i32>) -> TestResult {
        if m.is_nothing() {
            return TestResult::discard();
        }
        let f = |x: &i32| Just(x.saturating_add(10));
        let g = |x: &i32| Just(x.saturating_mul(2));
        TestResult::from_bool(m.bind(f).bind(g) == m.bind(|x| f(x).bind(g)))
    }
    quickcheck(monad_associativity as fn(Maybe<i32>) -> TestResult);
}

// MonadPlus / Alternative Laws

#[test]
fn test_monad_plus_left_identity() {
    fn monad_plus_left_identity(m: Maybe<i32>) -> TestResult {
        if m.is_nothing() {
            return TestResult::discard();
        }
        TestResult::from_bool(Maybe::<i32>::mzero().mplus(&m) == m)
    }
    quickcheck(monad_plus_left_identity as fn(Maybe<i32>) -> TestResult);
}

#[test]
fn test_monad_plus_right_identity() {
    fn monad_plus_right_identity(m: Maybe<i32>) -> TestResult {
        if m.is_nothing() {
            return TestResult::discard();
        }
        TestResult::from_bool(m.mplus(&Maybe::<i32>::mzero()) == m)
    }
    quickcheck(monad_plus_right_identity as fn(Maybe<i32>) -> TestResult);
}

#[test]
fn test_monad_plus_left_zero_for_bind() {
    fn left_zero(_: i32) -> bool {
        let f = |val: &i32| Just(*val + 1);
        Maybe::<i32>::mzero().bind(f) == Maybe::<i32>::mzero()
    }
    quickcheck(left_zero as fn(i32) -> bool);
}
