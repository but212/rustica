use quickcheck::{TestResult, quickcheck};
use rustica::datatypes::maybe::{Maybe, Maybe::*, MaybeError};
use rustica::traits::alternative::Alternative;
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

// ---------------- Additional direct unit tests ----------------

#[test]
fn test_construction_aliases() {
    let j = Maybe::some(5);
    let n: Maybe<i32> = Maybe::none();
    let w_true = Maybe::when(true, 7);
    let w_false = Maybe::when(false, 7);

    assert_eq!(j, Just(5));
    assert!(n.is_nothing());
    assert_eq!(w_true, Just(7));
    assert_eq!(w_false, Nothing);
}

#[test]
fn test_predicates_and_as_ref_to_option() {
    let j = Just(10);
    let n: Maybe<i32> = Nothing;

    assert!(j.is_just());
    assert!(n.is_nothing());
    assert_eq!(j.as_ref(), Some(&10));
    assert_eq!(n.as_ref(), None);
    assert_eq!(j.to_option(), Some(10));
    assert_eq!(n.to_option(), None);
}

#[test]
fn test_unwrap_variants() {
    let j = Just(42);
    let n: Maybe<i32> = Nothing;

    assert_eq!(j.unwrap_or(0), 42);
    assert_eq!(n.unwrap_or(0), 0);
    assert_eq!(j.unwrap_or_else(|| 10), 42);
    assert_eq!(n.unwrap_or_else(|| 10), 10);
}

#[test]
#[should_panic(expected = "Maybe::unwrap()")]
fn test_unwrap_panics_on_nothing() {
    let n: Maybe<i32> = Nothing;
    let _ = n.unwrap();
}

#[test]
fn test_fmap_and_fmap_owned() {
    let j = Just(String::from("hi"));
    let n: Maybe<String> = Nothing;

    assert_eq!(j.fmap(|s| s.len()), Just(2usize));
    assert_eq!(n.fmap(|s| s.len()), Nothing);

    let j2 = Just(String::from("abc"));
    assert_eq!(j2.fmap_owned(|s| s + "!"), Just(String::from("abc!")));
    let n2: Maybe<String> = Nothing;
    assert_eq!(n2.fmap_owned(|s| s + "!"), Nothing);
}

#[test]
fn test_bind_and_bind_owned() {
    let j = Just(3);
    let n: Maybe<i32> = Nothing;

    let f = |x: &i32| if *x % 2 == 1 { Just(x * 10) } else { Nothing };
    assert_eq!(j.bind(f), Just(30));
    assert_eq!(n.bind(f), Nothing);

    let j2 = Just(String::from("ab"));
    let g = |s: String| if s.len() == 2 { Just(s + "c") } else { Nothing };
    assert_eq!(j2.bind_owned(g), Just(String::from("abc")));
}

#[test]
fn test_join_and_join_owned() {
    let nested = Just(Just(9));
    assert_eq!(nested.join(), Just(9));

    let nested2 = Just(Just(String::from("x")));
    assert_eq!(nested2.join_owned(), Just(String::from("x")));

    let inner_nothing: Maybe<Maybe<i32>> = Just(Nothing);
    let outer_nothing: Maybe<Maybe<i32>> = Nothing;
    assert_eq!(inner_nothing.join(), Nothing);
    assert_eq!(outer_nothing.join(), Nothing);
}

#[test]
fn test_fmap_or_and_filter_and_tap() {
    let j = Just(41);
    let n: Maybe<i32> = Nothing;
    assert_eq!(j.fmap_or(0, |x| x + 1), 42);
    assert_eq!(n.fmap_or(0, |x| x + 1), 0);

    assert_eq!(j.filter(|&x| x > 40), Just(41));
    assert_eq!(j.filter(|&x| x > 100), Nothing);
    assert_eq!(n.filter(|&x| x > 0), Nothing);

    use std::cell::RefCell;
    let acc = RefCell::new(0);
    let _ = Just(5).tap(|x| *acc.borrow_mut() += *x);
    let _ = Nothing::<i32>.tap(|x| *acc.borrow_mut() += *x);
    assert_eq!(*acc.borrow(), 5);
}

#[test]
fn test_iterators_and_to_vec() {
    let mut j = Just(2);
    let n: Maybe<i32> = Nothing;

    // iter
    assert_eq!(j.iter().copied().collect::<Vec<_>>(), vec![2]);
    assert!(n.iter().next().is_none());

    // iter_mut
    for v in j.iter_mut() {
        *v += 5;
    }
    assert_eq!(j, Just(7));

    // owned IntoIterator
    let it: Vec<_> = Just(1).into_iter().collect();
    assert_eq!(it, vec![1]);
    assert!(n.into_iter().next().is_none());

    // to_vec
    let j2 = Just(3);
    let n2: Maybe<i32> = Nothing;
    assert_eq!(j2.to_vec(), vec![3]);
    assert!(n2.to_vec().is_empty());
}

#[test]
fn test_conversions_option_result_and_from_iterator() {
    // Option <-> Maybe
    assert_eq!(Maybe::from_option(Some(4)), Just(4));
    let none_opt: Option<i32> = None;
    assert_eq!(Maybe::from_option(none_opt), Nothing);

    let j = Just(10);
    let n: Maybe<i32> = Nothing;
    assert_eq!(j.to_option(), Some(10));
    assert_eq!(n.to_option(), None);

    // From<Result>
    let ok: Result<i32, &str> = Ok(7);
    let err: Result<i32, &str> = Err("e");
    assert_eq!(Maybe::from(ok), Just(7));
    assert_eq!(Maybe::from(err), Nothing);

    // IntoIterator/FromIterator: first element
    let v = vec![9, 8, 7];
    let m: Maybe<i32> = v.into_iter().collect();
    assert_eq!(m, Just(9));

    let v2: Vec<i32> = vec![];
    let m2: Maybe<i32> = v2.into_iter().collect();
    assert_eq!(m2, Nothing);
}

#[test]
fn test_with_error_and_standard_result() {
    let j = Just(1);
    let n: Maybe<i32> = Nothing;

    // inherent to_result with custom error
    assert_eq!(j.to_result("err"), Ok(1));
    assert_eq!(n.to_result("err"), Err("err"));

    // to_standard_result (built-in MaybeError)
    let j_ok: Result<i32, MaybeError> = j.to_standard_result();
    assert_eq!(j_ok, Ok(1));
    let n_err: Result<i32, MaybeError> = n.to_standard_result();
    assert_eq!(n_err, Err(MaybeError::ValueNotPresent));

    // to_standard_result
    let j_ok2 = Just(2).to_standard_result();
    let n_err2: Result<i32, MaybeError> = Nothing.to_standard_result();
    assert_eq!(j_ok2, Ok(2));
    assert_eq!(n_err2, Err(MaybeError::ValueNotPresent));
}

#[test]
fn test_alternative_and_monadplus() {
    // empty/guard
    assert_eq!(Maybe::<i32>::empty_alt::<i32>(), Nothing);
    assert_eq!(Maybe::<i32>::guard(true), Just(()));
    assert_eq!(Maybe::<i32>::guard(false), Nothing);

    // alt/mplus prefer first Just
    let a = Just(1);
    let b = Just(2);
    let n: Maybe<i32> = Nothing;
    assert_eq!(a.alt(&b), a);
    assert_eq!(a.alt(&n), a);
    assert_eq!(n.alt(&b), b);
    assert_eq!(n.alt(&n), n);

    assert_eq!(Maybe::<i32>::mzero::<i32>(), Nothing);
    assert_eq!(a.mplus(&b), a);
    assert_eq!(a.mplus(&n), a);
    assert_eq!(n.mplus(&b), b);
    assert_eq!(n.mplus(&n), n);

    // mplus_owned
    assert_eq!(a.clone().mplus_owned(b.clone()), a);
    assert_eq!(n.clone().mplus_owned(b.clone()), b);
}

#[test]
#[should_panic(expected = "called `Maybe::unwrap()` on a `Nothing` value")]
fn test_identity_value_panics_on_nothing() {
    let n: Maybe<i32> = Nothing;
    let _ = n.unwrap();
}

#[test]
fn test_try_unwrap_success_and_error() {
    let j = Just(3);
    let n: Maybe<i32> = Nothing;
    assert_eq!(j.try_unwrap().unwrap(), 3);
    let err = n.try_unwrap().unwrap_err();
    let msg = format!("{}", err);
    assert!(msg.contains("Cannot unwrap Nothing value"));
}

#[test]
fn test_immutability() {
    let orig = Just(5);
    let mapped = orig.fmap(|x| x + 1);
    // ensure orig unchanged
    assert_eq!(orig, Just(5));
    assert_eq!(mapped, Just(6));

    let bound = orig.bind(|x| if *x > 0 { Just(x + 1) } else { Nothing });
    assert_eq!(orig, Just(5));
    assert_eq!(bound, Just(6));
}

#[cfg(feature = "serde")]
#[test]
fn test_maybe_serde() {
    use rustica::datatypes::maybe::Maybe;
    use serde_json;

    // Test with a Just value
    let just: Maybe<i32> = Maybe::Just(42);
    let serialized_just = serde_json::to_string(&just).unwrap();
    let deserialized_just: Maybe<i32> = serde_json::from_str(&serialized_just).unwrap();
    assert_eq!(just, deserialized_just);

    // Test with a Nothing value
    let nothing: Maybe<i32> = Maybe::Nothing;
    let serialized_nothing = serde_json::to_string(&nothing).unwrap();
    let deserialized_nothing: Maybe<i32> = serde_json::from_str(&serialized_nothing).unwrap();
    assert_eq!(nothing, deserialized_nothing);

    // Test with a struct
    #[derive(serde::Serialize, serde::Deserialize, PartialEq, Debug, Clone)]
    struct Point {
        x: i32,
        y: i32,
    }
    let point = Point { x: 1, y: 2 };
    let just_point = Maybe::Just(point.clone());
    let serialized_point = serde_json::to_string(&just_point).unwrap();
    let deserialized_point: Maybe<Point> = serde_json::from_str(&serialized_point).unwrap();
    assert_eq!(just_point, deserialized_point);
}
