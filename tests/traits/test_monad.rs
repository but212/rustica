use super::TestFunctor;
use quickcheck_macros::quickcheck;
use rustica::traits::functor::Functor;
use rustica::traits::identity::Identity;
use rustica::traits::monad::Monad;
use rustica::traits::pure::Pure;

// Test basic Monad methods on Option
#[test]
fn test_option_monad_methods() {
    let some_value: Option<i32> = Some(42);
    let none_value: Option<i32> = None;

    // Test bind method
    let double = |x: &i32| Some(x * 2);
    assert_eq!(some_value.bind(double), Some(84));
    assert_eq!(none_value.bind(double), None);

    // Test bind_owned method
    assert_eq!(some_value.bind_owned(|x| Some(x * 2)), Some(84));
    assert_eq!(none_value.bind_owned(|x| Some(x * 2)), None);

    // Test join method
    let nested_some: Option<Option<i32>> = Some(Some(42));
    let nested_none: Option<Option<i32>> = Some(None);
    assert_eq!(nested_some.join::<i32>(), Some(42));
    assert_eq!(nested_none.join::<i32>(), None);

    // Test join_owned method
    let nested_some: Option<Option<i32>> = Some(Some(42));
    let nested_none: Option<Option<i32>> = Some(None);
    assert_eq!(nested_some.join_owned::<i32>(), Some(42));
    assert_eq!(nested_none.join_owned::<i32>(), None);

    // Test flat_map (alias for bind)
    assert_eq!(some_value.flat_map(double), Some(84));
    assert_eq!(none_value.flat_map(double), None);

    // Test flat_map_owned (alias for bind_owned)
    assert_eq!(some_value.flat_map_owned(|x| Some(x * 2)), Some(84));
    assert_eq!(none_value.flat_map_owned(|x| Some(x * 2)), None);

    // Test map_and_pure method
    assert_eq!(some_value.map_and_pure(|x| x * 2), Some(84));
    assert_eq!(none_value.map_and_pure(|x| x * 2), None);

    // Test try_bind method
    let default_value = 0;
    let success_fn = |x: &i32| Ok::<Option<i32>, &str>(Some(x * 2));
    let error_fn = |_: &i32| Err::<Option<i32>, &str>("Error");

    assert_eq!(some_value.try_bind(&default_value, success_fn), Some(84));
    assert_eq!(some_value.try_bind(&default_value, error_fn), Some(0));
    assert_eq!(none_value.try_bind(&default_value, success_fn), None);
}

// Test Monad methods on Result
#[test]
fn test_result_monad_methods() {
    let ok_value: Result<i32, &str> = Ok(42);
    let err_value: Result<i32, &str> = Err("error");

    // Test bind method
    let double = |x: &i32| Ok::<_, &str>(x * 2);
    assert_eq!(ok_value.bind(double), Ok(84));
    assert_eq!(err_value.bind(double), Err("error"));

    // Test bind_owned method
    assert_eq!(
        ok_value.bind_owned(|x| Ok::<_, &str>(x * 2)),
        Ok(84)
    );
    assert_eq!(
        err_value.bind_owned(|x| Ok::<_, &str>(x * 2)),
        Err("error")
    );

    // Test join method
    let nested_ok: Result<Result<i32, &str>, &str> = Ok(Ok(42));
    let nested_err_inner: Result<Result<i32, &str>, &str> = Ok(Err("inner error"));
    let nested_err_outer: Result<Result<i32, &str>, &str> = Err("outer error");

    assert_eq!(nested_ok.join::<i32>(), Ok(42));
    assert_eq!(nested_err_inner.join::<i32>(), Err("inner error"));
    assert_eq!(nested_err_outer.join::<i32>(), Err("outer error"));

    // Test join_owned method
    let nested_ok: Result<Result<i32, &str>, &str> = Ok(Ok(42));
    let nested_err_inner: Result<Result<i32, &str>, &str> = Ok(Err("inner error"));
    let nested_err_outer: Result<Result<i32, &str>, &str> = Err("outer error");

    assert_eq!(nested_ok.join_owned::<i32>(), Ok(42));
    assert_eq!(nested_err_inner.join_owned::<i32>(), Err("inner error"));
    assert_eq!(nested_err_outer.join_owned::<i32>(), Err("outer error"));

    // Test map_and_pure method
    assert_eq!(ok_value.map_and_pure(|x| x * 2), Ok(84));
    assert_eq!(err_value.map_and_pure(|x| x * 2), Err("error"));
}

// Test Monad Laws

// Left Identity Law: pure(a).bind(f) == f(a)
#[test]
fn monad_law_left_identity() {
    // Test with Option
    let value = 42;
    let f = |x: &i32| Some(x * 2);

    let left: Option<i32> = Option::<i32>::pure(&value).bind(f);
    let right = f(&value);

    assert_eq!(left, right);

    // Test with Result
    let value = 42;
    let f = |x: &i32| Ok::<i32, &str>(x * 2);

    let left: Result<i32, &str> = Result::<i32, &str>::pure(&value).bind(f);
    let right = f(&value);

    assert_eq!(left, right);
}

// Right Identity Law: m.bind(pure) == m
#[test]
fn monad_law_right_identity() {
    // Test with Option
    let m: Option<i32> = Some(42);

    let left = m.clone().bind(Option::<i32>::pure);

    assert_eq!(left, m);

    // Test with Result
    let m: Result<i32, &str> = Ok(42);

    let left = m.clone().bind(Result::<i32, &str>::pure);

    assert_eq!(left, m);
}

// Associativity Law: m.bind(f).bind(g) == m.bind(|x| f(x).bind(g))
#[test]
fn monad_law_associativity() {
    // Test with Option
    let m: Option<i32> = Some(42);
    let f = |x: &i32| Some(x * 2);
    let g = |x: &i32| Some(x + 10);

    let left = m.clone().bind(f).bind(g);
    let right = m.bind(|x| f(x).bind(g));

    assert_eq!(left, right);

    // Test with Result
    let m: Result<i32, &str> = Ok(42);
    let f = |x: &i32| Ok::<i32, &str>(x * 2);
    let g = |x: &i32| Ok::<i32, &str>(x + 10);

    let left = m.clone().bind(f).bind(g);
    let right = m.bind(|x| f(x).bind(g));

    assert_eq!(left, right);
}

// Applicative Consistency Law: m.bind(|x| pure(f(x))) == m.fmap(f)
#[test]
fn monad_law_applicative_consistency() {
    // Test with Option
    let m: Option<i32> = Some(42);
    let f = |x: &i32| x * 2;

    let left = m.clone().bind(|x| Option::<i32>::pure(&f(x)));
    let right = m.fmap(f);

    assert_eq!(left, right);

    // Test with Result
    let m: Result<i32, &str> = Ok(42);
    let f = |x: &i32| x * 2;

    let left = m.clone().bind(|x| Result::<i32, &str>::pure(&f(x)));
    let right = m.fmap(f);

    assert_eq!(left, right);
}

// QuickCheck properties for Monad laws

// Left Identity Law with QuickCheck
#[quickcheck]
fn quickcheck_monad_left_identity(x: i32) -> bool {
    let f = |x: &i32| Some(x.saturating_mul(2));

    let left: Option<i32> = Option::<i32>::pure(&x).bind(f);
    let right = f(&x);

    left == right
}

// Right Identity Law with QuickCheck
#[quickcheck]
fn quickcheck_monad_right_identity(x: i32) -> bool {
    let m: Option<i32> = Some(x);

    let left = m.clone().bind(Option::<i32>::pure);

    left == m
}

// Associativity Law with QuickCheck
#[quickcheck]
fn quickcheck_monad_associativity(x: i32) -> bool {
    let m: Option<i32> = Some(x);
    let f = |x: &i32| Some(x.saturating_mul(2));
    let g = |x: &i32| Some(x.saturating_add(10));

    let left = m.clone().bind(f).bind(g);
    let right = m.bind(|x| f(x).bind(g));

    left == right
}

// Applicative Consistency Law with QuickCheck
#[quickcheck]
fn quickcheck_monad_applicative_consistency(x: i32) -> bool {
    let m: Option<i32> = Some(x);
    let f = |x: &i32| x.saturating_mul(2);

    let left = m.clone().bind(|x| Option::<i32>::pure(&f(x)));
    let right = m.fmap(f);

    left == right
}

// Test custom TestFunctor Monad implementation
#[test]
fn test_custom_monad() {
    let functor = TestFunctor::new(42);

    // Test bind
    let result = functor.bind(|x| TestFunctor::new(x * 2));
    assert_eq!(*result.value(), 84);

    // Test bind_owned
    let result = functor.clone().bind_owned(|x| TestFunctor::new(x * 2));
    assert_eq!(*result.value(), 84);

    // Test join
    let nested = TestFunctor::new(TestFunctor::new(42));
    let result = nested.join::<i32>();
    assert_eq!(*result.value(), 42);

    // Test map_and_pure
    let result = functor.map_and_pure(|x| x * 2);
    assert_eq!(*result.value(), 84);
}
