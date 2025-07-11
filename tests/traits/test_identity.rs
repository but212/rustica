use super::TestFunctor;
use quickcheck::TestResult;
use quickcheck_macros::quickcheck;
use rustica::traits::functor::Functor;
use rustica::traits::identity::Identity;

// Test basic Identity methods on TestFunctor
#[test]
fn test_identity_basic_methods() {
    let test_value = 42;
    let functor = TestFunctor::new(test_value);

    // Test value method
    assert_eq!(*functor.value(), test_value);

    // Test into_value method
    assert_eq!(functor.into_value(), test_value);

    // Test pure_identity method
    let created = TestFunctor::<i32>::pure_identity(test_value);
    assert_eq!(*created.value(), test_value);

    // Test id function
    let x = 10;
    assert_eq!(<TestFunctor<i32> as Identity>::id(x), x);
}

// Test try_value and try_into_value on Option
#[test]
fn test_option_identity_methods() {
    let some_value: Option<i32> = Some(42);
    let none_value: Option<i32> = None;

    // Test try_value
    assert_eq!(some_value.try_value(), Some(&42));
    assert_eq!(none_value.try_value(), None);

    // Test try_into_value
    assert_eq!(some_value.try_into_value(), Some(42));
    assert_eq!(none_value.try_into_value(), None);

    // Test pure_identity
    let created = Option::<i32>::pure_identity(42);
    assert_eq!(created, Some(42));
}

// Test try_value and try_into_value on Result
#[test]
fn test_result_identity_methods() {
    let ok_value: Result<i32, &str> = Ok(42);
    let err_value: Result<i32, &str> = Err("error");

    // Test try_value
    assert_eq!(ok_value.try_value(), Some(&42));
    assert_eq!(err_value.try_value(), None);

    // Test try_into_value
    let ok_value: Result<i32, &str> = Ok(42);
    let err_value: Result<i32, &str> = Err("error");
    assert_eq!(ok_value.try_into_value(), Some(42));
    assert_eq!(err_value.try_into_value(), None);

    // Test pure_identity
    let created = Result::<i32, &str>::pure_identity(42);
    assert_eq!(created, Ok(42));
}

// Test Identity Laws

// Left Identity Law: identity.pure_identity(a).transform(f) == f(a)
#[quickcheck]
fn identity_law_left_identity(x: i32) -> bool {
    // Use a safe function that won't overflow for large values
    let f = |x: &i32| x.saturating_mul(2);
    let left = TestFunctor::<i32>::pure_identity(x).fmap(f);
    let right = f(&x);

    *left.value() == right
}

// Right Identity Law: identity.transform(Identity::id) == identity
#[test]
fn identity_law_right_identity() {
    let x = TestFunctor::new(42);

    // We need to use a fully-qualified path for Identity::id
    // Use the identity function with the specific type implementation
    let left = x
        .clone()
        .fmap(|val| <TestFunctor<i32> as Identity>::id(*val));

    assert_eq!(left, x);
}

// Test map_or_else for Option and TestFunctor with quickcheck
#[quickcheck]
fn prop_option_map_or_else_some(x: i32) -> bool {
    let some_value = Some(x);
    let result = some_value.map_or_else(|| 0, |x| x.saturating_mul(2));
    result == x.saturating_mul(2)
}

#[quickcheck]
fn prop_option_map_or_else_none() -> bool {
    let none_value: Option<i32> = None;
    let result = none_value.map_or_else(|| 0, |x| x.saturating_mul(2));
    result == 0
}

// Test Vec implementation of Identity with quickcheck
#[quickcheck]
fn prop_vec_identity_with_elements(xs: Vec<i32>) -> TestResult {
    if xs.is_empty() {
        return TestResult::discard();
    }
    let vec_with_elements = xs.clone();
    // value() and into_value() should both return the first element
    let v = *vec_with_elements.value();
    let v2 = vec_with_elements.clone().into_value();
    TestResult::from_bool(v == xs[0] && v2 == xs[0])
}

#[quickcheck]
fn prop_vec_identity_empty() -> bool {
    let empty_vec: Vec<i32> = vec![];
    empty_vec.try_value().is_none() && empty_vec.try_into_value().is_none()
}

#[quickcheck]
fn prop_vec_pure_identity(x: i32) -> bool {
    let created_vec = Vec::<i32>::pure_identity(x);
    created_vec == vec![x]
}
