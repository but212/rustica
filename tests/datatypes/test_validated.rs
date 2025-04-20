use rustica::datatypes::validated::Validated;
use rustica::prelude::*;
use rustica::traits::foldable::Foldable;
use rustica::traits::identity::Identity;

#[test]
fn test_validated_creation() {
    // Test valid creation
    let valid: Validated<String, i32> = Validated::valid(42);
    assert!(valid.is_valid());
    assert!(!valid.is_invalid());
    assert_eq!(valid.value(), &42);

    // Test invalid creation with a single error
    let invalid: Validated<&str, i32> = Validated::invalid("error");
    assert!(!invalid.is_valid());
    assert!(invalid.is_invalid());
    assert_eq!(invalid.errors().len(), 1);
    assert_eq!(invalid.errors()[0], "error");

    // Test invalid creation with multiple errors
    let multi_invalid: Validated<&str, i32> =
        Validated::invalid_many(["error1", "error2", "error3"]);
    assert!(multi_invalid.is_invalid());
    assert_eq!(multi_invalid.errors().len(), 3);
    assert_eq!(multi_invalid.errors()[0], "error1");
    assert_eq!(multi_invalid.errors()[1], "error2");
    assert_eq!(multi_invalid.errors()[2], "error3");
}

#[test]
fn test_validated_errors() {
    // Valid case should return empty errors
    let valid: Validated<String, i32> = Validated::valid(42);
    assert!(valid.errors().is_empty());

    // Invalid with single error
    let invalid: Validated<String, i32> = Validated::invalid("error".to_string());
    assert_eq!(invalid.errors().len(), 1);
    assert_eq!(invalid.errors()[0], "error");

    // Invalid with multiple errors
    let multi_invalid: Validated<String, i32> = Validated::invalid_many([
        "error1".to_string(),
        "error2".to_string(),
        "error3".to_string(),
    ]);
    assert_eq!(multi_invalid.errors().len(), 3);
    assert_eq!(multi_invalid.errors()[0], "error1");
    assert_eq!(multi_invalid.errors()[1], "error2");
    assert_eq!(multi_invalid.errors()[2], "error3");
}

#[test]
fn test_validated_functor() {
    // Test map on Valid
    let valid: Validated<String, i32> = Validated::valid(21);
    let mapped = valid.fmap(|x| x * 2);
    assert_eq!(mapped, Validated::valid(42));

    // Test map on Invalid
    let invalid: Validated<String, i32> = Validated::invalid("error".to_string());
    let mapped = invalid.fmap(|x| x * 2);
    assert_eq!(mapped, Validated::invalid("error".to_string()));

    // Test fmap_owned
    let valid: Validated<String, i32> = Validated::valid(21);
    let mapped = valid.fmap_owned(|x| x * 2);
    assert_eq!(mapped, Validated::valid(42));

    // Test fmap_invalid
    let invalid: Validated<&str, i32> = Validated::invalid("error");
    let mapped = invalid.fmap_invalid(|e| format!("Error: {}", e));
    assert_eq!(mapped, Validated::invalid("Error: error".to_string()));

    // Test fmap_invalid_owned
    let invalid: Validated<&str, i32> = Validated::invalid("error");
    let mapped = invalid.fmap_invalid_owned(|e| format!("Error: {}", e));
    assert_eq!(mapped, Validated::invalid("Error: error".to_string()));
}

#[test]
fn test_validated_applicative() {
    // Test apply Valid to Valid
    let value: Validated<String, i32> = Validated::valid(21);
    let f: Validated<String, fn(&i32) -> i32> = Validated::valid(|x| x * 2);
    let result = value.apply(&f);
    assert_eq!(result, Validated::valid(42));

    // Test apply Valid to Invalid
    let value: Validated<String, i32> = Validated::valid(21);
    let f: Validated<String, fn(&i32) -> i32> = Validated::invalid("error".to_string());
    let result = value.apply(&f);
    assert_eq!(result, Validated::invalid("error".to_string()));

    // Test apply Invalid to Valid
    let value: Validated<String, i32> = Validated::invalid("error".to_string());
    let f: Validated<String, fn(&i32) -> i32> = Validated::valid(|x| x * 2);
    let result = value.apply(&f);
    assert_eq!(result, Validated::invalid("error".to_string()));

    // Test apply Invalid to Invalid (error accumulation)
    let value: Validated<String, i32> = Validated::invalid("error1".to_string());
    let f: Validated<String, fn(&i32) -> i32> = Validated::invalid("error2".to_string());
    let result = value.apply(&f);
    let errors = result.errors();
    assert_eq!(errors.len(), 2);
    assert_eq!(errors[0], "error1");
    assert_eq!(errors[1], "error2");

    // Test pure
    let pure: Validated<String, i32> = Validated::<String, i32>::pure(&42);
    assert_eq!(pure, Validated::valid(42));

    // Test lift2
    let a: Validated<String, i32> = Validated::valid(10);
    let b: Validated<String, i32> = Validated::valid(32);
    let result = a.lift2(&b, |x, y| x + y);
    assert_eq!(result, Validated::valid(42));

    // Test lift3
    let a: Validated<String, i32> = Validated::valid(10);
    let b: Validated<String, i32> = Validated::valid(20);
    let c: Validated<String, i32> = Validated::valid(12);
    let result = a.lift3(&b, &c, |x, y, z| x + y + z);
    assert_eq!(result, Validated::valid(42));

    // Test lift3 with one Invalid
    let a: Validated<String, i32> = Validated::valid(10);
    let b: Validated<String, i32> = Validated::invalid("error".to_string());
    let c: Validated<String, i32> = Validated::valid(12);
    let result = a.lift3(&b, &c, |x, y, z| x + y + z);
    assert_eq!(result, Validated::invalid("error".to_string()));

    // Test lift3 with multiple Invalid (error accumulation)
    let a: Validated<String, i32> = Validated::invalid("error1".to_string());
    let b: Validated<String, i32> = Validated::invalid("error2".to_string());
    let c: Validated<String, i32> = Validated::invalid("error3".to_string());
    let result = a.lift3(&b, &c, |x, y, z| x + y + z);
    let errors = result.errors();
    assert_eq!(errors.len(), 3);
    assert_eq!(errors[0], "error1");
    assert_eq!(errors[1], "error2");
    assert_eq!(errors[2], "error3");
}

#[test]
fn test_validated_monad() {
    // Test bind with Valid
    let valid: Validated<String, i32> = Validated::valid(21);
    let result = valid.bind(|&x| Validated::valid(x * 2));
    assert_eq!(result, Validated::valid(42));

    // Test bind with Invalid
    let invalid: Validated<String, i32> = Validated::invalid("error".to_string());
    let result = invalid.bind(|&x| Validated::valid(x * 2));
    assert_eq!(result, Validated::invalid("error".to_string()));

    // Test compose
    let f = |x: &i32| Validated::<String, i32>::valid(x + 10);
    let g = |x: &i32| Validated::<String, i32>::valid(x * 2);
    let composed = |x: &i32| f(x).bind(|&y| g(&y));

    let result = composed(&11);
    assert_eq!(result, Validated::valid(42));

    // Test fold_left
    let valid: Validated<String, i32> = Validated::valid(21);
    let result = valid.fold_left(&0, |acc, x| acc + x);
    assert_eq!(result, 21);

    // Test fold_left with Invalid
    let invalid: Validated<String, i32> = Validated::invalid("error".to_string());
    let result = invalid.fold_left(&0, |acc, x| acc + x);
    assert_eq!(result, 0);
}

#[test]
fn test_validated_conversions() {
    // Test from_result with Ok
    let ok_result: Result<i32, &str> = Ok(42);
    let validated = Validated::from_result(&ok_result);
    assert!(validated.is_valid());
    assert_eq!(validated.value(), &42);

    // Test from_result with Err
    let err_result: Result<i32, &str> = Err("error");
    let validated = Validated::from_result(&err_result);
    assert!(validated.is_invalid());
    assert_eq!(validated.errors()[0], "error");

    // Test to_result with Valid
    let valid: Validated<&str, i32> = Validated::valid(42);
    let result = valid.to_result();
    assert!(result.is_ok());
    assert_eq!(result.ok().unwrap(), 42);

    // Test to_result with Invalid (single error)
    let invalid: Validated<&str, i32> = Validated::invalid("error");
    let result = invalid.to_result();
    assert!(result.is_err());
    let err_val = result.unwrap_err();
    assert_eq!(err_val, "error");

    // Test to_result with Invalid (multiple errors)
    let multi_invalid: Validated<&str, i32> = Validated::invalid_many(["error1", "error2"]);
    let result = multi_invalid.to_result();
    assert!(result.is_err());
    let err_val = result.unwrap_err();
    assert_eq!(err_val, "error1");

    // Test from_option with Some
    let some_value: Option<i32> = Some(42);
    let validated = Validated::from_option(&some_value, &"no value");
    assert_eq!(validated, Validated::valid(42));

    // Test from_option with None
    let none_value: Option<i32> = None;
    let validated = Validated::from_option(&none_value, &"no value");
    assert_eq!(validated, Validated::invalid("no value"));

    // Test to_option with Valid
    let valid: Validated<&str, i32> = Validated::valid(42);
    let option = valid.to_option();
    assert_eq!(option, Some(42));

    // Test to_option with Invalid
    let invalid: Validated<&str, i32> = Validated::invalid("error");
    let option = invalid.to_option();
    assert_eq!(option, None);
}

#[test]
fn test_validated_error_accumulation() {
    // Test combining single errors
    let error1: Validated<&str, i32> = Validated::invalid("error1");
    let error2: Validated<&str, i32> = Validated::invalid("error2");

    // Using applicative apply for combination
    let f: Validated<&str, fn(&i32) -> i32> = Validated::valid(|a| a * 2);
    let result = error1.apply(&f);
    let result = result.ap2(&error2, |f_result, b| f_result + b);

    let errors = result.errors();
    assert_eq!(errors.len(), 2);
    assert_eq!(errors[0], "error1");
    assert_eq!(errors[1], "error2");

    // Test nested error accumulation
    let a = Validated::invalid("error1");
    let b = Validated::invalid("error2");
    let c = Validated::invalid("error3");

    let result = a.lift3(&b, &c, |x: &i32, y: &i32, z: &i32| x + y + z);
    let errors = result.errors();
    assert_eq!(errors.len(), 3);
    assert_eq!(errors[0], "error1");
    assert_eq!(errors[1], "error2");
    assert_eq!(errors[2], "error3");
}

#[test]
fn test_validated_unwrap_or_methods() {
    // Test unwrap_or with Valid
    let valid: Validated<&str, i32> = Validated::valid(42);
    assert_eq!(valid.unwrap_or(&0), 42);

    // Test unwrap_or with Invalid
    let invalid: Validated<&str, i32> = Validated::invalid("error");
    assert_eq!(invalid.unwrap_or(&0), 0);
}

#[test]
fn test_validated_real_world_scenario() {
    // Define validation functions
    fn validate_name(name: &str) -> Validated<String, String> {
        if name.trim().is_empty() {
            Validated::invalid("Name must not be empty".to_string())
        } else if name.len() < 2 {
            Validated::invalid("Name must be at least 2 characters".to_string())
        } else {
            Validated::valid(name.to_string())
        }
    }

    fn validate_age(age: i32) -> Validated<String, i32> {
        if age < 0 {
            Validated::invalid("Age must be positive".to_string())
        } else if age < 18 {
            Validated::invalid("Age must be at least 18".to_string())
        } else {
            Validated::valid(age)
        }
    }

    fn validate_email(email: &str) -> Validated<String, String> {
        if !email.contains('@') {
            Validated::invalid("Email must contain @ symbol".to_string())
        } else {
            Validated::valid(email.to_string())
        }
    }

    // Valid inputs
    let valid_name = validate_name("John Doe");
    let valid_age = validate_age(25);
    let valid_email = validate_email("john@example.com");

    // Combine validations using applicative style
    let valid_user = valid_name.lift3(&valid_age, &valid_email, |name, age, email| {
        format!("{} ({}): {}", name, age, email)
    });

    assert!(valid_user.is_valid());
    assert_eq!(valid_user.value(), &"John Doe (25): john@example.com");

    // Invalid inputs
    let invalid_name = validate_name("");
    let invalid_age = validate_age(15);
    let invalid_email = validate_email("not-an-email");

    // Combine validations to get all errors
    let invalid_user = invalid_name.lift3(&invalid_age, &invalid_email, |name, age, email| {
        format!("{} ({}): {}", name, age, email)
    });

    assert!(invalid_user.is_invalid());

    let errors = invalid_user.errors();
    assert_eq!(errors.len(), 3);
    assert_eq!(errors[0], "Name must not be empty");
    assert_eq!(errors[1], "Age must be at least 18");
    assert_eq!(errors[2], "Email must contain @ symbol");
}

#[test]
fn test_validated_edge_cases() {
    use rustica::datatypes::validated::Validated;
    // Empty error vector (invalid_many with empty)
    let empty: Validated<String, i32> = Validated::invalid_many(Vec::<String>::new());
    assert!(empty.is_invalid());
    assert!(empty.errors().is_empty());
    // Large error vector
    let many: Vec<_> = (0..100).map(|i| format!("err{i}")).collect();
    let large: Validated<String, i32> = Validated::invalid_many(many.clone());
    assert_eq!(large.errors().len(), 100);
    assert_eq!(large.errors()[0], "err0");
    assert_eq!(large.errors()[99], "err99");
}

#[test]
fn test_validated_fmap_invalid_multiple() {
    use rustica::datatypes::validated::Validated;
    let multi: Validated<&str, i32> = Validated::invalid_many(["e1", "e2"]);
    let mapped = multi.fmap_invalid(|e| format!("Err: {e}"));
    assert_eq!(
        mapped.errors(),
        &["Err: e1".to_string(), "Err: e2".to_string()]
    );
    let mapped_owned = multi.fmap_invalid_owned(|e| format!("Err: {e}"));
    assert_eq!(
        mapped_owned.errors(),
        &["Err: e1".to_string(), "Err: e2".to_string()]
    );
}

#[test]
fn test_validated_apply_owned() {
    use rustica::datatypes::validated::Validated;
    let value: Validated<String, i32> = Validated::valid(10);
    let f: Validated<String, fn(i32) -> i32> = Validated::valid(|x| x + 1);
    let applied = value.clone().apply_owned(f.clone());
    assert_eq!(applied, Validated::valid(11));
    let invalid: Validated<String, i32> = Validated::invalid("err".to_string());
    let applied = invalid.clone().apply_owned(f.clone());
    assert!(applied.is_invalid());
    let applied: Validated<String, i32> =
        value.apply_owned::<i32, fn(i32) -> i32>(Validated::invalid("err2".to_string()));
    assert!(applied.is_invalid());
}

#[test]
fn test_validated_iterators_and_collections() {
    use rustica::datatypes::validated::Validated;
    let valid: Validated<String, i32> = Validated::valid(1);
    let vals: Vec<_> = valid.iter().cloned().collect();
    assert_eq!(vals, vec![1]);
    let invalid: Validated<String, i32> =
        Validated::invalid_many(["e1".to_string(), "e2".to_string()]);
    let errs: Vec<_> = invalid.iter_errors().cloned().collect();
    assert_eq!(errs, vec!["e1".to_string(), "e2".to_string()]);
}

#[test]
fn test_validated_foldable_and_identity() {
    use rustica::datatypes::validated::Validated;
    use rustica::traits::foldable::Foldable;
    use rustica::traits::identity::Identity;
    let valid: Validated<String, i32> = Validated::valid(5);
    let sum = valid.fold_left(&0, |acc, x| acc + x);
    assert_eq!(sum, 5);
    let prod = valid.fold_right(&1, |x, acc| x * acc);
    assert_eq!(prod, 5);
    assert_eq!(valid.value(), &5);
    assert_eq!(valid.into_value(), 5);
    let pure: Validated<String, i32> = Validated::<String, i32>::pure_identity(42);
    assert_eq!(pure, Validated::valid(42));
}

#[test]
fn test_validated_laws() {
    use rustica::datatypes::validated::Validated;
    use rustica::traits::applicative::Applicative;
    use rustica::traits::functor::Functor;
    use rustica::traits::monad::Monad;
    // Functor identity
    let v: Validated<String, i32> = Validated::valid(5);
    assert_eq!(v.fmap(|x| *x), v);
    // Functor composition
    let f = |x: &i32| x + 1;
    let g = |x: &i32| x * 2;
    let comp1 = v.fmap(|x| f(&g(x)));
    let comp2 = v.fmap(g).fmap(f);
    assert_eq!(comp1, comp2);
    // Applicative identity
    let id_fn = |x: &i32| *x;
    let id_app = Validated::valid(id_fn);
    let applied = v.apply(&id_app);
    assert_eq!(applied, v);
    // Monad left identity
    let a = 42;
    let f = |x: &i32| Validated::valid(*x + 1);
    let left = Validated::<String, i32>::pure(&a).bind(f);
    let right = f(&a);
    assert_eq!(left, right);
    // Monad right identity
    let m = Validated::<String, i32>::valid(1);
    let right = m.bind(|x| Validated::<String, i32>::pure(x));
    assert_eq!(right, m);
    // Monad associativity
    let f = |x: &i32| Validated::<String, i32>::valid(x + 1);
    let g = |x: &i32| Validated::<String, i32>::valid(x * 2);
    let m = Validated::<String, i32>::valid(10);

    let left = m.bind(f).bind(g);
    let right = m.bind(|x| f(x).bind(g));
    assert_eq!(left, right);

    // Corrected test with consistent results
    let composed = |x: &i32| f(x).bind(|&y| g(&y));
    let result = composed(&11);
    assert_eq!(result, Validated::valid(24));

    // Test fold_left
    let valid: Validated<String, i32> = Validated::valid(21);
    let result = valid.fold_left(&0, |acc, x| acc + x);
    assert_eq!(result, 21);

    // Test fold_left with Invalid
    let invalid: Validated<String, i32> = Validated::invalid("error".to_string());
    let result = invalid.fold_left(&0, |acc, x| acc + x);
    assert_eq!(result, 0);
}

#[test]
fn test_validated_equality_and_ordering() {
    use rustica::datatypes::validated::Validated;
    let v1 = Validated::<String, i32>::valid(1);
    let v2 = Validated::<String, i32>::valid(1);
    let v3 = Validated::<String, i32>::valid(2);
    assert_eq!(v1, v2);
    assert_ne!(v1, v3);
    let i1 = Validated::<String, i32>::invalid("e".to_string());
    let i2 = Validated::<String, i32>::invalid("e".to_string());
    let i3 = Validated::<String, i32>::invalid("e2".to_string());
    assert_eq!(i1, i2);
    assert_ne!(i1, i3);
}

#[test]
fn test_validated_unwrap_and_expect() {
    use rustica::datatypes::validated::Validated;
    let v = Validated::<String, i32>::valid(42);
    assert_eq!(v.unwrap(), 42);
    let i: Validated<String, i32> = Validated::<String, i32>::invalid("err".to_string());
    let result = std::panic::catch_unwind(|| i.unwrap());
    assert!(result.is_err());
    let v = Validated::<String, i32>::valid(7);
    assert_eq!(v.unwrap(), 7);
}

#[test]
fn test_validated_invalid_vec_panics_on_empty() {
    use std::panic;
    let result = panic::catch_unwind(|| {
        Validated::<&str, i32>::invalid_vec(Vec::<&str>::new());
    });
    assert!(result.is_err());
}

#[test]
fn test_validated_unwrap_invalid_panics_on_valid() {
    use std::panic;
    let valid = Validated::<&str, i32>::valid(1);
    let result = panic::catch_unwind(|| {
        valid.unwrap_invalid();
    });
    assert!(result.is_err());
}

#[test]
fn test_validated_iterators() {
    let valid = Validated::<&str, i32>::valid(42);
    let invalid = Validated::<&str, i32>::invalid("err");
    // iter
    let vals: Vec<_> = valid.iter().collect();
    assert_eq!(vals, vec![&42]);
    let vals: Vec<_> = invalid.iter().collect();
    assert!(vals.is_empty());
    // iter_mut
    let mut valid2 = Validated::<&str, i32>::valid(100);
    let mut invalid2 = Validated::<&str, i32>::invalid("err2");
    let vals: Vec<_> = valid2.iter_mut().collect();
    assert_eq!(vals.len(), 1);
    let vals: Vec<_> = invalid2.iter_mut().collect();
    assert!(vals.is_empty());
    // iter_errors
    let errs: Vec<_> = invalid.iter_errors().collect();
    assert_eq!(errs, vec![&"err"]);
    let errs: Vec<_> = valid.iter_errors().collect();
    assert!(errs.is_empty());
    // iter_errors_mut
    let mut invalid3 = Validated::<&str, i32>::invalid("err3");
    let errs: Vec<_> = invalid3.iter_errors_mut().collect();
    assert_eq!(errs.len(), 1);
}

#[test]
fn test_validated_trait_laws() {
    use rustica::traits::applicative::Applicative;
    use rustica::traits::functor::Functor;
    use rustica::traits::monad::Monad;
    // Functor identity
    let v: Validated<String, i32> = Validated::valid(5);
    assert_eq!(v.fmap(|x| *x), v);
    // Functor composition
    let f = |x: &i32| x + 1;
    let g = |x: &i32| x * 2;
    let lhs = v.fmap(|x| f(&g(x)));
    let rhs = v.fmap(g).fmap(f);
    assert_eq!(lhs, rhs);
    // Applicative identity
    let u: Validated<String, fn(&i32) -> i32> = Validated::valid(|x| *x);
    let a = Validated::valid(7);
    assert_eq!(a.apply(&u), a);
    // Applicative homomorphism
    let f = |x: &i32| x + 1;
    let a: Validated<String, i32> = Validated::valid(3);
    let u = Validated::valid(f);
    assert_eq!(a.apply(&u), Validated::valid(f(&3)));
    // Monad left identity
    let f = |x: &i32| Validated::<String, i32>::valid(x * 2);
    let a = 10;
    assert_eq!(Validated::valid(a).bind(f), f(&a));
    // Monad right identity
    let m = Validated::<String, i32>::valid(9);
    assert_eq!(m.bind(|x| Validated::valid(*x)), m);
    // Monad associativity
    let m = Validated::<String, i32>::valid(5);
    let f = |x: &i32| Validated::<String, i32>::valid(x + 1);
    let g = |x: &i32| Validated::<String, i32>::valid(x * 2);
    let lhs = m.bind(f).bind(g);
    let rhs = m.bind(|x| f(x).bind(g));
    assert_eq!(lhs, rhs);
}
