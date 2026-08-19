use rustica::datatypes::wrapper::first::First;
use rustica::datatypes::wrapper::last::Last;
use rustica::datatypes::wrapper::max::Max;
use rustica::datatypes::wrapper::min::Min;
use rustica::datatypes::wrapper::predicate::Predicate;
use rustica::datatypes::wrapper::product::Product;
use rustica::datatypes::wrapper::sum::Sum;
use rustica::datatypes::wrapper::thunk::Thunk;
use rustica::prelude::*;
use rustica::traits::evaluate::Evaluate;
use std::sync::{Arc, Mutex};

#[test]
fn test_monoid_wrappers_behavior() {
    // 1. Optional Wrappers (First/Last)
    assert_eq!(First(Some(1)).combine(&First(Some(2))), First(Some(1)));
    assert_eq!(Last(Some(1)).combine(&Last(Some(2))), Last(Some(2)));
    assert_eq!(First::<i32>::empty(), First(None));

    // 2. Numeric Selection (Min/Max)
    assert_eq!(Min(10).combine(&Min(5)), Min(5));
    assert_eq!(Max(10).combine(&Max(5)), Max(10));
    assert_eq!(Min::<u32>::empty(), Min(0)); // Default min for unsigned

    // 3. Numeric Arithmetic (Sum/Product)
    assert_eq!(Sum(10).combine(&Sum(5)), Sum(15));
    assert_eq!(Product(10).combine(&Product(5)), Product(50));
    assert_eq!(Product::<i32>::empty(), Product(1));
}

#[test]
fn test_thunk_and_hkt_composition() {
    // 1. Thunk: Lazy evaluation and side-effect control
    let counter = Arc::new(Mutex::new(0));
    let thunk = Thunk::new(move || {
        let mut n = counter.lock().unwrap();
        *n += 1;
        *n
    });

    assert_eq!(thunk.evaluate(), 1);
    assert_eq!(thunk.evaluate(), 2);
    assert_eq!(thunk.evaluate_owned(), 3);

    // 2. HKT: Mapping over wrappers
    assert_eq!(Sum(42).fmap(|x| x.to_string()), Sum("42".to_string()));
    assert_eq!(First(Some(10)).fmap(|x| x * 2), First(Some(20)));

    // 3. Composition
    let sum_of_prods = Sum(Product(5).0).combine(&Sum(Product(10).0));
    assert_eq!(sum_of_prods, Sum(15));
}

#[test]
fn test_predicate_algebra_and_laws() {
    let is_even = Predicate::new(|x: &i32| *x % 2 == 0);
    let is_positive = Predicate::new(|x: &i32| *x > 0);

    // 1. Set Operations (Methods & Operators)
    let even_or_positive = is_even.union(&is_positive);
    let even_and_positive = is_even.intersection(&is_positive);
    let not_even = !is_even.clone();

    assert!(even_or_positive.contains(&-2)); // Even
    assert!(even_or_positive.contains(&3)); // Positive
    assert!(even_and_positive.contains(&2));
    assert!(!even_and_positive.contains(&3));
    assert!(not_even.contains(&3));

    // 2. Complex composition (A - B)
    let positive_odd = is_positive - is_even.clone();
    assert!(positive_odd.contains(&3));
    assert!(!positive_odd.contains(&2));
    assert!(!positive_odd.contains(&-1));

    // 3. Algebraic Laws (Identity)
    let empty = Predicate::<i32>::empty();
    assert_eq!(is_even.combine(&empty).contains(&2), is_even.contains(&2));
}

#[test]
fn test_wrapper_integration_use_cases() {
    let data = [1, 2, 3, 4, 5];

    // Aggregating with different Monoids
    let total = data
        .iter()
        .map(|&x| Sum(x))
        .fold(Sum::empty(), |acc, x| acc.combine(&x));
    let fact = data
        .iter()
        .map(|&x| Product(x))
        .fold(Product::empty(), |acc, x| acc.combine(&x));
    let minimum = data
        .iter()
        .map(|&x| Min(x))
        .fold(Min(i32::MAX), |acc, x| acc.combine(&x));

    assert_eq!(total, Sum(15));
    assert_eq!(fact, Product(120));
    assert_eq!(minimum, Min(1));

    // Optional stream processing
    let opts = [None, Some(42), Some(84)];
    let first = opts
        .iter()
        .filter_map(|&x| x)
        .map(|x| First(Some(x)))
        .fold(First::empty(), |acc, x| acc.combine(&x));
    assert_eq!(first, First(Some(42)));
}

#[cfg(feature = "serde")]
#[test]
fn test_wrapper_serialization() {
    use serde_json;
    let s = Sum(42);
    let json = serde_json::to_string(&s).unwrap();
    assert_eq!(serde_json::from_str::<Sum<i32>>(&json).unwrap(), s);
}
