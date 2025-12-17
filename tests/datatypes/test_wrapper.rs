use rustica::datatypes::wrapper::first::First;
use rustica::datatypes::wrapper::last::Last;
use rustica::datatypes::wrapper::max::Max;
use rustica::datatypes::wrapper::memoizer::Memoizer;
use rustica::datatypes::wrapper::min::Min;
use rustica::datatypes::wrapper::product::Product;
use rustica::datatypes::wrapper::sum::Sum;
use rustica::datatypes::wrapper::thunk::Thunk;
use rustica::prelude::*;
use rustica::traits::evaluate::Evaluate;
use std::sync::{Arc, Mutex};
use std::thread;

#[test]
fn test_first_wrapper() {
    // Test First creation and access
    let first_some = First(Some(42));
    let first_none = First(None);

    // Test semigroup combine
    let combined = first_some.combine(&First(Some(84)));
    assert_eq!(combined, First(Some(42)));

    // Test combining with None
    let combined_with_none = first_none.clone().combine(&first_some);
    assert_eq!(combined_with_none, first_some);
    let combined_with_none = first_some.combine(&first_none);
    assert_eq!(combined_with_none, first_some);

    // Test monoid empty
    let empty = First::<i32>::empty();
    assert_eq!(empty, First(None));
}

#[test]
fn test_last_wrapper() {
    // Test Last creation and access
    let last_some = Last(Some(42));
    let last_none = Last(None);

    // Test semigroup combine
    let combined = last_some.combine(&Last(Some(84)));
    assert_eq!(combined, Last(Some(84)));

    // Test combining with None
    let combined_with_none = last_none.clone().combine(&last_some);
    assert_eq!(combined_with_none, last_some);
    let combined_with_none = last_some.combine(&last_none);
    assert_eq!(combined_with_none, last_some);

    // Test monoid empty
    let empty = Last::<i32>::empty();
    assert_eq!(empty, Last(None));
}

#[test]
fn test_min_wrapper() {
    // Test Min creation and access
    let min1 = Min(10);
    let min2 = Min(5);
    let min3 = Min(15);

    // Test semigroup combine
    let combined = min1.combine(&min2);
    assert_eq!(combined, Min(5));
    let combined = min2.combine(&min3);
    assert_eq!(combined, Min(5));
    let combined = min1.combine(&min3);
    assert_eq!(combined, Min(10));

    // Test monoid empty for u32 (default is 0, which is the min)
    let empty = Min::<u32>::empty();
    assert_eq!(empty, Min(0));
}

#[test]
fn test_max_wrapper() {
    // Test Max creation and access
    let max1 = Max(10);
    let max2 = Max(5);
    let max3 = Max(15);

    // Test semigroup combine
    let combined = max1.combine(&max2);
    assert_eq!(combined, Max(10));
    let combined = max2.combine(&max3);
    assert_eq!(combined, Max(15));
    let combined = max1.combine(&max3);
    assert_eq!(combined, Max(15));

    // Test monoid empty for u32 (default is 0)
    let empty = Max::<u32>::empty();
    assert_eq!(empty, Max(0));
}

#[test]
fn test_sum_wrapper() {
    // Test Sum creation and access
    let sum1 = Sum(10);
    let sum2 = Sum(5);
    let sum3 = Sum(15);

    // Test semigroup combine
    let combined = sum1.combine(&sum2);
    assert_eq!(combined, Sum(15));
    let combined = sum2.combine(&sum3);
    assert_eq!(combined, Sum(20));
    let combined = sum1.combine(&sum3);
    assert_eq!(combined, Sum(25));

    // Test monoid empty
    let empty = Sum::<i32>::empty();
    assert_eq!(empty, Sum(0));
}

#[test]
fn test_product_wrapper() {
    // Test Product creation and access
    let prod1 = Product(10);
    let prod2 = Product(5);
    let prod3 = Product(2);

    // Test semigroup combine
    let combined = prod1.combine(&prod2);
    assert_eq!(combined, Product(50));
    let combined = prod2.combine(&prod3);
    assert_eq!(combined, Product(10));
    let combined = prod1.combine(&prod3);
    assert_eq!(combined, Product(20));

    // Test monoid empty
    let empty = Product::<i32>::empty();
    assert_eq!(empty, Product(1));
}

#[test]
fn test_thunk_wrapper() {
    // Test Thunk creation and evaluation
    let counter = Arc::new(Mutex::new(0));
    let counter_clone = counter.clone();

    let thunk = Thunk::new(move || {
        let mut count = counter_clone.lock().unwrap();
        *count += 1;
        *count
    });

    // First evaluation should increment counter to 1
    assert_eq!(thunk.evaluate(), 1);
    // Second evaluation should increment counter to 2
    assert_eq!(thunk.evaluate(), 2);

    // Test evaluate_owned
    let counter = Arc::new(Mutex::new(0));
    let counter_clone = counter.clone();

    let thunk = Thunk::new(move || {
        let mut count = counter_clone.lock().unwrap();
        *count += 1;
        *count
    });

    // Consume the thunk
    assert_eq!(thunk.evaluate_owned(), 1);
}

#[test]
fn test_memoizer_basic() {
    let counter = Arc::new(Mutex::new(0));
    let counter_clone = counter.clone();
    let memoizer = Memoizer::new();
    // First call should compute the value
    let v1 = memoizer.get_or_compute((), |_| {
        let mut count = counter_clone.lock().unwrap();
        *count += 1;
        *count
    });
    assert_eq!(v1, 1);
    // Second call should use cache
    let v2 = memoizer.get_or_compute((), |_| unreachable!());
    assert_eq!(v2, 1);
    assert_eq!(*counter.lock().unwrap(), 1);
    // Clear cache and recompute
    memoizer.clear();
    let v3 = memoizer.get_or_compute((), |_| {
        let mut count = counter.lock().unwrap();
        *count += 1;
        *count
    });
    assert_eq!(v3, 2);
}

#[test]
fn test_memoizer_fn() {
    let counter = Arc::new(Mutex::new(0));
    let counter_clone = counter.clone();
    let memoizer = Memoizer::new();
    // First call with value
    let v1 = memoizer.get_or_compute(5, |_| {
        let mut count = counter_clone.lock().unwrap();
        *count += 1;
        10
    });
    assert_eq!(v1, 10);
    // Second call with same value uses cache
    let v2 = memoizer.get_or_compute(5, |_| unreachable!());
    assert_eq!(v2, 10);
    assert_eq!(*counter.lock().unwrap(), 1);
    // Call with new value
    let v3 = memoizer.get_or_compute(10, |_| {
        let mut count = counter.lock().unwrap();
        *count += 1;
        20
    });
    assert_eq!(v3, 20);
    assert_eq!(*counter.lock().unwrap(), 2);
    // Clear cache and recompute for same value
    memoizer.clear();
    let v4 = memoizer.get_or_compute(10, |_| {
        let mut count = counter.lock().unwrap();
        *count += 1;
        20
    });
    assert_eq!(v4, 20);
    assert_eq!(*counter.lock().unwrap(), 3);
}

#[test]
fn test_combined_wrappers() {
    // Test combining different wrappers

    // Sum of products
    let prod1 = Product(5);
    let prod2 = Product(10);
    let sum_of_products = Sum(prod1.0).combine(&Sum(prod2.0));
    assert_eq!(sum_of_products, Sum(15));

    // Product of sums
    let sum1 = Sum(5);
    let sum2 = Sum(10);
    let product_of_sums = Product(sum1.0).combine(&Product(sum2.0));
    assert_eq!(product_of_sums, Product(50));

    // Min of sums
    let sum1 = Sum(5);
    let sum2 = Sum(10);
    let min_of_sums = Min(sum1.0).combine(&Min(sum2.0));
    assert_eq!(min_of_sums, Min(5));

    // Sum of mins
    let min1 = Min(5);
    let min2 = Min(3);
    let sum_of_mins = Sum(min1.0).combine(&Sum(min2.0));
    assert_eq!(sum_of_mins, Sum(8));

    // First of products
    let prod1 = Product(5);
    let prod2 = Product(10);
    let first_of_products = First(Some(prod1.0)).combine(&First(Some(prod2.0)));
    assert_eq!(first_of_products, First(Some(5)));

    // Product of firsts
    let first1 = First(Some(5));
    let first2 = First(Some(10));
    let product_of_firsts = Product(first1.0.unwrap()).combine(&Product(first2.0.unwrap()));
    assert_eq!(product_of_firsts, Product(50));
}

#[test]
fn test_wrapper_hkt() {
    // Test HKT implementation for wrappers
    let sum = Sum(42);
    let mapped_sum = sum.fmap(|x| x.to_string());
    assert_eq!(mapped_sum, Sum("42".to_string()));

    let prod = Product(42);
    let mapped_prod = prod.fmap(|x| x.to_string());
    assert_eq!(mapped_prod, Product("42".to_string()));

    let min = Min(42);
    let mapped_min = min.fmap(|x| x.to_string());
    assert_eq!(mapped_min, Min("42".to_string()));

    let max = Max(42);
    let mapped_max = max.fmap(|x| x.to_string());
    assert_eq!(mapped_max, Max("42".to_string()));

    let first = First(Some(42));
    let mapped_first = first.fmap(|x| x.to_string());
    assert_eq!(mapped_first, First(Some("42".to_string())));

    let last = Last(Some(42));
    let mapped_last = last.fmap(|x| x.to_string());
    assert_eq!(mapped_last, Last(Some("42".to_string())));
}

#[test]
fn test_real_world_use_cases() {
    // Test some practical use cases for the wrapper types

    // 1. Using Sum to calculate total
    let values = [1, 2, 3, 4, 5];
    let total = values
        .iter()
        .map(|&x| Sum(x))
        .fold(Sum(0), |acc, x| acc.combine(&x));
    assert_eq!(total, Sum(15));

    // 2. Using Product to calculate factorial
    let values = [1, 2, 3, 4, 5];
    let factorial = values
        .iter()
        .map(|&x| Product(x))
        .fold(Product(1), |acc, x| acc.combine(&x));
    assert_eq!(factorial, Product(120));

    // 3. Using Min to find minimum value
    let values = [5, 3, 8, 2, 7];
    let minimum = values
        .iter()
        .map(|&x| Min(x))
        .fold(Min(i32::MAX), |acc, x| acc.combine(&x));
    assert_eq!(minimum, Min(2));

    // 4. Using Max to find maximum value
    let values = [5, 3, 8, 2, 7];
    let maximum = values
        .iter()
        .map(|&x| Max(x))
        .fold(Max(i32::MIN), |acc, x| acc.combine(&x));
    assert_eq!(maximum, Max(8));

    // 5. Using First to get the first non-None value
    let values: Vec<Option<i32>> = vec![None, Some(42), Some(84), None];
    let first: First<i32> = values
        .iter()
        .filter_map(|&x| x) // Filter out None, unwrap Some
        .map(|x| First(Some(x)))
        .fold(First(None), |acc, x| acc.combine(&x));
    assert_eq!(first, First(Some(42)));

    // 6. Using Last to get the last non-None value
    let values: Vec<Option<i32>> = vec![None, Some(42), Some(84), None];
    let last: Last<i32> = values
        .iter()
        .filter_map(|&x| x) // Filter out None, unwrap Some
        .map(|x| Last(Some(x)))
        .fold(Last(None), |acc, x| acc.combine(&x));
    assert_eq!(last, Last(Some(84)));

    // 7. Using Memoizer for expensive computation
    let counter = Arc::new(Mutex::new(0));
    let counter_clone = counter.clone();

    // Define an "expensive" function
    let memoizer = Memoizer::new();

    // Call multiple times
    for _ in 0..10 {
        assert_eq!(
            memoizer.get_or_compute((), |_| {
                let mut count = counter_clone.lock().unwrap();
                *count += 1;
                499500
            }),
            499500
        );
    }

    // Should only have computed once
    assert_eq!(*counter.lock().unwrap(), 1);
}

#[test]
fn single_thread_memoization() {
    let memo: Memoizer<u32, u32> = Memoizer::new();
    let result = memo.get_or_compute(5, |x| x * 2);
    assert_eq!(result, 10);
    // Should hit cache
    let again = memo.get_or_compute(5, |_| 999);
    assert_eq!(again, 10);
}

#[test]
fn multi_threaded_memoization() {
    let memo = Arc::new(Memoizer::new());
    let handles: Vec<_> = (0..8)
        .map(|i| {
            let memo = memo.clone();
            thread::spawn(move || memo.get_or_compute(i % 3, |x| x * 10))
        })
        .collect();
    let results: Vec<_> = handles.into_iter().map(|h| h.join().unwrap()).collect();
    for &v in &[0, 10, 20] {
        assert!(results.contains(&v));
    }
}

#[test]
fn clear_cache() {
    let memo: Memoizer<u32, u32> = Memoizer::new();
    memo.get_or_compute(1, |x| x + 1);
    memo.clear();
    let v = memo.get_or_compute(1, |_| 42);
    assert_eq!(v, 42);
}

#[test]
fn test_memoizer_default() {
    let counter = Arc::new(Mutex::new(0));
    let counter_clone = counter.clone();
    let memoizer: Memoizer<(), i32> = Memoizer::default();

    // First call should compute the value
    let v1 = memoizer.get_or_compute((), |_| {
        let mut count = counter_clone.lock().unwrap();
        *count += 1;
        *count
    });
    assert_eq!(v1, 1);

    // Second call should use cache
    let v2 = memoizer.get_or_compute((), |_| unreachable!());
    assert_eq!(v2, 1);
    assert_eq!(*counter.lock().unwrap(), 1);

    // Clear cache and recompute
    memoizer.clear();
    let v3 = memoizer.get_or_compute((), |_| {
        let mut count = counter.lock().unwrap();
        *count += 1;
        *count
    });
    assert_eq!(v3, 2);
}

#[cfg(feature = "serde")]
#[test]
fn test_wrapper_serde() {
    use serde_json;

    // Test First
    let first = First(Some(42));
    let serialized = serde_json::to_string(&first).unwrap();
    let deserialized: First<i32> = serde_json::from_str(&serialized).unwrap();
    assert_eq!(first, deserialized);

    // Test Last
    let last = Last(Some(42));
    let serialized = serde_json::to_string(&last).unwrap();
    let deserialized: Last<i32> = serde_json::from_str(&serialized).unwrap();
    assert_eq!(last, deserialized);

    // Test Max
    let max = Max(42);
    let serialized = serde_json::to_string(&max).unwrap();
    let deserialized: Max<i32> = serde_json::from_str(&serialized).unwrap();
    assert_eq!(max, deserialized);

    // Test Min
    let min = Min(42);
    let serialized = serde_json::to_string(&min).unwrap();
    let deserialized: Min<i32> = serde_json::from_str(&serialized).unwrap();
    assert_eq!(min, deserialized);

    // Test Product
    let product = Product(42);
    let serialized = serde_json::to_string(&product).unwrap();
    let deserialized: Product<i32> = serde_json::from_str(&serialized).unwrap();
    assert_eq!(product, deserialized);

    // Test Sum
    let sum = Sum(42);
    let serialized = serde_json::to_string(&sum).unwrap();
    let deserialized: Sum<i32> = serde_json::from_str(&serialized).unwrap();
    assert_eq!(sum, deserialized);
}

// ============================================================================
// Predicate Tests
// ============================================================================

mod predicate_tests {
    use rustica::datatypes::wrapper::predicate::Predicate;
    use rustica::traits::monoid::Monoid;
    use rustica::traits::semigroup::Semigroup;

    mod basic_operations {
        use super::*;

        #[test]
        fn test_new_and_contains() {
            let is_positive = Predicate::new(|&x: &i32| x > 0);
            assert!(is_positive.contains(&5));
            assert!(!is_positive.contains(&-3));
            assert!(!is_positive.contains(&0));
        }

        #[test]
        fn test_even_predicate() {
            let is_even = Predicate::new(|x: &i32| *x % 2 == 0);
            assert!(is_even.contains(&2));
            assert!(is_even.contains(&-4));
            assert!(!is_even.contains(&3));
        }

        #[test]
        fn test_string_predicate() {
            let is_long = Predicate::new(|s: &String| s.len() > 5);
            assert!(is_long.contains(&"hello world".to_string()));
            assert!(!is_long.contains(&"hi".to_string()));
        }
    }

    mod set_operations {
        use super::*;

        #[test]
        fn test_union() {
            let is_even = Predicate::new(|x: &i32| *x % 2 == 0);
            let is_positive = Predicate::new(|x: &i32| *x > 0);
            let even_or_positive = is_even.union(&is_positive);

            assert!(even_or_positive.contains(&2)); // Even and positive
            assert!(even_or_positive.contains(&-4)); // Even but not positive
            assert!(even_or_positive.contains(&3)); // Positive but not even
            assert!(!even_or_positive.contains(&-5)); // Neither
        }

        #[test]
        fn test_intersection() {
            let is_even = Predicate::new(|x: &i32| *x % 2 == 0);
            let is_positive = Predicate::new(|x: &i32| *x > 0);
            let even_and_positive = is_even.intersection(&is_positive);

            assert!(even_and_positive.contains(&2)); // Even and positive
            assert!(!even_and_positive.contains(&-4)); // Even but not positive
            assert!(!even_and_positive.contains(&3)); // Positive but not even
            assert!(!even_and_positive.contains(&-5)); // Neither
        }

        #[test]
        fn test_diff() {
            let is_integer = Predicate::new(|x: &f64| x.fract() == 0.0);
            let is_negative = Predicate::new(|x: &f64| *x < 0.0);
            let positive_integers = is_integer.diff(&is_negative);

            assert!(positive_integers.contains(&2.0)); // Integer and not negative
            assert!(!positive_integers.contains(&-3.0)); // Integer but negative
            assert!(!positive_integers.contains(&1.5)); // Not an integer
        }

        #[test]
        fn test_negate() {
            let is_even = Predicate::new(|x: &i32| *x % 2 == 0);
            let is_odd = is_even.negate();

            assert!(!is_odd.contains(&2));
            assert!(is_odd.contains(&3));
            assert!(!is_odd.contains(&0));
        }

        #[test]
        fn test_double_negate() {
            let is_positive = Predicate::new(|x: &i32| *x > 0);
            let double_negated = is_positive.negate().negate();

            // Double negation should be equivalent to original
            for x in [-5, -1, 0, 1, 5] {
                assert_eq!(is_positive.contains(&x), double_negated.contains(&x));
            }
        }
    }

    mod operator_overloading {
        use super::*;

        #[test]
        fn test_bitor_operator() {
            let is_even = Predicate::new(|x: &i32| *x % 2 == 0);
            let is_positive = Predicate::new(|x: &i32| *x > 0);
            let combined = is_even | is_positive;

            assert!(combined.contains(&2)); // Both
            assert!(combined.contains(&-4)); // Even only
            assert!(combined.contains(&3)); // Positive only
            assert!(!combined.contains(&-3)); // Neither
        }

        #[test]
        fn test_bitand_operator() {
            let is_even = Predicate::new(|x: &i32| *x % 2 == 0);
            let is_positive = Predicate::new(|x: &i32| *x > 0);
            let combined = is_even & is_positive;

            assert!(combined.contains(&2));
            assert!(!combined.contains(&-4));
            assert!(!combined.contains(&3));
        }

        #[test]
        fn test_sub_operator() {
            let is_positive = Predicate::new(|x: &i32| *x > 0);
            let is_even = Predicate::new(|x: &i32| *x % 2 == 0);
            let positive_odd = is_positive - is_even;

            assert!(positive_odd.contains(&3));
            assert!(positive_odd.contains(&5));
            assert!(!positive_odd.contains(&2));
            assert!(!positive_odd.contains(&-3));
        }

        #[test]
        fn test_not_operator() {
            let is_positive = Predicate::new(|x: &i32| *x > 0);
            let not_positive = !is_positive;

            assert!(not_positive.contains(&-5));
            assert!(not_positive.contains(&0));
            assert!(!not_positive.contains(&5));
        }
    }

    mod semigroup_impl {
        use super::*;

        #[test]
        fn test_combine() {
            let is_even = Predicate::new(|x: &i32| *x % 2 == 0);
            let is_large = Predicate::new(|x: &i32| *x > 100);
            let is_even_or_large = is_even.combine(&is_large);

            assert!(is_even_or_large.contains(&2)); // Even but not large
            assert!(is_even_or_large.contains(&200)); // Both
            assert!(is_even_or_large.contains(&101)); // Large but not even
            assert!(!is_even_or_large.contains(&51)); // Neither
        }

        #[test]
        fn test_combine_owned() {
            let is_divisible_by_2 = Predicate::new(|x: &i32| *x % 2 == 0);
            let is_divisible_by_3 = Predicate::new(|x: &i32| *x % 3 == 0);
            let is_divisible_by_2_or_3 = is_divisible_by_2.combine_owned(is_divisible_by_3);

            assert!(is_divisible_by_2_or_3.contains(&6)); // Both
            assert!(is_divisible_by_2_or_3.contains(&4)); // 2 only
            assert!(is_divisible_by_2_or_3.contains(&9)); // 3 only
            assert!(!is_divisible_by_2_or_3.contains(&5)); // Neither
        }

        #[test]
        fn test_associativity_law() {
            let is_even = Predicate::new(|x: &i32| *x % 2 == 0);
            let is_positive = Predicate::new(|x: &i32| *x > 0);
            let is_multiple_of_3 = Predicate::new(|x: &i32| *x % 3 == 0);

            let test_values = [-6, -3, -2, -1, 0, 1, 2, 3, 4, 5, 6, 9, 12];

            for &val in test_values.iter() {
                let left = is_even.combine(&is_positive).combine(&is_multiple_of_3);
                let right = is_even.combine(&is_positive.combine(&is_multiple_of_3));
                assert_eq!(left.contains(&val), right.contains(&val));
            }
        }
    }

    mod monoid_impl {
        use super::*;

        #[test]
        fn test_empty() {
            let empty_pred = Predicate::<i32>::empty();

            // Empty predicate always returns false
            assert!(!empty_pred.contains(&42));
            assert!(!empty_pred.contains(&-7));
            assert!(!empty_pred.contains(&0));
        }

        #[test]
        fn test_left_identity_law() {
            let is_even = Predicate::new(|x: &i32| *x % 2 == 0);
            let test_values = [-10, -5, -2, -1, 0, 1, 2, 5, 10];

            for &val in test_values.iter() {
                let empty = Predicate::<i32>::empty();
                assert_eq!(
                    empty.combine(&is_even).contains(&val),
                    is_even.contains(&val)
                );
            }
        }

        #[test]
        fn test_right_identity_law() {
            let is_positive = Predicate::new(|x: &i32| *x > 0);
            let test_values = [-10, -5, -2, -1, 0, 1, 2, 5, 10];

            for &val in test_values.iter() {
                let empty = Predicate::<i32>::empty();
                assert_eq!(
                    is_positive.combine(&empty).contains(&val),
                    is_positive.contains(&val)
                );
            }
        }

        #[test]
        fn test_combine_with_empty() {
            let empty_pred = Predicate::<i32>::empty();
            let is_positive = Predicate::new(|x: &i32| *x > 0);
            let combined = empty_pred.combine(&is_positive);

            assert!(combined.contains(&5));
            assert!(!combined.contains(&-5));
        }
    }

    mod complex_scenarios {
        use super::*;

        #[test]
        fn test_complex_predicate_composition() {
            let is_even = Predicate::new(|x: &i32| *x % 2 == 0);
            let is_positive = Predicate::new(|x: &i32| *x > 0);
            let is_small = Predicate::new(|x: &i32| *x < 10);

            // Positive and (even or small)
            let complex = is_positive.intersection(&is_even.union(&is_small));

            assert!(complex.contains(&2)); // Positive, even, small
            assert!(complex.contains(&3)); // Positive, not even, small
            assert!(complex.contains(&12)); // Positive, even, not small
            assert!(!complex.contains(&-2)); // Not positive
            assert!(!complex.contains(&15)); // Positive but not even and not small
        }

        #[test]
        fn test_clone() {
            let is_positive = Predicate::new(|x: &i32| *x > 0);
            let cloned = is_positive.clone();

            for x in [-5, 0, 5] {
                assert_eq!(is_positive.contains(&x), cloned.contains(&x));
            }
        }

        #[test]
        fn test_distributivity() {
            let a = Predicate::new(|x: &i32| *x > 0);
            let b = Predicate::new(|x: &i32| *x % 2 == 0);
            let c = Predicate::new(|x: &i32| *x < 10);

            let test_values = [-5, -2, 0, 1, 2, 5, 8, 10, 15, 20];

            for &val in test_values.iter() {
                let left = a.intersection(&b.union(&c));
                let right = a.intersection(&b).union(&a.intersection(&c));
                assert_eq!(left.contains(&val), right.contains(&val));
            }
        }
    }
}
