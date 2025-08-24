use rustica::datatypes::wrapper::first::First;
use rustica::datatypes::wrapper::last::Last;
use rustica::datatypes::wrapper::max::Max;
use rustica::datatypes::wrapper::memoizer::Memoizer;
use rustica::datatypes::wrapper::min::Min;
use rustica::datatypes::wrapper::product::Product;
use rustica::datatypes::wrapper::sum::Sum;
use rustica::datatypes::wrapper::thunk::Thunk;
use rustica::datatypes::wrapper::value::Value;
use rustica::prelude::*;
use rustica::traits::evaluate::Evaluate;
use rustica::traits::foldable::Foldable;
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

    // Test fold operations
    let folded_left = first_some.fold_left(&0, |acc, x| acc + x);
    assert_eq!(folded_left, 42);

    let folded_right = first_some.fold_right(&0, |x, acc| x + acc);
    assert_eq!(folded_right, 42);
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

    // Test fold operations
    let folded_left = last_some.fold_left(&0, |acc, x| acc + x);
    assert_eq!(folded_left, 42);

    let folded_right = last_some.fold_right(&0, |x, acc| x + acc);
    assert_eq!(folded_right, 42);
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

    // Test fold operations
    let folded_left = min1.fold_left(&0, |acc, x| acc + x);
    assert_eq!(folded_left, 10);

    let folded_right = min1.fold_right(&0, |x, acc| x + acc);
    assert_eq!(folded_right, 10);
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

    // Test fold operations
    let folded_left = max1.fold_left(&0, |acc, x| acc + x);
    assert_eq!(folded_left, 10);

    let folded_right = max1.fold_right(&0, |x, acc| x + acc);
    assert_eq!(folded_right, 10);
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

    // Test fold operations
    let folded_left = sum1.fold_left(&0, |acc, x| acc + x);
    assert_eq!(folded_left, 10);

    let folded_right = sum1.fold_right(&0, |x, acc| x + acc);
    assert_eq!(folded_right, 10);
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

    // Test fold operations
    let folded_left = prod1.fold_left(&1, |acc, x| acc * x);
    assert_eq!(folded_left, 10);

    let folded_right = prod1.fold_right(&1, |x, acc| x * acc);
    assert_eq!(folded_right, 10);
}

#[test]
fn test_value_wrapper() {
    // Test Value creation and access
    let value = Value::new(42);

    // Test evaluate
    assert_eq!(value.evaluate(), 42);
    assert_eq!(value.evaluate_owned(), 42);
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

    let value = Value::new(42);
    let mapped_value = value.fmap(|x| x.to_string());
    assert_eq!(mapped_value.evaluate(), "42".to_string());
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
    let first = values
        .iter()
        .map(|&x| First(x))
        .fold(First(None), |acc, x| acc.combine(&x));
    assert_eq!(first, First(Some(42)));

    // 6. Using Last to get the last non-None value
    let values: Vec<Option<i32>> = vec![None, Some(42), Some(84), None];
    let last = values
        .iter()
        .map(|&x| Last(x))
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
