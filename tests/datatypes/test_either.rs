use rustica::datatypes::either::Either;
use rustica::traits::applicative::Applicative;
use rustica::traits::functor::Functor;
use rustica::traits::identity::Identity;
use rustica::traits::monad::Monad;
use rustica::traits::pure::Pure;

#[test]
fn test_either_creation_and_access() {
    // Test Left creation
    let left: Either<i32, &str> = Either::left(42);
    assert!(left.is_left());
    assert!(!left.is_right());
    assert_eq!(left.unwrap_left(), 42);
    assert_eq!(*left.left_ref(), 42);

    let left_consumed = Either::<i32, &str>::left(43);
    assert_eq!(left_consumed.left_value(), 43);

    // Test Right creation
    let right: Either<i32, &str> = Either::right("hello");
    assert!(!right.is_left());
    assert!(right.is_right());
    assert_eq!(right.unwrap_right(), "hello");
    assert_eq!(*right.right_ref(), "hello");

    let right_consumed = Either::<i32, &str>::right("world");
    assert_eq!(right_consumed.right_value(), "world");
}

#[test]
fn test_either_mapping() {
    // Test map_left
    let left: Either<i32, &str> = Either::left(42);
    let doubled = left.clone().fmap_left(|x| x * 2);
    assert_eq!(doubled.unwrap_left(), 84);

    // Test map_right
    let right: Either<i32, String> = Either::right("hello".to_string());
    let upper = right.clone().fmap_right(|s| s.to_uppercase());
    assert_eq!(upper.unwrap_right(), "HELLO");

    // Test that mapping the wrong side doesn't change anything
    let left_mapped = left.clone().fmap_right(|s| s.to_uppercase());
    assert_eq!(left_mapped.unwrap_left(), 42);
    let right_mapped = right.clone().fmap_left(|x| x * 2);
    assert_eq!(right_mapped.unwrap_right(), "hello");
}

#[test]
fn test_either_functor() {
    // Test with borrowed values
    let right: Either<i32, i32> = Either::right(42);
    let mapped = right.fmap(|x| x + 1);
    assert_eq!(mapped.unwrap_right(), 43);

    let left: Either<i32, i32> = Either::left(42);
    let mapped = left.fmap(|x| x + 1);
    assert_eq!(mapped.unwrap_left(), 42);

    // Test with owned values
    let right: Either<String, i32> = Either::right(42);
    let mapped = right.fmap(|x| x * 2);
    assert_eq!(mapped.unwrap_right(), 84);

    let left: Either<String, i32> = Either::left("error".to_string());
    let mapped = left.fmap(|x| x * 2);
    assert_eq!(mapped.unwrap_left(), "error");
}

#[test]
fn test_either_applicative() {
    // Test pure
    let pure: Either<i32, i32> = Either::<i32, i32>::pure(&42);
    assert_eq!(pure.unwrap_right(), 42);

    // Test apply
    let value: Either<&str, i32> = Either::right(42);
    let f: Either<&str, Box<dyn Fn(&i32) -> i32>> = Either::right(Box::new(|x| x + 1));
    let result = value.apply(&f);
    assert_eq!(result.unwrap_right(), 43);

    // Test apply_owned
    let value: Either<&str, i32> = Either::right(42);
    let f: Either<&str, fn(i32) -> i32> = Either::right(|x| x + 1);
    let result = value.apply_owned(f);
    assert_eq!(result.unwrap_right(), 43);

    // Test lift2
    let a: Either<&str, i32> = Either::right(2);
    let b: Either<&str, i32> = Either::right(3);
    let result = a.lift2(&b, |x, y| x * y);
    assert_eq!(result.unwrap_right(), 6);

    // Test lift2_owned
    let a: Either<&str, i32> = Either::right(2);
    let b: Either<&str, i32> = Either::right(3);
    let result = a.lift2_owned(b, |x, y| x * y);
    assert_eq!(result.unwrap_right(), 6);

    // Test lift3
    let a: Either<&str, i32> = Either::right(2);
    let b: Either<&str, i32> = Either::right(3);
    let c: Either<&str, i32> = Either::right(4);
    let result = a.lift3(&b, &c, |x, y, z| x * y + z);
    assert_eq!(result.unwrap_right(), 10);

    // Test lift3_owned
    let a: Either<&str, i32> = Either::right(2);
    let b: Either<&str, i32> = Either::right(3);
    let c: Either<&str, i32> = Either::right(4);
    let result = a.lift3_owned(b, c, |x, y, z| x * y + z);
    assert_eq!(result.unwrap_right(), 10);
}

#[test]
fn test_either_monad() {
    // Test bind
    let right: Either<&str, i32> = Either::right(42);
    let result = right.bind(|x| Either::right(x + 1));
    assert_eq!(result.unwrap_right(), 43);

    let left: Either<&str, i32> = Either::left("error");
    let result = left.bind(|x| Either::right(x + 1));
    assert_eq!(result.unwrap_left(), "error");

    // Test join
    let nested: Either<&str, Either<&str, i32>> = Either::right(Either::right(42));
    let flattened = nested.join();
    assert_eq!(flattened.unwrap_right(), 42);

    // Test bind_owned and join_owned (optimized versions)
    let right: Either<&str, i32> = Either::right(42);
    let result = right.bind_owned(|x| Either::right(x + 1));
    assert_eq!(result.unwrap_right(), 43);

    let nested = Either::<&str, Either<&str, i32>>::right(Either::right(42));
    let flattened = nested.join_owned();
    assert_eq!(flattened.unwrap_right(), 42);
}

#[test]
fn test_either_or_methods() {
    // Test left_or
    let left: Either<&str, i32> = Either::left("error");
    let right: Either<&str, i32> = Either::right(42);

    assert_eq!(left.clone().left_or("default"), "error");
    assert_eq!(right.clone().left_or("default"), "default");

    // Test right_or
    assert_eq!(left.clone().right_or(0), 0);
    assert_eq!(right.clone().right_or(0), 42);
}

#[test]
fn test_either_performance_pattern() {
    // Test a common pattern that benefits from the optimized methods
    let process_data = |input: i32| -> Either<&'static str, String> {
        let either: Either<&'static str, i32> = if input > 0 {
            Either::right(input)
        } else {
            Either::left("Invalid input")
        };

        // Using the optimized methods
        either.fmap_owned(|x| x * 2).bind_owned(|x| {
            if x < 100 {
                Either::right(x.to_string())
            } else {
                Either::left("Result too large")
            }
        })
    };

    // Test valid case
    let result = process_data(42);
    assert_eq!(result.right_value(), "84");

    // Test invalid input
    let result = process_data(-1);
    assert_eq!(result.left_value(), "Invalid input");

    // Test too large result
    let result = process_data(60);
    assert_eq!(result.left_value(), "Result too large");
}

#[test]
fn test_either_identity() {
    let right: Either<&str, i32> = Either::right(42);
    assert_eq!(*right.value(), 42);
}

#[test]
#[should_panic(expected = "called unwrap_left on Right value")]
fn test_either_unwrap_left_panic() {
    let right: Either<i32, &str> = Either::right("hello");
    right.unwrap_left();
}

#[test]
#[should_panic(expected = "called unwrap_right on Left value")]
fn test_either_unwrap_right_panic() {
    let left: Either<i32, &str> = Either::left(42);
    left.unwrap_right();
}

#[test]
fn test_either_error_handling() {
    // Simulate error handling with Either
    fn safe_div(n: i32, d: i32) -> Either<&'static str, i32> {
        if d == 0 {
            Either::left("division by zero")
        } else {
            Either::right(n / d)
        }
    }

    // Test successful case
    let result1 = safe_div(10, 2);
    assert_eq!(result1.unwrap_right(), 5);

    // Test error case
    let result2 = safe_div(10, 0);
    assert_eq!(result2.unwrap_left(), "division by zero");

    // Test chaining computations
    let result3 = safe_div(10, 2).bind(|x| safe_div(*x, 1));
    assert_eq!(result3.unwrap_right(), 5);

    let result4 = safe_div(10, 2).bind(|x| safe_div(*x, 0));
    assert_eq!(result4.unwrap_left(), "division by zero");
}
