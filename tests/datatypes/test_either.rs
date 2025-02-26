use rustica::datatypes::either::Either;
use rustica::traits::functor::Functor;
use rustica::traits::applicative::Applicative;
use rustica::traits::monad::Monad;
use rustica::traits::identity::Identity;
use rustica::traits::pure::Pure;

#[test]
fn test_either_creation_and_access() {
    // Test Left creation
    let left: Either<i32, &str> = Either::left(42);
    assert!(left.is_left());
    assert!(!left.is_right());
    assert_eq!(left.unwrap_left(), 42);

    // Test Right creation
    let right: Either<i32, &str> = Either::right("hello");
    assert!(!right.is_left());
    assert!(right.is_right());
    assert_eq!(right.unwrap_right(), "hello");
}

#[test]
fn test_either_mapping() {
    // Test map_left
    let left: Either<i32, &str> = Either::left(42);
    let doubled = left.clone().map_left(&|x| x * 2);
    assert_eq!(doubled.unwrap_left(), 84);

    // Test map_right
    let right: Either<i32, String> = Either::right("hello".to_string());
    let upper = right.clone().map_right(&|s| s.to_uppercase());
    assert_eq!(upper.unwrap_right(), "HELLO");

    // Test that mapping the wrong side doesn't change anything
    let left_mapped = left.clone().map_right(&|s| s.to_uppercase());
    assert_eq!(left_mapped.unwrap_left(), 42);
    let right_mapped = right.clone().map_left(&|x| x * 2);
    assert_eq!(right_mapped.unwrap_right(), "hello");
}

#[test]
fn test_either_functor() {
    let right: Either<i32, i32> = Either::right(42);
    let mapped = right.fmap(&|x| x + 1);
    assert_eq!(mapped.unwrap_right(), 43);

    let left: Either<i32, i32> = Either::left(42);
    let mapped = left.fmap(&|x| x + 1);
    assert_eq!(mapped.unwrap_left(), 42);
}

#[test]
fn test_either_applicative() {
    // Test pure
    let pure: Either<i32, i32> = Either::<i32, i32>::pure(42);
    assert_eq!(pure.unwrap_right(), 42);

    // Test apply
    let value: Either<&str, i32> = Either::right(42);
    let f: Either<&str, Box<dyn Fn(&i32) -> i32>> = Either::right(Box::new(|x| x + 1));
    let result = value.apply(&f);
    assert_eq!(result.unwrap_right(), 43);

    // Test lift2
    let a: Either<&str, i32> = Either::right(2);
    let b: Either<&str, i32> = Either::right(3);
    let result = a.lift2(&b, &|x, y| x * y);
    assert_eq!(result.unwrap_right(), 6);

    // Test lift3
    let a: Either<&str, i32> = Either::right(2);
    let b: Either<&str, i32> = Either::right(3);
    let c: Either<&str, i32> = Either::right(4);
    let result = a.lift3(&b, &c, &|x, y, z| x * y + z);
    assert_eq!(result.unwrap_right(), 10);
}

#[test]
fn test_either_monad() {
    // Test bind
    let right: Either<&str, i32> = Either::right(42);
    let result = right.bind(&|x| Either::right(x + 1));
    assert_eq!(result.unwrap_right(), 43);

    let left: Either<&str, i32> = Either::left("error");
    let result = left.bind(&|x| Either::right(x + 1));
    assert_eq!(result.unwrap_left(), "error");

    // Test join
    let nested: Either<&str, Either<&str, i32>> = Either::right(Either::right(42));
    let flattened = nested.join();
    assert_eq!(flattened.unwrap_right(), 42);
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
    let result3 = safe_div(10, 2)
        .bind(&|x| safe_div(*x, 1));
    assert_eq!(result3.unwrap_right(), 5);

    let result4 = safe_div(10, 2)
        .bind(&|x| safe_div(*x, 0));
    assert_eq!(result4.unwrap_left(), "division by zero");
}
