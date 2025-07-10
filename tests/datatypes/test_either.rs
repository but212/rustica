use rustica::datatypes::either::Either;
use rustica::traits::applicative::Applicative;
use rustica::traits::functor::Functor;
use rustica::traits::identity::Identity;
use rustica::traits::monad::Monad;

// Type alias to simplify complex types
type BoxedIntFunction<'a> = Either<&'a str, Box<dyn Fn(&i32) -> i32>>;
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
    let doubled = left.fmap_left(|x| x * 2);
    assert_eq!(doubled.unwrap_left(), 84);

    // Test map_right
    let right: Either<i32, String> = Either::right("hello".to_string());
    let upper = right.clone().fmap_right(|s| s.to_uppercase());
    assert_eq!(upper.unwrap_right(), "HELLO");

    // Test that mapping the wrong side doesn't change anything
    let left_mapped = left.fmap_right(|s| s.to_uppercase());
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
    let pure: Either<&str, i32> = Either::<&str, i32>::pure(&42);
    assert_eq!(pure.unwrap_right(), 42);

    // Test apply
    let value: Either<&str, i32> = Either::right(42);
    let f: BoxedIntFunction = Either::right(Box::new(|x| x + 1));
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

    // Test apply short-circuiting behavior
    let value_right: Either<&str, i32> = Either::right(42);
    let value_left: Either<&str, i32> = Either::left("value error");
    type EitherF<'a> = Either<&'a str, Box<dyn Fn(&i32) -> i32>>;
    let f_right: EitherF = Either::right(Box::new(|x| x + 1));
    let f_left: EitherF = Either::left("function error");

    // Right <*> Right = Right
    assert_eq!(value_right.apply(&f_right).unwrap_right(), 43);
    // Left <*> Right = Left
    assert_eq!(value_left.apply(&f_right).unwrap_left(), "value error");
    // Right <*> Left = Left
    assert_eq!(value_right.apply(&f_left).unwrap_left(), "function error");
    // Left <*> Left = Left (first Left encountered)
    assert_eq!(value_left.apply(&f_left).unwrap_left(), "value error");

    // Test apply_owned short-circuiting behavior
    let value_right_owned: Either<&str, i32> = Either::right(42);
    let value_left_owned: Either<&str, i32> = Either::left("value error owned");
    let f_right_owned: Either<&str, fn(i32) -> i32> = Either::right(|x| x + 1);
    let f_left_owned: Either<&str, fn(i32) -> i32> = Either::left("function error owned");

    // Right <*> Right = Right
    assert_eq!(
        value_right_owned.apply_owned(f_right_owned).unwrap_right(),
        43
    );
    // Left <*> Right = Left
    assert_eq!(
        value_left_owned.apply_owned(f_right_owned).unwrap_left(),
        "value error owned"
    );
    // Right <*> Left = Left
    assert_eq!(
        value_right_owned.apply_owned(f_left_owned).unwrap_left(),
        "function error owned"
    );
    // Left <*> Left = Left (first Left encountered)
    assert_eq!(
        value_left_owned.apply_owned(f_left_owned).unwrap_left(),
        "value error owned"
    );

    // Test lift2 short-circuiting behavior
    let a_right: Either<&str, i32> = Either::right(2);
    let a_left: Either<&str, i32> = Either::left("a error");
    let b_right: Either<&str, i32> = Either::right(3);
    let b_left: Either<&str, i32> = Either::left("b error");

    // Right lift Right = Right
    assert_eq!(a_right.lift2(&b_right, |x, y| x * y).unwrap_right(), 6);
    // Left lift Right = Left
    assert_eq!(
        a_left.lift2(&b_right, |x, y| x * y).unwrap_left(),
        "a error"
    );
    // Right lift Left = Left
    assert_eq!(
        a_right.lift2(&b_left, |x, y| x * y).unwrap_left(),
        "b error"
    );
    // Left lift Left = Left (first Left encountered)
    assert_eq!(a_left.lift2(&b_left, |x, y| x * y).unwrap_left(), "a error");

    // Test lift2_owned short-circuiting behavior
    // Right lift Right = Right
    assert_eq!(a_right.lift2_owned(b_right, |x, y| x * y).unwrap_right(), 6);
    // Left lift Right = Left
    assert_eq!(
        a_left.lift2_owned(b_right, |x, y| x * y).unwrap_left(),
        "a error"
    );
    // Right lift Left = Left
    assert_eq!(
        a_right.lift2_owned(b_left, |x, y| x * y).unwrap_left(),
        "b error"
    );
    // Left lift Left = Left (first Left encountered)
    assert_eq!(
        a_left.lift2_owned(b_left, |x, y| x * y).unwrap_left(),
        "a error"
    );

    // Test lift3 short-circuiting behavior
    let c_right: Either<&str, i32> = Either::right(4);
    let c_left: Either<&str, i32> = Either::left("c error");

    // R lift R lift R = R
    assert_eq!(
        a_right
            .lift3(&b_right, &c_right, |x, y, z| x * y + z)
            .unwrap_right(),
        10
    );
    // L lift R lift R = L (a)
    assert_eq!(
        a_left
            .lift3(&b_right, &c_right, |x, y, z| x * y + z)
            .unwrap_left(),
        "a error"
    );
    // R lift L lift R = L (b)
    assert_eq!(
        a_right
            .lift3(&b_left, &c_right, |x, y, z| x * y + z)
            .unwrap_left(),
        "b error"
    );
    // R lift R lift L = L (c)
    assert_eq!(
        a_right
            .lift3(&b_right, &c_left, |x, y, z| x * y + z)
            .unwrap_left(),
        "c error"
    );
    // L lift L lift R = L (a)
    assert_eq!(
        a_left
            .lift3(&b_left, &c_right, |x, y, z| x * y + z)
            .unwrap_left(),
        "a error"
    );

    // Test lift3_owned short-circuiting behavior
    // R lift R lift R = R
    assert_eq!(
        a_right
            .lift3_owned(b_right, c_right, |x, y, z| x * y + z)
            .unwrap_right(),
        10
    );
    // L lift R lift R = L (a)
    assert_eq!(
        a_left
            .lift3_owned(b_right, c_right, |x, y, z| x * y + z)
            .unwrap_left(),
        "a error"
    );
    // R lift L lift R = L (b)
    assert_eq!(
        a_right
            .lift3_owned(b_left, c_right, |x, y, z| x * y + z)
            .unwrap_left(),
        "b error"
    );
    // R lift R lift L = L (c)
    assert_eq!(
        a_right
            .lift3_owned(b_right, c_left, |x, y, z| x * y + z)
            .unwrap_left(),
        "c error"
    );
    // L lift L lift R = L (a)
    assert_eq!(
        a_left
            .lift3_owned(b_left, c_right, |x, y, z| x * y + z)
            .unwrap_left(),
        "a error"
    );
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

    assert_eq!(left.left_or("default"), "error");
    assert_eq!(right.left_or("default"), "default");

    // Test right_or
    assert_eq!(left.right_or(0), 0);
    assert_eq!(right.right_or(0), 42);
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

#[test]
fn test_either_left_or_right_or() {
    let l: Either<&str, i32> = Either::left("err");
    let r: Either<&str, i32> = Either::right(42);

    assert_eq!(l.left_or("default"), "err");
    assert_eq!(r.left_or("default"), "default");
    assert_eq!(l.right_or(0), 0);
    assert_eq!(r.right_or(0), 42);
}
