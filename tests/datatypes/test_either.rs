use rustica::datatypes::either::Either;
use rustica::datatypes::error::EitherError;
use rustica::traits::{applicative::Applicative, functor::Functor, monad::Monad};

#[test]
fn test_either_monadic_fundamentals() {
    // 1. Creation and Basic Access
    let left: Either<i32, &str> = Either::left(42);
    let right: Either<i32, &str> = Either::right("hello");

    assert!(left.is_left() && right.is_right());
    assert_eq!(left.left_ref(), &42);
    assert_eq!(right.right_ref(), &"hello");

    // 2. Functor and Mapping (Both sides)
    assert_eq!(
        Either::<i32, i32>::left(42)
            .fmap_left(|x| x * 2)
            .unwrap_left(),
        84
    );
    assert_eq!(
        Either::<i32, &str>::right("hi")
            .fmap_right(|s| s.len())
            .unwrap_right(),
        2
    );
    assert_eq!(
        Either::<&str, i32>::right(10)
            .fmap(|x| x + 5)
            .unwrap_right(),
        15
    );

    // 3. Applicative and Monad
    let val = Either::<&str, i32>::right(42);
    let f = Either::<&str, fn(i32) -> i32>::right(|x| x + 1);

    // In rustica, usually f.apply(val) or the wrapper needs correct HKT mapping
    assert_eq!(f.apply_owned(val).unwrap_right(), 43);
    assert_eq!(
        Either::<&str, i32>::right(42)
            .bind(|x| Either::right(x * 2))
            .unwrap_right(),
        84
    );
    assert_eq!(
        Either::<&str, Either<&str, i32>>::right(Either::right(100))
            .join()
            .unwrap_right(),
        100
    );
}

#[test]
fn test_either_error_propagation() {
    // Consolidated test for short-circuiting and error handling
    let err = Either::<&str, i32>::left("init error");
    let ok = Either::<&str, i32>::right(10);

    // Applicative short-circuit
    assert_eq!(
        Either::<&str, i32>::lift2(|x, y| x + y, &err, &ok).unwrap_left(),
        "init error"
    );
    assert_eq!(
        Either::<&str, i32>::lift2(|x, y| x + y, &ok, &err).unwrap_left(),
        "init error"
    );

    // Monad short-circuit
    let result = ok
        .bind(|_| Either::left("bind error"))
        .bind(|_: &i32| Either::right(100));
    assert_eq!(result.unwrap_left(), "bind error");

    // Real-world safe division scenario
    fn safe_div(n: i32, d: i32) -> Either<&'static str, i32> {
        if d == 0 {
            Either::left("div0")
        } else {
            Either::right(n / d)
        }
    }
    assert_eq!(
        safe_div(10, 0).bind(|x| safe_div(*x, 1)).unwrap_left(),
        "div0"
    );
}

#[test]
fn test_either_utilities_and_conversions() {
    let left: Either<i32, String> = Either::left(42);
    let right: Either<i32, String> = Either::right("ok".to_string());

    // 1. Or Methods
    assert_eq!(left.clone().left_or(0), 42);
    assert_eq!(right.clone().left_or(0), 0);
    assert_eq!(
        left.clone().right_or("default".to_string()),
        "default".to_string()
    );
    assert_eq!(
        right.clone().right_or("default".to_string()),
        "ok".to_string()
    );

    // 2. Option & Result Conversions
    assert_eq!(left.clone().left_option(), Some(42));
    assert_eq!(right.clone().to_result(), Ok("ok".to_string()));

    let res_err: Result<i32, &str> = Err("oops");
    assert_eq!(
        Either::from_result(res_err),
        Either::<&str, i32>::left("oops")
    );

    // 3. Iterators
    assert_eq!(left.clone().left_iter().next(), Some(42));
    assert_eq!(right.clone().left_iter().next(), None);

    // 4. Try & Mut Methods
    let mut m_left = left.clone();
    *m_left.left_mut() = 100;
    assert_eq!(m_left.try_unwrap_left(), Ok(100));
    assert_eq!(
        right.clone().try_unwrap_left(),
        Err(EitherError::ExpectedLeft)
    );
}

#[test]
fn test_either_misc_and_safety() {
    // 1. Serde integration
    #[cfg(feature = "serde")]
    {
        use serde_json;
        let r: Either<String, i32> = Either::right(42);
        let s = serde_json::to_string(&r).unwrap();
        assert_eq!(serde_json::from_str::<Either<String, i32>>(&s).unwrap(), r);
    }

    // 2. Panics (Negative cases)
    let left: Either<i32, &str> = Either::left(1);
    assert!(std::panic::catch_unwind(move || left.unwrap_right()).is_err());

    // 3. Optimized pattern (bind_owned/fmap_owned)
    let res = Either::<&str, i32>::right(10)
        .fmap_owned(|x| x * 2)
        .bind_owned(|x| {
            if x > 15 {
                Either::right(x.to_string())
            } else {
                Either::left("small")
            }
        });
    assert_eq!(res.right_value(), "20");
}
