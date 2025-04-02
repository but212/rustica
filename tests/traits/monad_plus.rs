use rustica::traits::monad::Monad;
use rustica::traits::monad_plus::MonadPlus;

#[test]
fn test_option_monad_plus_identity() {
    let some_val: Option<i32> = Some(42);
    let none_val: Option<i32> = None;

    // Identity law checks
    assert_eq!(none_val.mplus(&some_val), some_val);
    assert_eq!(some_val.mplus(&none_val), some_val);
}

#[test]
fn test_option_monad_plus_associativity() {
    let a: Option<i32> = Some(1);
    let b: Option<i32> = Some(2);
    let c: Option<i32> = Some(3);

    // Associativity law check
    assert_eq!(a.mplus(&b).mplus(&c), a.mplus(&b.mplus(&c)));
}

#[test]
fn test_option_monad_plus_operations() {
    let a: Option<i32> = Some(1);
    let b: Option<i32> = None;
    let c: Option<i32> = Some(3);

    // Test combinations
    assert_eq!(a.mplus_owned(b), Some(1));
    assert_eq!(b.mplus_owned(c), Some(3));
    assert_eq!(b.mplus_owned(b), None);
}

#[test]
fn test_option_monad_plus_with_collection() {
    // Implement a helper function to find the first Some value
    fn first_some<T: Clone, I: Iterator<Item = Option<T>>>(iter: I) -> Option<T> {
        for item in iter {
            if item.is_some() {
                return item;
            }
        }
        None
    }

    let options: Vec<Option<i32>> = vec![None, None, Some(42), Some(7)];
    let result = first_some(options.into_iter());
    assert_eq!(result, Some(42));

    let empty_options: Vec<Option<i32>> = vec![None, None];
    let result = first_some(empty_options.into_iter());
    assert_eq!(result, None);
}

#[test]
fn test_option_monad_plus_with_mapping() {
    // Implement a helper function to find the first Some after applying a function
    fn first_mapped<T: Clone, U, I: Iterator<Item = U>, F: Fn(U) -> Option<T>>(
        iter: I,
        f: F,
    ) -> Option<T> {
        for item in iter {
            let result = f(item);
            if result.is_some() {
                return result;
            }
        }
        None
    }

    let numbers = vec![1, 2, 3, 4];
    let result = first_mapped(
        numbers.into_iter(),
        |x: i32| {
            if x > 2 {
                Some(x * 10)
            } else {
                None
            }
        },
    );
    assert_eq!(result, Some(30));

    let small_numbers = vec![1, 2];
    let result = first_mapped(small_numbers.into_iter(), |x: i32| {
        if x > 2 {
            Some(x * 10)
        } else {
            None
        }
    });
    assert_eq!(result, None);
}

#[test]
fn test_monad_plus_with_bind() {
    let opt: Option<i32> = Some(42);

    // Left Zero: mzero >>= f == mzero
    let left_zero: Option<i32> = Option::<i32>::mzero().bind(|x| Some(x + 1));
    assert_eq!(left_zero, None);

    // Right Zero: x >>= (\_ -> mzero) == mzero
    let right_zero: Option<i32> = opt.bind(|_| Option::<i32>::mzero());
    assert_eq!(right_zero, None);

    // Left Distribution: (a <|> b) >>= f == (a >>= f) <|> (b >>= f)
    let a: Option<i32> = Some(1);
    let b: Option<i32> = Some(2);
    let f = |x: &i32| Some(x * 10);

    let left_side: Option<i32> = a.mplus(&b).bind(f);
    let right_side: Option<i32> = a.bind(f).mplus(&b.bind(f));
    assert_eq!(left_side, right_side);
}
