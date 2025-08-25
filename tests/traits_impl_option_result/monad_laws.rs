use rustica::traits::monad::Monad;
use rustica::traits::pure::Pure;

/// Test the Monad Left Identity Law: pure(a) >>= f = f(a)
///
/// Binding a pure value with a function should be equivalent
/// to applying the function directly to the value.
#[cfg(test)]
mod monad_left_identity_law {
    use super::*;

    #[test]
    fn test_option_left_identity() {
        let value = 42;
        let f = |x: &i32| if *x > 0 { Some(x * 2) } else { None };

        // Test: pure(a) >>= f = f(a)
        let left_side = <Option<i32> as Pure>::pure(&value).bind(&f);
        let right_side = f(&value);

        assert_eq!(left_side, right_side);
    }

    #[test]
    fn test_result_left_identity() {
        let value = 42;
        let f = |x: &i32| -> Result<i32, &str> { if *x > 0 { Ok(x * 2) } else { Err("negative") } };

        // Test: pure(a) >>= f = f(a)
        let left_side = <Result<i32, &str> as Pure>::pure(&value).bind(&f);
        let right_side = f(&value);

        assert_eq!(left_side, right_side);
    }
}

/// Test the Monad Right Identity Law: m >>= pure = m
///
/// Binding a monadic value with the pure function should
/// return the original monadic value unchanged.
#[cfg(test)]
mod monad_right_identity_law {
    use super::*;

    #[test]
    fn test_option_right_identity() {
        let some_value = Some(42);
        let none_value: Option<i32> = None;

        let pure_fn = |x: &i32| <Option<i32> as Pure>::pure(x);

        // Test: m >>= pure = m
        assert_eq!(some_value.bind(&pure_fn), some_value);
        assert_eq!(none_value.bind(&pure_fn), none_value);
    }

    #[test]
    fn test_result_right_identity() {
        let ok_value: Result<i32, &str> = Ok(42);
        let err_value: Result<i32, &str> = Err("error");

        let pure_fn = |x: &i32| <Result<i32, &str> as Pure>::pure(x);

        // Test: m >>= pure = m
        assert_eq!(ok_value.bind(&pure_fn), ok_value);
        assert_eq!(err_value.bind(&pure_fn), err_value);
    }
}

/// Test the Monad Associativity Law: (m >>= f) >>= g = m >>= (\x -> f(x) >>= g)
///
/// The order of binding operations should not matter - binding should be associative.
/// Note: Due to Rust's lifetime system complexity, we demonstrate this with simpler examples.
#[cfg(test)]
mod monad_associativity_law {
    use super::*;

    #[test]
    fn test_option_associativity_simple() {
        let some_value = Some(5);
        let none_value: Option<i32> = None;

        let f = |x: &i32| Some(*x * 2);
        let g = |x: &i32| Some(*x + 1);

        // Test: (m >>= f) >>= g = m >>= (\x -> f(x) >>= g)
        let left_side = some_value.bind(&f).bind(&g);
        let right_side = some_value.bind(|x| f(x).bind(&g));

        assert_eq!(left_side, right_side);

        // Test with None
        let left_side_none = none_value.bind(&f).bind(&g);
        let right_side_none = none_value.bind(|x| f(x).bind(&g));

        assert_eq!(left_side_none, right_side_none);
    }

    #[test]
    fn test_result_associativity_simple() {
        let ok_value: Result<i32, &str> = Ok(5);
        let err_value: Result<i32, &str> = Err("error");

        let f = |x: &i32| -> Result<i32, &str> { Ok(*x * 2) };
        let g = |x: &i32| -> Result<i32, &str> { Ok(*x + 1) };

        // Test: (m >>= f) >>= g = m >>= (\x -> f(x) >>= g)
        let left_side = ok_value.bind(&f).bind(&g);
        let right_side = ok_value.bind(|x| f(x).bind(&g));

        assert_eq!(left_side, right_side);

        // Test with Err
        let left_side_err = err_value.bind(&f).bind(&g);
        let right_side_err = err_value.bind(|x| f(x).bind(&g));

        assert_eq!(left_side_err, right_side_err);
    }
}

/// Test the Join Consistency Law: join(fmap(f, m)) = bind(m, f)
///
/// The join operation should be consistent with bind - they should
/// produce equivalent results when used appropriately.
#[cfg(test)]
mod monad_join_consistency_law {
    use super::*;
    use rustica::traits::functor::Functor;

    #[test]
    fn test_option_join_consistency() {
        let some_value = Some(42);
        let none_value: Option<i32> = None;

        let f = |x: &i32| Some(x * 2);

        // Test: join(fmap(f, m)) = bind(m, f)
        let bind_some = some_value.bind(&f);
        let fmap_then_join_some = some_value.fmap(&f).join();
        assert_eq!(fmap_then_join_some, bind_some);

        // Test with None
        let bind_none = none_value.bind(&f);
        let fmap_then_join_none = none_value.fmap(&f).join();
        assert_eq!(fmap_then_join_none, bind_none);
    }

    #[test]
    fn test_result_join_consistency() {
        let ok_value: Result<i32, &str> = Ok(42);
        let err_value: Result<i32, &str> = Err("error");

        let f = |x: &i32| -> Result<i32, &str> { Ok(x * 2) };

        // Test: join(fmap(f, m)) = bind(m, f)
        let bind_ok = ok_value.bind(&f);
        let fmap_then_join_ok = ok_value.fmap(&f).join();
        assert_eq!(fmap_then_join_ok, bind_ok);

        // Test with Err
        let bind_err = err_value.bind(&f);
        let fmap_then_join_err = err_value.fmap(&f).join();
        assert_eq!(fmap_then_join_err, bind_err);
    }
}

#[cfg(test)]
mod monad_quickcheck_laws {
    use super::*;
    use quickcheck_macros::quickcheck;
    use rustica::traits::functor::Functor;

    // Join Consistency Law: join(fmap(f, m)) == bind(m, f) for Option
    #[quickcheck]
    fn qc_option_join_consistency(m: Option<i32>) -> bool {
        let f = |x: &i32| Some(x.saturating_mul(2));
        let left = m.fmap(&f).join();
        let right = m.bind(&f);
        left == right
    }

    // Join Consistency Law: join(fmap(f, m)) == bind(m, f) for Result
    #[quickcheck]
    fn qc_result_join_consistency(m: Result<i32, i8>) -> bool {
        let f = |x: &i32| -> Result<i32, i8> { Ok(x.saturating_mul(2)) };
        let left = m.fmap(&f).join();
        let right = m.bind(&f);
        left == right
    }

    // Left Identity Law: pure(a).bind(f) == f(a) for Result
    #[quickcheck]
    fn qc_result_left_identity(x: i32) -> bool {
        let f = |x: &i32| -> Result<i32, i8> { Ok(x.saturating_mul(2)) };
        let left: Result<i32, i8> = <Result<i32, i8> as Pure>::pure(&x).bind(&f);
        let right = f(&x);
        left == right
    }

    // Right Identity Law: m.bind(pure) == m for Result (covers Ok and Err)
    #[quickcheck]
    fn qc_result_right_identity(x: i32, e: i8, is_ok: bool) -> bool {
        let m: Result<i32, i8> = if is_ok { Ok(x) } else { Err(e) };
        let left = m.clone().bind(Result::<i32, i8>::pure);
        left == m
    }

    // Associativity Law: (m.bind(f)).bind(g) == m.bind(|x| f(x).bind(g)) for Result
    #[quickcheck]
    fn qc_result_associativity(x: i32, e: i8, is_ok: bool) -> bool {
        let m: Result<i32, i8> = if is_ok { Ok(x) } else { Err(e) };
        let f = |x: &i32| -> Result<i32, i8> { Ok(x.saturating_mul(2)) };
        let g = |x: &i32| -> Result<i32, i8> { Ok(x.saturating_add(10)) };
        let left = m.clone().bind(&f).bind(&g);
        let right = m.bind(|x| f(x).bind(&g));
        left == right
    }
}
