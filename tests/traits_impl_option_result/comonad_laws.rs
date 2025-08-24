use rustica::traits::comonad::Comonad;

/// Comonad Left Identity: extend(extract)(w) = w
#[cfg(test)]
mod comonad_left_identity_law {
    use super::*;

    #[test]
    fn test_option_left_identity() {
        let some = Some(10);
        let none: Option<i32> = None;

        let left_some = some.extend(|w| w.extract());
        assert_eq!(left_some, some);

        let left_none = none.extend(|w| w.extract());
        assert_eq!(left_none, none);
    }

    #[test]
    fn test_result_left_identity() {
        let ok: Result<i32, &str> = Ok(10);
        let err: Result<i32, &str> = Err("error");

        let left_ok = ok.extend(|w| w.extract());
        assert_eq!(left_ok, ok);

        let left_err = err.extend(|w| w.extract());
        assert_eq!(left_err, err);
    }
}

/// Comonad Right Identity: extract(extend(f)(w)) = f(w)
/// Note: Only applicable when extract is defined (Some/Ok).
#[cfg(test)]
mod comonad_right_identity_law {
    use super::*;

    #[test]
    fn test_option_right_identity_some() {
        let some = Some(21);
        let f = |w: &Option<i32>| w.extract().saturating_mul(2);

        let left = some.extend(&f).extract();
        let right = f(&some);
        assert_eq!(left, right);
    }

    #[test]
    fn test_result_right_identity_ok() {
        let ok: Result<i32, &str> = Ok(21);
        let f = |w: &Result<i32, &str>| w.extract().saturating_mul(2);

        let left = ok.extend(&f).extract();
        let right = f(&ok);
        assert_eq!(left, right);
    }
}

/// Comonad Associativity:
/// extend(f)(extend(g)(w)) = extend(|x| f(extend(g)(x)))(w)
#[cfg(test)]
mod comonad_associativity_law {
    use super::*;

    #[test]
    fn test_option_associativity() {
        let some = Some(5);
        let none: Option<i32> = None;

        let f = |w: &Option<i32>| w.extract().saturating_add(3);
        let g = |w: &Option<i32>| w.extract().saturating_mul(2);

        // Some case
        let left_some = some.extend(&g).extend(&f);
        let right_some = some.extend(|x| f(&x.extend(&g)));
        assert_eq!(left_some, right_some);

        // None case
        let left_none = none.extend(&g).extend(&f);
        let right_none = none.extend(|x| f(&x.extend(&g)));
        assert_eq!(left_none, right_none);
    }

    #[test]
    fn test_result_associativity() {
        let ok: Result<i32, i8> = Ok(5);
        let err: Result<i32, i8> = Err(7);

        let f = |w: &Result<i32, i8>| w.extract().saturating_add(3);
        let g = |w: &Result<i32, i8>| w.extract().saturating_mul(2);

        // Ok case
        let left_ok = ok.extend(&g).extend(&f);
        let right_ok = ok.extend(|x| f(&x.extend(&g)));
        assert_eq!(left_ok, right_ok);

        // Err case
        let left_err = err.extend(&g).extend(&f);
        let right_err = err.extend(|x| f(&x.extend(&g)));
        assert_eq!(left_err, right_err);
    }
}

#[cfg(test)]
mod comonad_quickcheck_laws {
    use super::*;
    use quickcheck_macros::quickcheck;

    // Left Identity: extend(extract)(w) == w for Option
    #[quickcheck]
    fn qc_option_left_identity(w: Option<i32>) -> bool {
        w.extend(|x| x.extract()) == w
    }

    // Left Identity: extend(extract)(w) == w for Result
    #[quickcheck]
    fn qc_result_left_identity(w: Result<i32, i8>) -> bool {
        w.extend(|x| x.extract()) == w
    }

    // Right Identity (applicable only when extract is defined)
    #[quickcheck]
    fn qc_option_right_identity(w: Option<i32>, n: i32) -> bool {
        let f = |x: &Option<i32>| x.extract().saturating_add(n);
        match &w {
            Some(_) => w.extend(&f).extract() == f(&w),
            None => true,
        }
    }

    #[quickcheck]
    fn qc_result_right_identity(w: Result<i32, i8>, n: i32) -> bool {
        let f = |x: &Result<i32, i8>| x.extract().saturating_add(n);
        match &w {
            Ok(_) => w.extend(&f).extract() == f(&w),
            Err(_) => true,
        }
    }

    // Associativity for Option
    #[quickcheck]
    fn qc_option_associativity(w: Option<i32>, a: i32, b: i32) -> bool {
        let f = move |x: &Option<i32>| x.extract().saturating_add(a);
        let g = move |x: &Option<i32>| x.extract().saturating_mul(b);
        let left = w.extend(&g).extend(&f);
        let right = w.extend(|x| f(&x.extend(&g)));
        left == right
    }

    // Associativity for Result
    #[quickcheck]
    fn qc_result_associativity(w: Result<i32, i8>, a: i32, b: i32) -> bool {
        let f = move |x: &Result<i32, i8>| x.extract().saturating_add(a);
        let g = move |x: &Result<i32, i8>| x.extract().saturating_mul(b);
        let left = w.extend(&g).extend(&f);
        let right = w.extend(|x| f(&x.extend(&g)));
        left == right
    }
}
