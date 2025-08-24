use rustica::datatypes::wrapper::thunk::Thunk;
use rustica::traits::evaluate::{Evaluate, EvaluateExt};

/// Evaluate Idempotence and Ref/Owned consistency laws
#[cfg(test)]
mod evaluate_idempotence_law {
    use super::*;

    #[test]
    fn test_option_idempotence_some_ref() {
        let some = Some(42);
        assert_eq!(some.evaluate(), some.evaluate());
    }

    #[test]
    fn test_result_idempotence_ok_ref() {
        let ok: Result<i32, i8> = Ok(42);
        assert_eq!(ok.evaluate(), ok.evaluate());
    }

    #[test]
    fn test_option_ref_owned_consistency_some() {
        let some = Some(7);
        assert_eq!(some.clone().evaluate(), some.evaluate_owned());
    }

    #[test]
    fn test_result_ref_owned_consistency_ok() {
        let ok: Result<i32, i8> = Ok(7);
        assert_eq!(ok.clone().evaluate(), ok.evaluate_owned());
    }
}

/// Evaluate Referential Transparency laws
#[cfg(test)]
mod evaluate_referential_transparency_law {
    use super::*;

    #[test]
    fn test_option_ref_transparency_some() {
        let some = Some(21);
        let f = |x: i32| x.saturating_mul(2).saturating_add(1);
        assert_eq!(f(some.evaluate()), some.map_evaluate(f));
    }

    #[test]
    fn test_result_ref_transparency_ok() {
        let ok: Result<i32, i8> = Ok(21);
        let f = |x: i32| x.saturating_mul(2).saturating_add(1);
        assert_eq!(f(ok.evaluate()), ok.map_evaluate(f));
    }
}

/// Evaluate Consistency laws
#[cfg(test)]
mod evaluate_consistency_law {
    use super::*;

    #[test]
    fn test_option_consistency_some() {
        let some = Some(10);
        assert_eq!(some.evaluate(), 10);
        assert_eq!(some.clone().evaluate_owned(), 10);
    }

    #[test]
    fn test_result_consistency_ok() {
        let ok: Result<i32, i8> = Ok(10);
        assert_eq!(ok.evaluate(), 10);
        assert_eq!(ok.clone().evaluate_owned(), 10);
    }
}

/// EvaluateExt combinator behavior on Option and Result
#[cfg(test)]
mod evaluate_ext_combinators {
    use super::*;

    #[test]
    fn test_option_map_identity_matches_evaluate() {
        let some = Some(5);
        let id = |x: i32| x;
        assert_eq!(some.map_evaluate(id), some.evaluate());

        let some2 = Some(7);
        assert_eq!(some2.clone().map_evaluate_owned(id), some2.evaluate_owned());
    }

    #[test]
    fn test_option_bind_and_combine() {
        let base = Some(10);
        let inc = base.bind_evaluate(|x: i32| Thunk::new(move || x.saturating_add(3)));
        assert_eq!(inc, 13);

        let a = Some(2);
        let b = Some(3);
        let sum = a.combine_evaluate(&b, |x: i32, y: i32| x.saturating_add(y));
        assert_eq!(sum, 5);

        let prod = Some(2).combine_evaluate_owned(Some(3), |x: i32, y: i32| x.saturating_mul(y));
        assert_eq!(prod, 6);
    }

    #[test]
    fn test_result_map_bind_and_combine_ok() {
        let id = |x: i32| x;
        let ok: Result<i32, i8> = Ok(5);
        assert_eq!(ok.map_evaluate(id), ok.evaluate());
        assert_eq!(ok.clone().map_evaluate_owned(id), ok.evaluate_owned());

        let ok2: Result<i32, i8> = Ok(5);
        let r = ok2.bind_evaluate(|x| Thunk::new(move || x.saturating_add(1)));
        assert_eq!(r, 6);

        let sum = Ok::<i32, i8>(2)
            .combine_evaluate(&Ok::<i32, i8>(3), |x: i32, y: i32| x.saturating_add(y));
        assert_eq!(sum, 5);

        let prod = Ok::<i32, i8>(2)
            .combine_evaluate_owned(Ok::<i32, i8>(3), |x: i32, y: i32| x.saturating_mul(y));
        assert_eq!(prod, 6);
    }

    #[test]
    fn test_filter_evaluate() {
        let some = Some(5);
        let none = Some(-1);
        assert_eq!(some.filter_evaluate(|&x| x > 0), Some(5));
        assert_eq!(none.filter_evaluate(|&x| x > 0), None);

        let ok: Result<i32, i8> = Ok(5);
        let bad: Result<i32, i8> = Ok(-1);
        assert_eq!(ok.filter_evaluate(|&x| x > 0), Some(5));
        assert_eq!(bad.filter_evaluate(|&x| x > 0), None);
    }

    #[test]
    fn test_filter_evaluate_owned() {
        let some = Some(5);
        let none = Some(-1);
        assert_eq!(some.clone().filter_evaluate_owned(|&x| x > 0), Some(5));
        assert_eq!(none.clone().filter_evaluate_owned(|&x| x > 0), None);

        let ok: Result<i32, i8> = Ok(5);
        let bad: Result<i32, i8> = Ok(-1);
        assert_eq!(ok.clone().filter_evaluate_owned(|&x| x > 0), Some(5));
        assert_eq!(bad.clone().filter_evaluate_owned(|&x| x > 0), None);
    }
}

/// QuickCheck properties for Evaluate laws
#[cfg(test)]
mod evaluate_quickcheck_laws {
    use super::*;
    use quickcheck_macros::quickcheck;

    // Idempotence (guard Some/Ok only)
    #[quickcheck]
    fn qc_option_idempotence(m: Option<i32>) -> bool {
        match m {
            Some(_) => m.evaluate() == m.evaluate(),
            None => true,
        }
    }

    #[quickcheck]
    fn qc_result_idempotence(m: Result<i32, i8>) -> bool {
        match m {
            Ok(_) => m.evaluate() == m.evaluate(),
            Err(_) => true,
        }
    }

    // Ref vs Owned consistency (guard Some/Ok only)
    #[quickcheck]
    fn qc_option_ref_owned_consistency(m: Option<i32>) -> bool {
        match m {
            Some(_) => m.clone().evaluate() == m.evaluate_owned(),
            None => true,
        }
    }

    #[quickcheck]
    fn qc_result_ref_owned_consistency(m: Result<i32, i8>) -> bool {
        match m {
            Ok(_) => m.clone().evaluate() == m.evaluate_owned(),
            Err(_) => true,
        }
    }

    // Referential transparency (guard Some/Ok only)
    #[quickcheck]
    fn qc_option_ref_transparency(m: Option<i32>) -> bool {
        let f: fn(i32) -> i32 = |x| x.saturating_mul(2).saturating_add(1);
        match m {
            Some(_) => m.map_evaluate(f) == f(m.evaluate()),
            None => true,
        }
    }

    #[quickcheck]
    fn qc_result_ref_transparency(m: Result<i32, i8>) -> bool {
        let f: fn(i32) -> i32 = |x| x.saturating_add(3).saturating_sub(1);
        match m {
            Ok(_) => m.map_evaluate(f) == f(m.evaluate()),
            Err(_) => true,
        }
    }

    // Consistency (guard Some/Ok only)
    #[quickcheck]
    fn qc_option_consistency(m: Option<i32>) -> bool {
        match &m {
            Some(x) => m.evaluate() == *x,
            None => true,
        }
    }

    #[quickcheck]
    fn qc_result_consistency(m: Result<i32, i8>) -> bool {
        match &m {
            Ok(x) => m.evaluate() == *x,
            Err(_) => true,
        }
    }

    // Combinators: bind with Thunk and combine (guard Some/Ok only)
    #[quickcheck]
    fn qc_option_bind_with_thunk(m: Option<i32>, k: i32) -> bool {
        match &m {
            Some(x) => {
                let res = m.bind_evaluate(|v| Thunk::new(move || v.saturating_add(k)));
                res == x.saturating_add(k)
            },
            None => true,
        }
    }

    #[quickcheck]
    fn qc_option_combine_sum(a: Option<i32>, b: Option<i32>) -> bool {
        match (&a, &b) {
            (Some(_), Some(_)) => {
                let left = a.combine_evaluate(&b, |x, y| x.saturating_add(y));
                let right = a.evaluate().saturating_add(b.evaluate());
                left == right
            },
            _ => true,
        }
    }

    #[quickcheck]
    fn qc_result_combine_sum(a: Result<i32, i8>, b: Result<i32, i8>) -> bool {
        match (&a, &b) {
            (Ok(_), Ok(_)) => {
                let left = a.combine_evaluate(&b, |x, y| x.saturating_add(y));
                let right = a.evaluate().saturating_add(b.evaluate());
                left == right
            },
            _ => true,
        }
    }
}
