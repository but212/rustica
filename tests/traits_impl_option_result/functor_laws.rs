use rustica::traits::functor::Functor;

/// Test the Functor Identity Law: fmap(id) = id
///
/// For any functor F and value x, mapping the identity function
/// should be equivalent to the identity operation on the functor.
#[cfg(test)]
mod functor_identity_law {
    use super::*;

    #[test]
    fn test_option_identity_law() {
        let some_value = Some(42);
        let none_value: Option<i32> = None;

        // Identity function
        let id = |x: &i32| *x;

        // Test: fmap(id) should equal the original value
        assert_eq!(some_value.fmap(&id), some_value);
        assert_eq!(none_value.fmap(&id), none_value);
    }

    #[test]
    fn test_result_identity_law() {
        let ok_value: Result<i32, &str> = Ok(42);
        let err_value: Result<i32, &str> = Err("error");

        // Identity function
        let id = |x: &i32| *x;

        // Test: fmap(id) should equal the original value
        assert_eq!(ok_value.fmap(&id), ok_value);
        assert_eq!(err_value.fmap(&id), err_value);
    }

    #[test]
    fn test_vec_identity_law() {
        let vec_value = vec![1, 2, 3];
        let empty_vec: Vec<i32> = vec![];

        // Identity function
        let id = |x: &i32| *x;

        // Test: fmap(id) should equal the original value
        assert_eq!(vec_value.fmap(&id), vec_value);
        assert_eq!(empty_vec.fmap(&id), empty_vec);
    }
}

/// Test the Functor Composition Law: fmap(g ∘ f) = fmap(g) ∘ fmap(f)
///
/// For any functor F and functions f and g, mapping the composition
/// of f and g should be equivalent to first mapping f then mapping g.
#[cfg(test)]
mod functor_composition_law {
    use super::*;

    #[test]
    fn test_option_composition_law() {
        let some_value = Some(5);
        let none_value: Option<i32> = None;

        let f = |x: &i32| x * 2;
        let g = |x: &i32| x + 1;
        let composed = |x: &i32| g(&f(x)); // g ∘ f

        // Test: fmap(g ∘ f) = fmap(g) ∘ fmap(f)
        assert_eq!(some_value.fmap(&composed), some_value.fmap(&f).fmap(&g));
        assert_eq!(none_value.fmap(&composed), none_value.fmap(&f).fmap(&g));
    }

    #[test]
    fn test_result_composition_law() {
        let ok_value: Result<i32, &str> = Ok(5);
        let err_value: Result<i32, &str> = Err("error");

        let f = |x: &i32| x * 2;
        let g = |x: &i32| x + 1;
        let composed = |x: &i32| g(&f(x)); // g ∘ f

        // Test: fmap(g ∘ f) = fmap(g) ∘ fmap(f)
        assert_eq!(ok_value.fmap(&composed), ok_value.fmap(&f).fmap(&g));
        assert_eq!(err_value.fmap(&composed), err_value.fmap(&f).fmap(&g));
    }

    #[test]
    fn test_vec_composition_law() {
        let vec_value = vec![1, 2, 3];
        let empty_vec: Vec<i32> = vec![];

        let f = |x: &i32| x * 2;
        let g = |x: &i32| x + 1;
        let composed = |x: &i32| g(&f(x)); // g ∘ f

        // Test: fmap(g ∘ f) = fmap(g) ∘ fmap(f)
        assert_eq!(vec_value.fmap(&composed), vec_value.fmap(&f).fmap(&g));
        assert_eq!(empty_vec.fmap(&composed), empty_vec.fmap(&f).fmap(&g));
    }
}

/// Test that functors preserve structure
///
/// This ensures that the functor operations don't change the "shape"
/// of the data structure, only the contained values.
#[cfg(test)]
mod functor_structure_preservation {
    use super::*;

    #[test]
    fn test_option_structure_preservation() {
        let some_value = Some(42);
        let none_value: Option<i32> = None;

        let f = |x: &i32| format!("value: {}", x);

        // Some should remain Some, None should remain None
        assert!(some_value.fmap(&f).is_some());
        assert!(none_value.fmap(&f).is_none());
    }

    #[test]
    fn test_result_structure_preservation() {
        let ok_value: Result<i32, &str> = Ok(42);
        let err_value: Result<i32, &str> = Err("error");

        let f = |x: &i32| format!("value: {}", x);

        // Ok should remain Ok, Err should remain Err
        assert!(ok_value.fmap(&f).is_ok());
        assert!(err_value.fmap(&f).is_err());

        // Error value should be unchanged
        if let Err(e) = err_value.fmap(&f) {
            assert_eq!(e, "error");
        }
    }

    #[test]
    fn test_vec_structure_preservation() {
        let vec_value = vec![1, 2, 3];
        let empty_vec: Vec<i32> = vec![];

        let f = |x: &i32| x.to_string();

        // Length should be preserved
        assert_eq!(vec_value.fmap(&f).len(), vec_value.len());
        assert_eq!(empty_vec.fmap(&f).len(), empty_vec.len());
    }
}

#[cfg(test)]
mod functor_quickcheck_laws {
    use super::*;
    use quickcheck_macros::quickcheck;

    // Identity Law: fmap(id) == id
    #[quickcheck]
    fn qc_option_identity(m: Option<i32>) -> bool {
        let id: fn(&i32) -> i32 = |x| *x;
        m.fmap(&id) == m
    }

    #[quickcheck]
    fn qc_result_identity(x: i32, e: i8, is_ok: bool) -> bool {
        let m: Result<i32, i8> = if is_ok { Ok(x) } else { Err(e) };
        let id: fn(&i32) -> i32 = |t| *t;
        m.clone().fmap(&id) == m
    }

    // Composition Law: fmap(g ∘ f) == fmap(g) ∘ fmap(f)
    #[quickcheck]
    fn qc_option_composition(m: Option<i32>) -> bool {
        let f: fn(&i32) -> i32 = |x| x.saturating_mul(2);
        let g: fn(&i32) -> i32 = |x| x.saturating_add(1);
        let composed = |x: &i32| g(&f(x));
        m.fmap(&composed) == m.fmap(&f).fmap(&g)
    }

    #[quickcheck]
    fn qc_result_composition(m: Result<i32, i8>) -> bool {
        let f: fn(&i32) -> i32 = |x| x.saturating_mul(2);
        let g: fn(&i32) -> i32 = |x| x.saturating_add(1);
        let composed = |x: &i32| g(&f(x));
        m.clone().fmap(&composed) == m.fmap(&f).fmap(&g)
    }

    // Structure preservation: shape (Some/None, Ok/Err) is preserved
    #[quickcheck]
    fn qc_option_structure_preserved(m: Option<i32>) -> bool {
        let f: fn(&i32) -> i64 = |x| (*x as i64).saturating_mul(3);
        m.fmap(&f).is_some() == m.is_some()
    }

    #[quickcheck]
    fn qc_result_structure_preserved(m: Result<i32, i8>) -> bool {
        let f: fn(&i32) -> i64 = |x| (*x as i64).saturating_add(10);
        m.fmap(&f).is_ok() == m.is_ok()
    }
}
