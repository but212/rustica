use rustica::traits::applicative::Applicative;
use rustica::traits::pure::Pure;

/// Test the Applicative Identity Law: pure(id) <*> v = v
///
/// Applying the identity function wrapped in the applicative context
/// should leave the value unchanged.
#[cfg(test)]
mod applicative_identity_law {
    use super::*;

    #[test]
    fn test_option_identity_law() {
        let some_value = Some(42);
        let none_value: Option<i32> = None;

        // Identity function wrapped in applicative context
        let id_fn = |x: &i32| *x;
        let pure_id = <Option<fn(&i32) -> i32> as Pure>::pure(&id_fn);

        // Test: pure(id) <*> v = v
        assert_eq!(Applicative::apply(&pure_id, &some_value), some_value);
        assert_eq!(Applicative::apply(&pure_id, &none_value), none_value);
    }

    #[test]
    fn test_result_identity_law() {
        let ok_value: Result<i32, &str> = Ok(42);
        let err_value: Result<i32, &str> = Err("error");

        // Identity function wrapped in applicative context
        let id_fn = |x: &i32| *x;
        let pure_id = <Result<fn(&i32) -> i32, &str> as Pure>::pure(&id_fn);

        // Test: pure(id) <*> v = v
        assert_eq!(Applicative::apply(&pure_id, &ok_value), ok_value);
        assert_eq!(Applicative::apply(&pure_id, &err_value), err_value);
    }

    #[test]
    fn test_vec_identity_law() {
        let vec_value = vec![1, 2, 3];
        let empty_vec: Vec<i32> = vec![];

        // Identity function wrapped in applicative context
        let id_fn = |x: &i32| *x;
        let pure_id = <Vec<fn(&i32) -> i32> as Pure>::pure(&id_fn);

        // Test: pure(id) <*> v = v
        assert_eq!(Applicative::apply(&pure_id, &vec_value), vec_value);
        assert_eq!(Applicative::apply(&pure_id, &empty_vec), empty_vec);
    }
}

/// Test the Applicative Composition Law: pure(∘) <*> u <*> v <*> w = u <*> (v <*> w)
///
/// Function composition should be associative in the applicative context.
#[cfg(test)]
mod applicative_composition_law {
    use rustica::traits::applicative::Applicative;

    #[test]
    fn test_option_composition_law() {
        // u: F (B -> C), v: F (A -> B), w: F A
        let u: Option<fn(&i32) -> i32> = Some(|x| x * 2);
        let v: Option<fn(&i32) -> i32> = Some(|x| x + 1);
        let w: Option<i32> = Some(5);

        // Left: pure(compose) <*> u <*> v <*> w
        // Use lift3 to express pure(compose) application directly
        let left = Option::<i32>::lift3(
            |f: &fn(&i32) -> i32, g: &fn(&i32) -> i32, x: &i32| f(&g(x)),
            &u,
            &v,
            &w,
        );

        // Right: u <*> (v <*> w)
        let vw = Applicative::apply(&v, &w);
        let right = Applicative::apply(&u, &vw);

        assert_eq!(left, right);
    }
}

/// Test the Applicative Homomorphism Law: pure(f) <*> pure(x) = pure(f(x))
///
/// Applying a pure function to a pure value should be equivalent to
/// applying the function directly and then wrapping the result.
#[cfg(test)]
mod applicative_homomorphism_law {
    use super::*;

    #[test]
    fn test_option_homomorphism_law() {
        let value = 42;
        let f = |x: &i32| x * 2;

        // Left side: pure(f) <*> pure(x)
        let pure_f = <Option<fn(&i32) -> i32> as Pure>::pure(&f);
        let pure_x = <Option<i32> as Pure>::pure(&value);
        let left_side = Applicative::apply(&pure_f, &pure_x);

        // Right side: pure(f(x))
        let right_side = <Option<i32> as Pure>::pure(&f(&value));

        assert_eq!(left_side, right_side);
    }

    #[test]
    fn test_result_homomorphism_law() {
        let value = 42;
        let f = |x: &i32| x * 2;

        // Left side: pure(f) <*> pure(x)
        let pure_f = <Result<fn(&i32) -> i32, &str> as Pure>::pure(&f);
        let pure_x = <Result<i32, &str> as Pure>::pure(&value);
        let left_side = Applicative::apply(&pure_f, &pure_x);

        // Right side: pure(f(x))
        let right_side = <Result<i32, &str> as Pure>::pure(&f(&value));

        assert_eq!(left_side, right_side);
    }

    #[test]
    fn test_vec_homomorphism_law() {
        let value = 42;
        let f = |x: &i32| x * 2;

        // Left side: pure(f) <*> pure(x)
        let pure_f = <Vec<fn(&i32) -> i32> as Pure>::pure(&f);
        let pure_x = <Vec<i32> as Pure>::pure(&value);
        let left_side = Applicative::apply(&pure_f, &pure_x);

        // Right side: pure(f(x))
        let right_side = <Vec<i32> as Pure>::pure(&f(&value));

        assert_eq!(left_side, right_side);
    }
}

/// Test the Applicative Interchange Law: u <*> pure(y) = pure($ y) <*> u
///
/// The order of application should not matter when one argument is pure.
#[cfg(test)]
mod applicative_interchange_law {
    use super::*;

    #[test]
    fn test_option_interchange_law() {
        let f: Option<fn(&i32) -> i32> = Some(|x: &i32| x * 2);
        let y = 42;

        // Left: u <*> pure(y)
        let pure_y = <Option<i32> as Pure>::pure(&y);
        let left = Applicative::apply(&f, &pure_y);

        // Right: pure($) <*> u <*> pure(y)  ≡  lift2(|f, y| f(y), u, pure(y))
        // Directly expresses applying the function to the value without ignoring params
        let right = Option::<i32>::lift2(
            |func: &fn(&i32) -> i32, y_ref: &i32| func(y_ref),
            &f,
            &pure_y,
        );

        assert_eq!(left, right);
    }
}

/// Test Applicative-Functor relationship: fmap(f, x) = pure(f) <*> x
///
/// Functor's fmap should be equivalent to applying a pure function
/// in the applicative context.
#[cfg(test)]
mod applicative_functor_relationship {
    use super::*;
    use rustica::traits::functor::Functor;

    #[test]
    fn test_option_functor_applicative_relationship() {
        let some_value = Some(42);
        let none_value: Option<i32> = None;
        let f = |x: &i32| x * 2;

        // Left side: fmap(f, x)
        let fmap_result_some = some_value.fmap(&f);
        let fmap_result_none = none_value.fmap(&f);

        // Right side: pure(f) <*> x
        let pure_f = <Option<fn(&i32) -> i32> as Pure>::pure(&f);
        let apply_result_some = Applicative::apply(&pure_f, &some_value);
        let apply_result_none = Applicative::apply(&pure_f, &none_value);

        assert_eq!(fmap_result_some, apply_result_some);
        assert_eq!(fmap_result_none, apply_result_none);
    }

    #[test]
    fn test_result_functor_applicative_relationship() {
        let ok_value: Result<i32, &str> = Ok(42);
        let err_value: Result<i32, &str> = Err("error");
        let f = |x: &i32| x * 2;

        // Left side: fmap(f, x)
        let fmap_result_ok = ok_value.fmap(&f);
        let fmap_result_err = err_value.fmap(&f);

        // Right side: pure(f) <*> x
        let pure_f = <Result<fn(&i32) -> i32, &str> as Pure>::pure(&f);
        let apply_result_ok = Applicative::apply(&pure_f, &ok_value);
        let apply_result_err = Applicative::apply(&pure_f, &err_value);

        assert_eq!(fmap_result_ok, apply_result_ok);
        assert_eq!(fmap_result_err, apply_result_err);
    }
}
