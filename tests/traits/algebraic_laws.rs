#![allow(deprecated)]

use super::TestFunctor;
use quickcheck_macros::quickcheck;
use rustica::datatypes::choice::Choice;
use rustica::datatypes::validated::Validated;
use rustica::prelude::*;

// --- Macro-based Functor Laws for Concrete Standard Types ---
test_functor_laws!(
    option_functor,
    Option<i32>,
    |a: i32| a.saturating_add(1),
    |b: i32| b.saturating_mul(2)
);

test_functor_laws!(
    result_functor,
    Result<i32, i32>,
    |a: i32| a.saturating_add(1),
    |b: i32| b.saturating_mul(2)
);

test_functor_laws!(
    vec_functor,
    Vec<i32>,
    |a: i32| a.saturating_add(1),
    |b: i32| b.saturating_mul(2)
);

// --- Choice Functor Laws ---
#[test]
fn test_choice_functor_laws() {
    let c = Choice::new(10, vec![20, 30]);

    // Identity: fmap id == id
    assert_eq!(c.clone().fmap(|x| x), c);

    // Composition: fmap (g . f) == fmap g . fmap f
    let f = |x: i32| x.saturating_add(5);
    let g = |x: i32| x.saturating_mul(3);
    assert_eq!(c.clone().fmap(move |x| g(f(x))), c.fmap(f).fmap(g));
}

// --- Functor Laws with TestFunctor ---
#[quickcheck]
fn functor_identity_law(x: TestFunctor<i32>) -> bool {
    x.clone().fmap(|a| a) == x
}

#[quickcheck]
fn functor_composition_law(x: TestFunctor<i32>) -> bool {
    let f = |a: i32| a.saturating_add(1);
    let g = |a: i32| a.saturating_mul(2);
    x.clone().fmap(move |a| f(g(a))) == x.fmap(g).fmap(f)
}

// --- Applicative Laws with TestFunctor ---
#[quickcheck]
fn applicative_identity_law(x: TestFunctor<i32>) -> bool {
    let id: fn(i32) -> i32 = |x: i32| x;
    TestFunctor::<fn(i32) -> i32>::pure(id).apply(x.clone()) == x
}

#[quickcheck]
fn applicative_homomorphism_law(val: i32) -> bool {
    let f: fn(i32) -> i32 = |x: i32| x.saturating_add(1);
    let pure_f = TestFunctor::<fn(i32) -> i32>::pure(f);
    let pure_val = TestFunctor::<i32>::pure(val);

    pure_f.apply(pure_val) == TestFunctor::new(f(val))
}

// --- Validated Applicative Laws (Composition, Interchange, Homomorphism, Identity) ---
#[test]
fn test_validated_applicative_laws() {
    type Val<T> = Validated<T, &'static str>;

    let f: fn(i32) -> i32 = |x| x.saturating_add(10);
    let g: fn(i32) -> i32 = |x| x.saturating_mul(2);

    // 1. Identity: pure(id).apply(v) == v
    let id: fn(i32) -> i32 = |x| x;
    let v_valid: Val<i32> = Validated::valid(42);
    assert_eq!(
        <Val<fn(i32) -> i32> as Pure>::pure(id).apply(v_valid.clone()),
        v_valid
    );

    let v_invalid: Val<i32> = Validated::invalid("err");
    assert_eq!(
        <Val<fn(i32) -> i32> as Pure>::pure(id).apply(v_invalid.clone()),
        v_invalid
    );

    // 2. Homomorphism: pure(f).apply(pure(x)) == pure(f(x))
    let pure_f: Val<fn(i32) -> i32> = <Val<fn(i32) -> i32> as Pure>::pure(f);
    let pure_x: Val<i32> = <Val<i32> as Pure>::pure(5);
    assert_eq!(pure_f.apply(pure_x), <Val<i32> as Pure>::pure(f(5)));

    // 3. Interchange: u.apply(pure(y)) == pure(|f| f(y)).apply(u)
    let u_valid: Val<fn(i32) -> i32> = <Val<fn(i32) -> i32> as Pure>::pure(f);
    let y = 7;
    let lhs = u_valid.apply(<Val<i32> as Pure>::pure(y));
    let rhs = <Val<fn(fn(i32) -> i32) -> i32> as Pure>::pure(|fn_obj: fn(i32) -> i32| fn_obj(y))
        .apply(<Val<fn(i32) -> i32> as Pure>::pure(f));
    assert_eq!(lhs, rhs);

    // 4. Composition: pure(compose).apply(u).apply(v).apply(w) == u.apply(v.apply(w))
    let u = <Val<fn(i32) -> i32> as Pure>::pure(f);
    let v = <Val<fn(i32) -> i32> as Pure>::pure(g);
    let w_valid = <Val<i32> as Pure>::pure(3);
    assert_eq!(u.apply(v.apply(w_valid)), <Val<i32> as Pure>::pure(f(g(3))));

    let w_invalid: Val<i32> = Validated::invalid("e1");
    assert_eq!(
        <Val<fn(i32) -> i32> as Pure>::pure(f)
            .apply(<Val<fn(i32) -> i32> as Pure>::pure(g).apply(w_invalid.clone())),
        w_invalid
    );

    // 5. Error Accumulation in Applicative
    let err_u: Val<fn(i32) -> i32> = Validated::invalid("err_fn");
    let err_v: Val<i32> = Validated::invalid("err_val");
    let combined = err_u.apply(err_v);
    assert!(matches!(combined, Validated::Invalid(ref errors) if errors.len() == 2));
}

// --- Monad Laws for Result, Option, Vec ---
#[quickcheck]
fn test_option_monad_laws(val: i32) -> bool {
    let f = |x: i32| {
        if x > 0 {
            Some(x.saturating_add(1))
        } else {
            None
        }
    };
    let g = |x: i32| Some(x.saturating_mul(2));

    // Left identity: pure(a).bind(f) == f(a)
    let left_id = Option::<i32>::pure(val).bind(f) == f(val);

    // Right identity: m.bind(pure) == m
    let opt = Some(val);
    let right_id = opt.bind(Option::<i32>::pure) == opt;

    // Associativity: m.bind(f).bind(g) == m.bind(|x| f(x).bind(g))
    let assoc = opt.bind(f).bind(g) == opt.bind(|x| f(x).bind(g));

    left_id && right_id && assoc
}

#[quickcheck]
fn test_result_monad_laws(val: i32) -> bool {
    type Res<T> = Result<T, i32>;
    let f = |x: i32| -> Res<i32> {
        if x % 2 == 0 {
            Ok(x.saturating_add(1))
        } else {
            Err(x)
        }
    };
    let g = |x: i32| -> Res<i32> { Ok(x.saturating_mul(3)) };

    // Left identity: pure(a).bind(f) == f(a)
    let left_id = Res::<i32>::pure(val).bind(f) == f(val);

    // Right identity: m.bind(pure) == m
    let res: Res<i32> = Ok(val);
    let right_id = res.bind(Res::<i32>::pure) == res;

    // Associativity
    let assoc = res.bind(f).bind(g) == res.bind(|x| f(x).bind(g));

    left_id && right_id && assoc
}

// --- Monad Laws with TestFunctor ---
#[quickcheck]
fn monad_left_identity_law(val: i32) -> bool {
    let f = |x: i32| TestFunctor::new(x.saturating_add(1));
    TestFunctor::<i32>::pure(val).bind(f) == f(val)
}

#[quickcheck]
fn monad_associativity_law(x: TestFunctor<i32>) -> bool {
    let f = |a: i32| TestFunctor::new(a.saturating_add(1));
    let g = |a: i32| TestFunctor::new(a.saturating_mul(2));

    x.clone().bind(f).bind(g) == x.bind(move |a| f(a).bind(g))
}

#[test]
fn vec_lift3_matches_cartesian_product() {
    let expected = vec![
        (1, 10, 100),
        (1, 10, 200),
        (1, 20, 100),
        (1, 20, 200),
        (2, 10, 100),
        (2, 10, 200),
        (2, 20, 100),
        (2, 20, 200),
    ];

    let result = Vec::<i32>::lift3(
        |a, b, c| (a, b, c),
        vec![1, 2],
        vec![10, 20],
        vec![100, 200],
    );

    assert_eq!(result, expected);
}

#[test]
fn test_product_monoid_i8() {
    use rustica::traits::monoid::Monoid;
    use rustica::traits::semigroup::Semigroup;

    #[derive(Debug, PartialEq, Eq, Clone, Copy)]
    struct TestProduct(i8);

    impl Semigroup for TestProduct {
        fn combine(self, other: Self) -> Self {
            TestProduct(self.0 * other.0)
        }
    }

    impl Monoid for TestProduct {
        fn empty() -> Self {
            TestProduct(1)
        }
    }

    let empty: TestProduct = TestProduct::empty();
    assert_eq!(empty.0, 1i8);

    let val = TestProduct(5i8);
    assert_eq!(val.combine(empty), val);
    assert_eq!(empty.combine(val), val);
}
