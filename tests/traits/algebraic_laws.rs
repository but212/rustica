use super::TestFunctor;
use quickcheck_macros::quickcheck;
use rustica::prelude::*;

// --- Functor Laws ---

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

// --- Applicative Laws ---

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

// --- Monad Laws ---

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
    use rustica::datatypes::wrapper::product::Product;
    use rustica::traits::monoid::Monoid;
    use rustica::traits::semigroup::Semigroup;

    let empty: Product<i8> = Product::empty();
    assert_eq!(empty.0, 1i8);

    let val = Product(5i8);
    assert_eq!(val.combine(empty), val);
    assert_eq!(empty.combine(val), val);
}
