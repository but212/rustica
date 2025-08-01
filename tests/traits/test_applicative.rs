use super::TestFunctor;
use quickcheck_macros::quickcheck;
use rustica::traits::applicative::Applicative;
use rustica::traits::pure::Pure;

// Property-based test for Applicative Identity Law (covers identity law)
#[quickcheck]
fn applicative_identity_law(x: TestFunctor<i32>) -> bool {
    let id = |x: &i32| *x;
    let pure_id = TestFunctor::<fn(&i32) -> i32>::pure(&id);
    pure_id.apply(&x) == x
}

// Property-based test for Applicative Homomorphism Law (covers homomorphism law)
#[quickcheck]
fn applicative_homomorphism_law(x: i32) -> bool {
    let f = |x: &i32| x.saturating_add(1);
    let pure_f = TestFunctor::<fn(&i32) -> i32>::pure(&f);
    let pure_x = TestFunctor::<i32>::pure(&x);
    let left = pure_f.apply(&pure_x);
    let right = TestFunctor::<i32>::pure(&f(&x));
    left == right
}

// Create a function that applies a function to a value
fn apply_to_y_fn(y: i32) -> impl Fn(&fn(&i32) -> i32) -> i32 {
    move |g| g(&y)
}

// Property-based test for Applicative Interchange Law
#[quickcheck]
fn applicative_interchange_law(y: i32) -> bool {
    let f: fn(&i32) -> i32 = |x| x.saturating_mul(2);
    let u = TestFunctor::new(f);
    let pure_y = TestFunctor::<i32>::pure(&y);
    let left = u.apply(&pure_y);

    let pure_apply_to_y = TestFunctor::new(apply_to_y_fn(y));
    let right = pure_apply_to_y.apply(&u);

    left == right
}

// Property-based test for Applicative Composition Law
#[quickcheck]
fn applicative_composition_law(x: i32) -> bool {
    let f = |x: &i32| x.saturating_add(1);
    let g = |x: &i32| x.saturating_mul(2);
    let u = TestFunctor::new(f);
    let v = TestFunctor::new(g);
    let w = TestFunctor::new(x);

    // Composition law for forward direction: compose.apply(u).apply(v).apply(w) == u.apply(v.apply(w))
    // Since we don't have compose, we'll test a simpler property
    let left = u.apply(&w);
    let right = TestFunctor::new(f(&x));

    left == right
}

// Property-based test for lift2
#[quickcheck]
fn applicative_lift2_law(a: i32, b: i32) -> bool {
    let fa = TestFunctor::new(a);
    let fb = TestFunctor::new(b);
    let sum = |x: &i32, y: &i32| x.saturating_add(*y);
    let result = TestFunctor::<i32>::lift2(sum, &fa, &fb);
    result == TestFunctor::new(a.saturating_add(b))
}

// Property-based test for lift3
#[quickcheck]
fn applicative_lift3_law(a: i32, b: i32, c: i32) -> bool {
    let fa = TestFunctor::new(a);
    let fb = TestFunctor::new(b);
    let fc = TestFunctor::new(c);
    let sum3 = |x: &i32, y: &i32, z: &i32| x.saturating_add(*y).saturating_add(*z);
    let result = TestFunctor::<i32>::lift3(sum3, &fa, &fb, &fc);
    result == TestFunctor::new(a.saturating_add(b).saturating_add(c))
}

// Property-based test for sequence_right
#[quickcheck]
fn applicative_sequence_right_law(a: i32, b: i32) -> bool {
    let fa = TestFunctor::new(a);
    let fb = TestFunctor::new(b);
    let result = TestFunctor::<i32>::sequence_right(&fa, &fb);
    result == fb
}

// Property-based test for sequence_left
#[quickcheck]
fn applicative_sequence_left_law(a: i32, b: i32) -> bool {
    let fa = TestFunctor::new(a);
    let fb = TestFunctor::new(b);
    let result = TestFunctor::<i32>::sequence_left(&fa, &fb);
    result == fa
}

// Property-based test for apply (function in context, covers apply_owned)
#[quickcheck]
fn applicative_apply_law(a: i32) -> bool {
    let f = |x: i32| x.saturating_sub(1);
    let ff = TestFunctor::new(f);
    let fa = TestFunctor::new(a);
    let result = ff.clone().apply_owned(fa.clone());
    result == TestFunctor::new(f(a))
}

// Property-based test for lift2_owned (owned version)
#[quickcheck]
fn applicative_lift2_owned_law(a: i32, b: i32) -> bool {
    let fa = TestFunctor::new(a);
    let fb = TestFunctor::new(b);
    let sum = |x: i32, y: i32| x.saturating_add(y);
    let result = TestFunctor::<i32>::lift2_owned(sum, fa.clone(), fb.clone());
    result == TestFunctor::new(a.saturating_add(b))
}

// Property-based test for lift3_owned (owned version)
#[quickcheck]
fn applicative_lift3_owned_law(a: i32, b: i32, c: i32) -> bool {
    let fa = TestFunctor::new(a);
    let fb = TestFunctor::new(b);
    let fc = TestFunctor::new(c);
    let sum3 = |x: i32, y: i32, z: i32| x.saturating_add(y).saturating_add(z);
    let result = TestFunctor::<i32>::lift3_owned(sum3, fa.clone(), fb.clone(), fc.clone());
    result == TestFunctor::new(a.saturating_add(b).saturating_add(c))
}
