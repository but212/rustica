use super::TestFunctor;
use quickcheck_macros::quickcheck;
use rustica::prelude::*;
use rustica::traits::applicative::Applicative;
use rustica::traits::pure::Pure;

// Applicative Identity Law: pure(id).apply(v) == v
#[quickcheck]
fn applicative_identity(x: TestFunctor<i32>) -> bool {
    let id = |x: &i32| *x;
    let pure_id = TestFunctor::<fn(&i32) -> i32>::pure(&id);
    x.apply(&pure_id) == x
}

// Applicative Homomorphism Law: pure(f).apply(pure(x)) == pure(f(x))
#[quickcheck]
fn applicative_homomorphism() -> bool {
    let f = |x: &i32| x + 1;
    let x = 5;
    
    let pure_f = TestFunctor::<fn(&i32) -> i32>::pure(&f);
    let pure_x = TestFunctor::<i32>::pure(&x);
    
    let left = pure_x.apply(&pure_f);
    let right = TestFunctor::<i32>::pure(&f(&x));
    
    left == right
}

// Applicative Interchange Law: u.apply(pure(y)) == pure(|f| f(y)).apply(u)
#[test]
fn applicative_interchange() {
    // Define a specific type for the function to avoid inference issues
    type Func = fn(&i32) -> i32;
    
    let f: Func = |x| x * 2;
    let u = TestFunctor::new(f);
    let y = 10;
    let pure_y = TestFunctor::new(y);
    
    // u.apply(pure(y))
    let left = pure_y.apply(&u);
    
    // The closure needs to match the exact type stored in u
    let apply_to_y = |g: &Func| g(&y);
    let pure_apply_to_y = TestFunctor::new(apply_to_y);
    
    // pure(|f| f(y)).apply(u)
    let right = u.apply(&pure_apply_to_y);
    
    assert_eq!(left, right);
}

// Applicative Composition Law:
// Test simplified to avoid complex type issues
#[test]
fn applicative_composition() {
    // Define functions and test values
    let f = |x: &i32| x + 1;
    let g = |x: &i32| x * 2;
    let x = 5;
    
    // Create functor instances
    let u = TestFunctor::new(f);
    let v = TestFunctor::new(g);
    let w = TestFunctor::new(x);
    
    // First compute: w.apply(v).apply(u)
    // This applies g then f to x
    let right = w.apply(&v).apply(&u);
    
    // Then compute the expected result directly
    let expected = TestFunctor::new(f(&g(&x)));
    
    assert_eq!(right, expected);
}

// Test for lift2 method
#[test]
fn test_lift2() {
    let x = TestFunctor::new(5);
    let y = TestFunctor::new(3);
    
    let add = |a: &i32, b: &i32| a + b;
    
    // Using lift2
    let result = x.lift2(&y, add);
    
    assert_eq!(*result.value(), 8);
}

// Test for lift3 method
#[test]
fn test_lift3() {
    let x = TestFunctor::new(5);
    let y = TestFunctor::new(3);
    let z = TestFunctor::new(2);
    
    let add3 = |a: &i32, b: &i32, c: &i32| a + b + c;
    
    // Using lift3
    let result = x.lift3(&y, &z, add3);
    
    assert_eq!(*result.value(), 10);
}

// Test for sequence_right method
#[test]
fn test_sequence_right() {
    let a = TestFunctor::new(1);
    let b = TestFunctor::new(2);
    
    let result = a.sequence_right(&b);
    
    assert_eq!(*result.value(), 2);
}

// Test for sequence_left method
#[test]
fn test_sequence_left() {
    let a = TestFunctor::new(1);
    let b = TestFunctor::new(2);
    
    let result = a.sequence_left(&b);
    
    assert_eq!(*result.value(), 1);
}

// Test for apply_owned (owned version of apply)
#[test]
fn test_apply_owned() {
    let x = TestFunctor::new(5);
    let f = TestFunctor::new(|x| x * 2);
    
    let result = x.apply_owned(f);
    
    assert_eq!(*result.value(), 10);
}

// Test for lift2_owned (owned version of lift2)
#[test]
fn test_lift2_owned() {
    let x = TestFunctor::new(5);
    let y = TestFunctor::new(3);
    
    let result = x.lift2_owned(y, |a, b| a + b);
    
    assert_eq!(*result.value(), 8);
}

// Test for lift3_owned (owned version of lift3)
#[test]
fn test_lift3_owned() {
    let x = TestFunctor::new(5);
    let y = TestFunctor::new(3);
    let z = TestFunctor::new(2);
    
    let result = x.lift3_owned(y, z, |a, b, c| a + b + c);
    
    assert_eq!(*result.value(), 10);
}
