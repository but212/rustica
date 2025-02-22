use quickcheck_macros::quickcheck;
use rustica::traits::monad::Monad;
use rustica::traits::pure::Pure;
use super::TestFunctor;

#[test]
fn test_monad_left_identity() {
    let x = 42;
    let f = |x| TestFunctor(x + 1);
    
    // Left identity: return a >>= f = f a
    assert_eq!(TestFunctor::pure(x).bind(f), f(x));
}

#[test]
fn test_monad_right_identity() {
    let m = TestFunctor(42);
    
    // Right identity: m >>= return = m
    assert_eq!(m.bind(TestFunctor::pure), m);
}

#[test]
fn test_monad_associativity() {
    let m = TestFunctor(42);
    let f = |x| TestFunctor(x + 1);
    let g = |x| TestFunctor(x * 2);
    
    // Associativity: (m >>= f) >>= g = m >>= (\x -> f x >>= g)
    assert_eq!(
        m.bind(f).bind(g),
        m.bind(|x| f(x).bind(g))
    );
}

#[quickcheck]
fn prop_monad_left_identity(x: i32) -> bool {
    let f = |x| TestFunctor(x + 1);
    TestFunctor::pure(x).bind(f) == f(x)
}

#[quickcheck]
fn prop_monad_right_identity(x: i32) -> bool {
    let m = TestFunctor(x);
    m.bind(TestFunctor::pure) == m
}

#[quickcheck]
fn prop_monad_associativity(x: i32) -> bool {
    let m = TestFunctor(x);
    let f = |x| TestFunctor(x + 1);
    let g = |x| TestFunctor(x * 2);
    
    m.bind(f).bind(g) == m.bind(|x| f(x).bind(g))
}

#[test]
fn test_monad_composition() {
    let m = TestFunctor(42);
    
    let result = m
        .bind(|x| TestFunctor(x + 1))
        .bind(|x| TestFunctor(x * 2))
        .bind(|x| TestFunctor(x.to_string()));
        
    assert!(result.get().is_string());
}
