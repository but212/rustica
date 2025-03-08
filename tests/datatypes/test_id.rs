use rustica::datatypes::id::Id;
use rustica::prelude::*;

#[test]
fn test_id_creation_and_access() {
    // Test creation and access of Id
    let id_int = Id::new(42);
    let id_string = Id::new("hello".to_string());
    
    assert_eq!(*id_int.value(), 42);
    assert_eq!(*id_string.value(), "hello");
}

#[test]
fn test_id_functor() {
    // Test functor properties of Id
    let x = Id::new(42);
    
    // Test fmap
    let doubled = x.fmap(|n| n * 2);
    let identity = x.fmap(|n| *n);
    
    assert_eq!(*doubled.value(), 84);
    assert_eq!(*identity.value(), 42);
    
    // Test functor laws
    // 1. Identity: fmap(id) == id
    let id_law = x.fmap(|n| *n);
    assert_eq!(*id_law.value(), *x.value());
    
    // 2. Composition: fmap(f . g) == fmap(f) . fmap(g)
    let f = |n: &i32| n * 2;
    let g = |n: &i32| n + 3;
    let composition1 = x.fmap(|n| f(&g(n)));
    let composition2 = x.fmap(g).fmap(f);
    assert_eq!(*composition1.value(), *composition2.value());
}

#[test]
fn test_id_pure() {
    // Test pure function of Id
    let pure_int = Id::<i32>::pure(&42);
    let pure_string = Id::<String>::pure(&"hello".to_string());
    
    assert_eq!(*pure_int.value(), 42);
    assert_eq!(*pure_string.value(), "hello");
}

#[test]
fn test_id_applicative() {
    // Test applicative properties of Id
    let x = Id::new(2);
    let y = Id::new(3);
    let z = Id::new(4);
    
    // Test apply
    let add_one = Id::new(|x: &i32| x + 1);
    let result = x.apply(&add_one);
    assert_eq!(*result.value(), 3);
    
    // Test lift2
    let add = |a: &i32, b: &i32| a + b;
    let sum = x.lift2(&y, &add);
    assert_eq!(*sum.value(), 5);
    
    // Test lift3
    let multiply = |a: &i32, b: &i32, c: &i32| a * b * c;
    let product = x.lift3(&y, &z, &multiply);
    assert_eq!(*product.value(), 24);
}

#[test]
fn test_id_monad() {
    // Test monad properties of Id
    let x = Id::new(42);
    
    // Test bind
    let f = |n: &i32| Id::new(n * 2);
    let g = |n: &i32| Id::new(n + 3);
    
    let bind_result = x.bind(&f);
    assert_eq!(*bind_result.value(), 84);
    
    // Test join
    let nested = Id::new(x.clone());
    let flattened = nested.join();
    assert_eq!(*flattened.value(), 42);
    
    // Test monad laws
    // 1. Left identity: pure(a).bind(f) == f(a)
    let left_identity = Id::<i32>::pure(&42).bind(&f);
    assert_eq!(*left_identity.value(), *f(&42).value());
    
    // 2. Right identity: m.bind(pure) == m
    let right_identity = x.bind(|n| Id::<i32>::pure(n));
    assert_eq!(*right_identity.value(), *x.value());
    
    // 3. Associativity: m.bind(f).bind(g) == m.bind(|x| f(x).bind(g))
    let assoc_left = x.bind(f).bind(g);
    let assoc_right = x.bind(|n| f(n).bind(&g));
    assert_eq!(*assoc_left.value(), *assoc_right.value());
}

#[test]
fn test_id_chaining() {
    // Test chaining of Id
    let x = Id::new(42);
    let result = x
        .fmap(|n| n + 1)
        .fmap(|n| n * 2)
        .fmap(|n| n.to_string());
    
    assert_eq!(*result.value(), "86");
}

#[test]
fn test_id_clone() {
    // Test cloning of Id
    let x = Id::new(42);
    let y = x.clone();
    assert_eq!(*x.value(), *y.value());
}