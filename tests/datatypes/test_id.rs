use rustica::datatypes::id::Id;
use rustica::prelude::*;

#[test]
fn test_id_creation_and_access() {
    // Test creation and access of Id
    let id_int = Id::new(42);
    let id_string = Id::new("hello".to_string());

    assert_eq!(id_int.unwrap(), 42);
    assert_eq!(id_string.clone().unwrap(), "hello");

    // Test the new as_ref method
    assert_eq!(id_int.as_ref(), &42);
    assert_eq!(id_string.as_ref(), &"hello".to_string());

    // Test consuming the value
    let id_consume = Id::new(100);
    assert_eq!(id_consume.into_inner(), 100);

    // Test value_or method
    let id_default = Id::new(42);
    assert_eq!(id_default.unwrap(), 42);
}

#[test]
fn test_id_functor() {
    // Test functor properties of Id
    let x = Id::new(42);

    // Test fmap
    let doubled = x.fmap(|n| n * 2);
    let identity = x.fmap(|n| *n);

    assert_eq!(doubled.unwrap(), 84);
    assert_eq!(identity.unwrap(), 42);

    // Test owned mapping
    let owned_map = Id::new(42).fmap(|n| n * 2);
    assert_eq!(owned_map.unwrap(), 84);

    // Test fmap_owned
    let owned_fmap = Id::new(42).fmap_owned(|n| n * 2);
    assert_eq!(owned_fmap.unwrap(), 84);

    // Test functor laws
    // 1. Identity: fmap(id) == id
    let id_law = x.fmap(|n| *n);
    assert_eq!(id_law.unwrap(), x.unwrap());

    // 2. Composition: fmap(f . g) == fmap(f) . fmap(g)
    let f = |n: &i32| n * 2;
    let g = |n: &i32| n + 3;
    let composition1 = x.fmap(|n| f(&g(n)));
    let composition2 = x.fmap(g).fmap(f);
    assert_eq!(composition1.unwrap(), composition2.unwrap());
}

#[test]
fn test_id_pure() {
    // Test pure function of Id
    let pure_int = Id::<i32>::pure(&42);
    let pure_string = Id::<String>::pure(&"hello".to_string());

    assert_eq!(pure_int.unwrap(), 42);
    assert_eq!(pure_string.unwrap(), "hello");
}

#[test]
fn test_id_applicative() {
    // Test applicative properties of Id
    let x = Id::new(2);
    let y = Id::new(3);
    let z = Id::new(4);

    // Test apply
    let add_one = Id::new(|x: &i32| x + 1);
    let result = add_one.apply(&x);
    assert_eq!(result.unwrap(), 3);

    // Test lift2
    let add = |a: &i32, b: &i32| a + b;
    let sum = Id::<i32>::lift2(add, &x, &y);
    assert_eq!(sum.unwrap(), 5);

    // Test lift3
    let multiply = |a: &i32, b: &i32, c: &i32| a * b * c;
    let product = Id::<i32>::lift3(multiply, &x, &y, &z);
    assert_eq!(product.unwrap(), 24);
}

#[test]
fn test_id_owned_applicative() {
    // Test optimized applicative operations
    let x: Id<i32> = Id::new(2);
    let y: Id<i32> = Id::new(3);
    let z: Id<i32> = Id::new(4);

    // Test apply_owned
    let add_one: Id<fn(i32) -> i32> = Id::new(|x| x + 1);
    let result = add_one.apply_owned(x);
    assert_eq!(result.unwrap(), 3);

    // Test lift2_owned
    let add = |a: i32, b: i32| a + b;
    let sum = Id::<i32>::lift2_owned(add, x, y);
    assert_eq!(sum.unwrap(), 5);

    // Test lift3_owned
    let multiply = |a: i32, b: i32, c: i32| a * b * c;
    let product = Id::<i32>::lift3_owned(multiply, x, y, z);
    assert_eq!(product.unwrap(), 24);
}

#[test]
fn test_id_monad() {
    // Test monad properties of Id
    let x = Id::new(42);

    // Test bind
    let f = |n: &i32| Id::new(n * 2);
    let g = |n: &i32| Id::new(n + 3);

    let bind_result = x.bind(&f);
    assert_eq!(bind_result.unwrap(), 84);

    // Test join
    let nested = Id::new(x);
    let flattened: Id<i32> = nested.join();
    assert_eq!(flattened.unwrap(), 42);

    // Test monad laws
    // 1. Left identity: pure(a).bind(f) == f(a)
    let left_identity = Id::<i32>::pure(&42).bind(&f);
    assert_eq!(left_identity.unwrap(), f(&42).unwrap());

    // 2. Right identity: m.bind(pure) == m
    let right_identity = x.bind(Id::<i32>::pure);
    assert_eq!(right_identity.unwrap(), x.unwrap());

    // 3. Associativity: m.bind(f).bind(g) == m.bind(|x| f(x).bind(g))
    let assoc_left = x.bind(f).bind(g);
    let assoc_right = x.bind(|n| f(n).bind(&g));
    assert_eq!(assoc_left.unwrap(), assoc_right.unwrap());
}

#[test]
fn test_id_owned_monad() {
    // Test optimized monad operations
    let x: Id<i32> = Id::new(42);

    // Test bind_owned
    let f = |n: i32| Id::new(n * 2);
    let result = x.bind_owned(f);
    assert_eq!(result.unwrap(), 84);

    // Test join_owned
    let nested: Id<Id<i32>> = Id::new(x);
    let flattened: Id<i32> = nested.join_owned();
    assert_eq!(flattened.unwrap(), 42);
}

#[test]
fn test_id_chaining() {
    // Test chaining of Id
    let x = Id::new(42);
    let result = x.fmap(|n| n + 1).fmap(|n| n * 2).fmap(|n| n.to_string());

    assert_eq!(result.unwrap(), "86");
}

#[test]
fn test_id_optimized_chains() {
    // Fully owned transformation chain
    let result = Id::new(10)
        .fmap(|n| n + 5)
        .fmap(|n| n * 2)
        .fmap(|n| n.to_string());
    assert_eq!(result.unwrap(), "30");

    // Complex chain with bind_owned and fmap_owned
    let result = Id::new(10)
        .fmap_owned(|n| n + 5)
        .bind_owned(|n| Id::new(n * 2))
        .fmap_owned(|n| n.to_string());
    assert_eq!(result.unwrap(), "30");
}

#[test]
fn test_id_clone() {
    // Test cloning of Id
    let x = Id::new(42);
    let y = x;
    assert_eq!(x.unwrap(), y.unwrap());
}

#[cfg(feature = "serde")]
#[test]
fn test_id_serde() {
    use rustica::datatypes::id::Id;
    use serde_json;

    // Test with a simple Id
    let id = Id::new(42);
    let serialized = serde_json::to_string(&id).unwrap();
    let deserialized: Id<i32> = serde_json::from_str(&serialized).unwrap();
    assert_eq!(id, deserialized);

    // Test with a string
    let id_str = Id::new("hello".to_string());
    let serialized_str = serde_json::to_string(&id_str).unwrap();
    let deserialized_str: Id<String> = serde_json::from_str(&serialized_str).unwrap();
    assert_eq!(id_str, deserialized_str);

    // Test with a struct
    #[derive(serde::Serialize, serde::Deserialize, PartialEq, Debug, Clone)]
    struct Point {
        x: i32,
        y: i32,
    }
    let point = Point { x: 1, y: 2 };
    let id_point = Id::new(point.clone());
    let serialized_point = serde_json::to_string(&id_point).unwrap();
    let deserialized_point: Id<Point> = serde_json::from_str(&serialized_point).unwrap();
    assert_eq!(id_point, deserialized_point);
}
