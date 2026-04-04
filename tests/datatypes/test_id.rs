use rustica::datatypes::id::Id;
use rustica::traits::{applicative::Applicative, functor::Functor, monad::Monad, pure::Pure};

#[test]
fn test_id_monadic_laws() {
    let x = Id::new(42);
    let f = |n: &i32| Id::new(n * 2);
    let g = |n: &i32| Id::new(n + 3);

    // 1. Functor Laws: Identity and Composition
    assert_eq!(x.clone().fmap(|n| *n).unwrap(), x.unwrap());
    assert_eq!(
        x.clone().fmap(|n| n + 3).fmap(|n| n * 2).unwrap(),
        x.clone().fmap(|n| (n + 3) * 2).unwrap()
    );

    // 2. Applicative: apply and lift2
    let app_f = Id::new(|n: &i32| n + 1);
    assert_eq!(app_f.apply(&x).unwrap(), 43);
    assert_eq!(Id::<i32>::lift2(|a, b| a + b, &x, &Id::new(8)).unwrap(), 50);

    // 3. Monad Laws: Left Identity, Right Identity, Associativity
    // Left Identity: pure(a).bind(f) == f(a)
    assert_eq!(Id::<i32>::pure(&42).bind(&f).unwrap(), f(&42).unwrap());
    // Right Identity: m.bind(pure) == m
    assert_eq!(x.clone().bind(Id::<i32>::pure).unwrap(), x.unwrap());
    // Associativity: m.bind(f).bind(g) == m.bind(|x| f(x).bind(g))
    assert_eq!(
        x.clone().bind(f).bind(g).unwrap(),
        x.clone().bind(|n| f(n).bind(&g)).unwrap()
    );

    // 4. Flattening (Join)
    assert_eq!(Id::new(Id::new(100)).join::<i32>().unwrap(), 100);
}

#[test]
fn test_id_pipelines() {
    // Verifying that owned and ref-based transformations interoperate within a chain
    let result = Id::new(10)
        .fmap_owned(|n| n + 5) // 15 (owned)
        .fmap(|n| n * 2) // 30 (ref)
        .bind_owned(|n| Id::new(n.to_string())) // "30" (owned)
        .unwrap();

    assert_eq!(result, "30");
}

#[test]
fn test_id_utilities() {
    let id = Id::new(42);

    // Accessors
    assert_eq!(id.as_ref(), &42);
    assert_eq!(id.clone().into_inner(), 42);

    // Serde Integration
    #[cfg(feature = "serde")]
    {
        use serde_json;
        let serialized = serde_json::to_string(&id).unwrap();
        let deserialized: Id<i32> = serde_json::from_str(&serialized).unwrap();
        assert_eq!(id, deserialized);
    }
}
