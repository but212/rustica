use rustica::datatypes::choice::Choice;
use rustica::prelude::*;
use rustica::traits::{
    alternative::Alternative, applicative::Applicative, foldable::Foldable, functor::Functor,
    monad::Monad,
};

#[test]
fn test_core_monadic_ops() {
    // 1. Creation and Functor
    let choice = Choice::new(1, vec![2, 3]);
    let doubled = choice.fmap(|x| x * 2);
    assert_eq!(*doubled.first().unwrap(), 2);
    assert_eq!(doubled.alternatives(), &[4, 6]);

    // 2. Applicative and LiftN
    let double_fn: fn(&i32) -> i32 = |x| x * 2;
    let triple_fn: fn(&i32) -> i32 = |x| x * 3;
    let f = Choice::new(double_fn, vec![triple_fn]);
    let applied = f.apply(&choice);
    assert_eq!(applied.len(), 6); // Combinations of (double, triple) x (1, 2, 3)

    let lift2 = Choice::<i32>::lift2(|x, y| x + y, &choice, &Choice::new(10, vec![]));
    assert_eq!(*lift2.first().unwrap(), 11);
    assert_eq!(lift2.alternatives(), &[12, 13]);

    // 3. Monad Bind
    let bound = choice.bind(|x| Choice::new(x * 10, vec![]));
    assert_eq!(*bound.first().unwrap(), 10);
    assert_eq!(bound.alternatives(), &[20, 30]);
}

#[test]
fn test_collection_behavior() {
    // 1. Semigroup & Monoid (Combine)
    let a = Choice::new(1, vec![2]);
    let b = Choice::new(3, vec![4]);
    let empty: Choice<i32> = Choice::new_empty();

    assert_eq!(*a.combine(&b).first().unwrap(), 1);
    assert_eq!(a.combine(&b).alternatives(), &[2, 3, 4]);
    assert_eq!(a.combine(&empty), a);
    assert_eq!(empty.combine(&a), a);

    // 2. Alt & Guard
    let guarded = Choice::<()>::guard(true);
    assert!(!guarded.is_empty());
    assert!(Choice::<()>::guard(false).is_empty());

    // 3. Add/Remove alternatives
    let modified = a.combine(&Choice::of_many(vec![5]));
    assert_eq!(modified.alternatives(), &[2, 5]);

    let removed = modified.remove_alternative(0); // Remove '2'
    assert_eq!(removed.alternatives(), &[5]);
}

#[test]
fn test_iteration_and_aggregation() {
    let choice = Choice::new(1, vec![2, 3]);

    // Iterator & Conversion
    let collected: Vec<_> = choice.iter().cloned().collect();
    assert_eq!(collected, vec![1, 2, 3]);
    let into_vec: Vec<i32> = choice.clone().into();
    assert_eq!(into_vec, vec![1, 2, 3]);

    // Folding
    assert_eq!(choice.fold_left(&0, |acc, x| acc + x), 6);
    assert_eq!(choice.fold_right(&1, |x, acc| x * acc), 6);

    // Search
    assert_eq!(choice.iter().find(|&&x| x == 2), Some(&2));
}

#[test]
fn test_structure_transformation() {
    // 1. Filter and Promotion
    let choice = Choice::new(1, vec![2, 3, 4]);
    let evens = choice.filter_values(|x| x % 2 == 0);
    assert_eq!(*evens.first().unwrap(), 2); // '2' was promoted since '1' was filtered
    assert_eq!(evens.alternatives(), &[4]);

    // 2. Flatten and join
    let nested = Choice::new(vec![1], vec![vec![2, 3]]);
    let flat = nested.flatten();
    assert_eq!(*flat.first().unwrap(), 1);
    assert_eq!(flat.alternatives(), &[2, 3]);

    let monad_nested = Choice::new(Choice::new(1, vec![2]), vec![Choice::new(3, vec![4])]);
    let joined = monad_nested.join();
    assert_eq!(*joined.first().unwrap(), 1);
    assert_eq!(joined.alternatives(), &[2, 3, 4]);
}

#[test]
fn test_monad_laws() {
    let m = Choice::new(1, vec![2]);
    let f = |x: &i32| Choice::new(x + 1, vec![]);
    let g = |x: &i32| Choice::new(x * 2, vec![]);

    // Left Identity: pure(a).bind(f) == f(a)
    assert_eq!(Choice::<i32>::pure(&10).bind(f), f(&10));

    // Right Identity: m.bind(pure) == m
    assert_eq!(m.bind(Choice::<i32>::pure), m);

    // Associativity: (m.bind(f)).bind(g) == m.bind(|x| f(x).bind(g))
    assert_eq!(m.bind(f).bind(g), m.bind(|x| f(x).bind(g)));
}

#[test]
fn test_utilities_and_resilience() {
    // Display & Eq
    let c = Choice::new(1, vec![2]);
    assert_eq!(c, c.clone());
    assert!(format!("{c}").contains("1"));

    // Sequence
    let opt_choice = Choice::new(Some(1), vec![Some(2)]);
    assert_eq!(opt_choice.clone().sequence(), Some(Choice::new(1, vec![2])));
    assert!(Choice::new(Some(1), vec![None]).sequence().is_none());

    // Serde
    #[cfg(feature = "serde")]
    {
        use serde_json;
        let serialized = serde_json::to_string(&c).unwrap();
        let deserialized: Choice<i32> = serde_json::from_str(&serialized).unwrap();
        assert_eq!(c, deserialized);
    }
}
