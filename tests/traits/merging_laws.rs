use quickcheck_macros::quickcheck;
use rustica::traits::monoid::{Monoid, MonoidExt};
use rustica::traits::semigroup::Semigroup;
use std::collections::{HashMap, HashSet};

// --- Basic Scalar Laws (String) ---

#[quickcheck]
fn string_monoid_laws(a: String, b: String, c: String) -> bool {
    let identity =
        String::empty().combine(a.clone()) == a && a.clone().combine(String::empty()) == a;
    let associativity = a.clone().combine(b.clone()).combine(c.clone()) == a.combine(b.combine(c));
    identity && associativity
}

// --- Collection Laws (Vec, HashMap, HashSet) ---

#[quickcheck]
fn vec_monoid_laws(a: Vec<i32>, b: Vec<i32>, c: Vec<i32>) -> bool {
    let identity =
        Vec::<i32>::empty().combine(a.clone()) == a && a.clone().combine(Vec::<i32>::empty()) == a;
    let assoc = a.clone().combine(b.clone()).combine(c.clone()) == a.combine(b.combine(c));
    identity && assoc
}

#[test]
fn test_map_set_merging() {
    // 1. HashMap: Overlapping keys should combine values
    let mut a = HashMap::new();
    a.insert("k", "v1".to_string());
    let mut b = HashMap::new();
    b.insert("k", "v2".to_string());
    assert_eq!(a.combine(b).get("k").unwrap(), "v1v2");

    // 2. HashSet: Semigroup combination is Union
    let mut s1 = HashSet::new();
    s1.insert(1);
    let mut s2 = HashSet::new();
    s2.insert(2);
    let combined = s1.combine(s2);
    assert!(combined.contains(&1) && combined.contains(&2));
}

// --- Tuple and Option Combination ---

#[test]
fn test_complex_combination_laws() {
    // 1. Tuples: Should combine element-wise
    let t1 = ("a".to_string(), vec![1]);
    let t2 = ("b".to_string(), vec![2]);
    assert_eq!(t1.combine(t2), ("ab".to_string(), vec![1, 2]));

    // 2. Options: Some(a).combine(Some(b)) == Some(a.combine(b))
    let o1 = Some("hello".to_string());
    let o2 = Some(" world".to_string());
    assert_eq!(o1.clone().combine(o2), Some("hello world".to_string()));
    assert_eq!(o1.combine(None), Some("hello".to_string()));
}

// --- Monoid Extensions (Repeat, Power, mconcat) ---

#[test]
fn test_monoid_utilities() {
    use rustica::traits::monoid::{mconcat, repeat};

    let values = vec!["a".to_string(), "b".to_string(), "c".to_string()];
    assert_eq!(mconcat(&values), "abc");
    assert_eq!(repeat("x".to_string(), 3), "xxx");
    assert!(String::empty().is_empty_monoid());
}

#[test]
fn test_validated_semigroup_accumulation() {
    use rustica::datatypes::validated::core::Validated;
    use rustica::datatypes::wrapper::sum::Sum;

    // 1. Semigroup accumulates both valid payloads when both are Valid
    let v1: Validated<String, Sum<i32>> = Validated::valid(Sum(10));
    let v2: Validated<String, Sum<i32>> = Validated::valid(Sum(20));
    assert_eq!(v1.combine(v2), Validated::valid(Sum(30)));

    // 2. Semigroup yields Invalid when one is Invalid (errors take precedence)
    let v1: Validated<String, Sum<i32>> = Validated::valid(Sum(10));
    let inv: Validated<String, Sum<i32>> = Validated::invalid("err1".to_string());
    assert!(v1.clone().combine(inv.clone()).is_invalid());
    assert!(inv.combine(v1).is_invalid());
}
