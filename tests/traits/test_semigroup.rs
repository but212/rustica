extern crate quickcheck;
use super::TestFunctor;
use quickcheck_macros::quickcheck;
use rustica::traits::semigroup::{Semigroup, SemigroupExt, combine_all_values, combine_values};
use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};

#[quickcheck]
fn semigroup_associativity(
    x: TestFunctor<String>, y: TestFunctor<String>, z: TestFunctor<String>,
) -> bool {
    x.combine(&y).combine(&z) == x.combine(&y.combine(&z))
}

mod string_semigroup {
    use super::*;

    #[test]
    fn test_combine() {
        let hello = "Hello, ".to_string();
        let world = "world!".to_string();
        assert_eq!(hello.combine(&world), "Hello, world!");
    }

    #[test]
    fn test_combine_owned() {
        let hello = "Hello, ".to_string();
        let world = "world!".to_string();
        assert_eq!(hello.combine_owned(world), "Hello, world!");
    }

    #[test]
    fn test_associativity() {
        let a = "a".to_string();
        let b = "b".to_string();
        let c = "c".to_string();
        assert_eq!(a.combine(&b).combine(&c), a.combine(&b.combine(&c)));
    }
}

mod vec_semigroup {
    use super::*;

    #[test]
    fn test_combine() {
        let a = vec![1, 2, 3];
        let b = vec![4, 5, 6];
        assert_eq!(a.combine(&b), vec![1, 2, 3, 4, 5, 6]);
    }

    #[test]
    fn test_combine_owned() {
        let a = vec![1, 2, 3];
        let b = vec![4, 5, 6];
        assert_eq!(a.combine_owned(b), vec![1, 2, 3, 4, 5, 6]);
    }

    #[test]
    fn test_associativity() {
        let a = vec![1];
        let b = vec![2];
        let c = vec![3];
        assert_eq!(a.combine(&b).combine(&c), a.combine(&b.combine(&c)));
    }
}

mod hashmap_semigroup {
    use super::*;

    #[test]
    fn test_combine_disjoint() {
        let mut a: HashMap<&str, String> = HashMap::new();
        a.insert("key1", "value1".to_string());

        let mut b: HashMap<&str, String> = HashMap::new();
        b.insert("key2", "value2".to_string());

        let combined = a.combine(&b);
        assert_eq!(combined.get("key1"), Some(&"value1".to_string()));
        assert_eq!(combined.get("key2"), Some(&"value2".to_string()));
    }

    #[test]
    fn test_combine_overlapping() {
        let mut a: HashMap<&str, String> = HashMap::new();
        a.insert("key", "hello".to_string());

        let mut b: HashMap<&str, String> = HashMap::new();
        b.insert("key", " world".to_string());

        let combined = a.combine(&b);
        assert_eq!(combined.get("key"), Some(&"hello world".to_string()));
    }

    #[test]
    fn test_combine_owned_overlapping() {
        let mut a: HashMap<&str, String> = HashMap::new();
        a.insert("key", "hello".to_string());

        let mut b: HashMap<&str, String> = HashMap::new();
        b.insert("key", " world".to_string());

        let combined = a.combine_owned(b);
        assert_eq!(combined.get("key"), Some(&"hello world".to_string()));
    }
}

mod hashset_semigroup {
    use super::*;

    #[test]
    fn test_combine() {
        let mut a: HashSet<i32> = HashSet::new();
        a.insert(1);
        a.insert(2);

        let mut b: HashSet<i32> = HashSet::new();
        b.insert(2);
        b.insert(3);

        let combined = a.combine(&b);
        assert!(combined.contains(&1));
        assert!(combined.contains(&2));
        assert!(combined.contains(&3));
    }

    #[test]
    fn test_combine_owned() {
        let mut a: HashSet<i32> = HashSet::new();
        a.insert(1);

        let mut b: HashSet<i32> = HashSet::new();
        b.insert(2);

        let combined = a.combine_owned(b);
        assert!(combined.contains(&1));
        assert!(combined.contains(&2));
    }
}

mod btreemap_semigroup {
    use super::*;

    #[test]
    fn test_combine_overlapping() {
        let mut a: BTreeMap<&str, String> = BTreeMap::new();
        a.insert("key", "hello".to_string());

        let mut b: BTreeMap<&str, String> = BTreeMap::new();
        b.insert("key", " world".to_string());

        let combined = a.combine(&b);
        assert_eq!(combined.get("key"), Some(&"hello world".to_string()));
    }

    #[test]
    fn test_combine_owned_overlapping() {
        let mut a: BTreeMap<&str, String> = BTreeMap::new();
        a.insert("key", "hello".to_string());

        let mut b: BTreeMap<&str, String> = BTreeMap::new();
        b.insert("key", " world".to_string());

        let combined = a.combine_owned(b);
        assert_eq!(combined.get("key"), Some(&"hello world".to_string()));
    }
}

mod btreeset_semigroup {
    use super::*;

    #[test]
    fn test_combine() {
        let mut a: BTreeSet<i32> = BTreeSet::new();
        a.insert(1);
        a.insert(2);

        let mut b: BTreeSet<i32> = BTreeSet::new();
        b.insert(2);
        b.insert(3);

        let combined = a.combine(&b);
        assert!(combined.contains(&1));
        assert!(combined.contains(&2));
        assert!(combined.contains(&3));
    }

    #[test]
    fn test_combine_owned() {
        let mut a: BTreeSet<i32> = BTreeSet::new();
        a.insert(1);

        let mut b: BTreeSet<i32> = BTreeSet::new();
        b.insert(2);

        let combined = a.combine_owned(b);
        assert!(combined.contains(&1));
        assert!(combined.contains(&2));
    }
}

mod tuple_semigroup {
    use super::*;

    #[test]
    fn test_tuple2_combine() {
        let a = ("hello".to_string(), vec![1]);
        let b = (" world".to_string(), vec![2]);
        let combined = a.combine(&b);
        assert_eq!(combined.0, "hello world");
        assert_eq!(combined.1, vec![1, 2]);
    }

    #[test]
    fn test_tuple2_combine_owned() {
        let a = ("hello".to_string(), vec![1]);
        let b = (" world".to_string(), vec![2]);
        let combined = a.combine_owned(b);
        assert_eq!(combined.0, "hello world");
        assert_eq!(combined.1, vec![1, 2]);
    }

    #[test]
    fn test_tuple3_combine() {
        let a = ("a".to_string(), vec![1], "x".to_string());
        let b = ("b".to_string(), vec![2], "y".to_string());
        let combined = a.combine(&b);
        assert_eq!(combined.0, "ab");
        assert_eq!(combined.1, vec![1, 2]);
        assert_eq!(combined.2, "xy");
    }

    #[test]
    fn test_tuple3_combine_owned() {
        let a = ("a".to_string(), vec![1], "x".to_string());
        let b = ("b".to_string(), vec![2], "y".to_string());
        let combined = a.combine_owned(b);
        assert_eq!(combined.0, "ab");
        assert_eq!(combined.1, vec![1, 2]);
        assert_eq!(combined.2, "xy");
    }

    #[test]
    fn test_tuple4_combine() {
        let a = ("a".to_string(), vec![1], "x".to_string(), vec![10]);
        let b = ("b".to_string(), vec![2], "y".to_string(), vec![20]);
        let combined = a.combine(&b);
        assert_eq!(combined.0, "ab");
        assert_eq!(combined.1, vec![1, 2]);
        assert_eq!(combined.2, "xy");
        assert_eq!(combined.3, vec![10, 20]);
    }

    #[test]
    fn test_tuple4_combine_owned() {
        let a = ("a".to_string(), vec![1], "x".to_string(), vec![10]);
        let b = ("b".to_string(), vec![2], "y".to_string(), vec![20]);
        let combined = a.combine_owned(b);
        assert_eq!(combined.0, "ab");
        assert_eq!(combined.1, vec![1, 2]);
        assert_eq!(combined.2, "xy");
        assert_eq!(combined.3, vec![10, 20]);
    }
}

mod option_semigroup {
    use super::*;

    #[test]
    fn test_combine_some_some() {
        let a: Option<String> = Some("hello".to_string());
        let b: Option<String> = Some(" world".to_string());
        assert_eq!(a.combine(&b), Some("hello world".to_string()));
    }

    #[test]
    fn test_combine_some_none() {
        let a: Option<String> = Some("hello".to_string());
        let b: Option<String> = None;
        assert_eq!(a.combine(&b), Some("hello".to_string()));
    }

    #[test]
    fn test_combine_none_some() {
        let a: Option<String> = None;
        let b: Option<String> = Some("world".to_string());
        assert_eq!(a.combine(&b), Some("world".to_string()));
    }

    #[test]
    fn test_combine_none_none() {
        let a: Option<String> = None;
        let b: Option<String> = None;
        assert_eq!(a.combine(&b), None);
    }

    #[test]
    fn test_combine_owned_some_some() {
        let a: Option<String> = Some("hello".to_string());
        let b: Option<String> = Some(" world".to_string());
        assert_eq!(a.combine_owned(b), Some("hello world".to_string()));
    }

    #[test]
    fn test_combine_owned_some_none() {
        let a: Option<String> = Some("hello".to_string());
        let b: Option<String> = None;
        assert_eq!(a.combine_owned(b), Some("hello".to_string()));
    }

    #[test]
    fn test_combine_owned_none_some() {
        let a: Option<String> = None;
        let b: Option<String> = Some("world".to_string());
        assert_eq!(a.combine_owned(b), Some("world".to_string()));
    }

    #[test]
    fn test_combine_owned_none_none() {
        let a: Option<String> = None;
        let b: Option<String> = None;
        assert_eq!(a.combine_owned(b), None);
    }
}

mod semigroup_ext {
    use super::*;

    #[test]
    fn test_combine_all() {
        let initial = "start".to_string();
        let values = vec!["-a".to_string(), "-b".to_string(), "-c".to_string()];
        let result = initial.combine_all(values);
        assert_eq!(result, "start-a-b-c");
    }

    #[test]
    fn test_combine_all_owned() {
        let values = vec!["a".to_string(), "b".to_string(), "c".to_string()];
        let result: String = SemigroupExt::combine_all_owned(values);
        assert_eq!(result, "abc");
    }

    #[test]
    fn test_combine_n_zero() {
        let s = "x".to_string();
        assert_eq!(s.combine_n(&0), "x");
    }

    #[test]
    fn test_combine_n() {
        let s = "x".to_string();
        assert_eq!(s.combine_n(&3), "xxx");
    }

    #[test]
    fn test_combine_n_owned_zero() {
        let s = "x".to_string();
        assert_eq!(s.combine_n_owned(0), "x");
    }

    #[test]
    fn test_combine_n_owned() {
        let s = "x".to_string();
        assert_eq!(s.combine_n_owned(2), "xx");
    }
}

mod utility_functions {
    use super::*;

    #[test]
    fn test_combine_all_values_non_empty() {
        let values = vec!["a".to_string(), "b".to_string(), "c".to_string()];
        let result = combine_all_values(values);
        assert_eq!(result, Some("abc".to_string()));
    }

    #[test]
    fn test_combine_all_values_empty() {
        let values: Vec<String> = vec![];
        let result = combine_all_values(values);
        assert_eq!(result, None);
    }

    #[test]
    fn test_combine_values() {
        let initial = "start".to_string();
        let values = vec!["-a".to_string(), "-b".to_string()];
        let result = combine_values(initial, values);
        assert_eq!(result, "start-a-b");
    }

    #[test]
    fn test_combine_values_empty() {
        let initial = "start".to_string();
        let values: Vec<String> = vec![];
        let result = combine_values(initial, values);
        assert_eq!(result, "start");
    }
}
