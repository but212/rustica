use quickcheck_macros::quickcheck;
use rustica::traits::monoid::Monoid;
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
    use rustica::traits::monoid::repeat;

    assert_eq!(repeat("x".to_string(), 3), "xxx");
}

#[test]
fn test_validated_semigroup_accumulation() {
    use rustica::datatypes::validated::core::Validated;
    use rustica::traits::semigroup::Semigroup;

    #[derive(Debug, PartialEq, Eq, Clone, Copy)]
    struct TestSum(i32);

    impl Semigroup for TestSum {
        fn combine(self, other: Self) -> Self {
            TestSum(self.0 + other.0)
        }
    }

    // 1. Semigroup accumulates both valid payloads when both are Valid
    let v1: Validated<TestSum, String> = Validated::valid(TestSum(10));
    let v2: Validated<TestSum, String> = Validated::valid(TestSum(20));
    assert_eq!(v1.combine(v2), Validated::valid(TestSum(30)));

    // 2. Semigroup yields Invalid when one is Invalid (errors take precedence)
    let v1: Validated<TestSum, String> = Validated::valid(TestSum(10));
    let inv: Validated<TestSum, String> = Validated::invalid("err1".to_string());
    assert!(v1.clone().combine(inv.clone()).is_invalid());
    assert!(inv.combine(v1).is_invalid());
}

#[test]
#[allow(deprecated)]
fn test_result_and_vec_with_non_clone_types() {
    use rustica::traits::applicative::Applicative;
    use rustica::traits::foldable::Foldable;
    use rustica::traits::functor::Functor;
    use rustica::traits::monad::Monad;
    use rustica::traits::monoid::Monoid;
    use rustica::traits::pure::Pure;

    #[allow(dead_code)]
    struct NonCloneErr(String);
    #[allow(dead_code)]
    struct MoveOnly(i32);

    // 1. Pure for Result with non-clone error
    let r: Result<i32, NonCloneErr> = <Result<i32, NonCloneErr> as Pure>::pure(42);
    assert_eq!(r.ok(), Some(42));

    // 2. Functor for Result with non-clone error
    let r: Result<i32, NonCloneErr> = Ok(10);
    let mapped = r.fmap(|x| x * 2);
    assert_eq!(mapped.ok(), Some(20));

    // 3. Applicative for Result with non-clone error
    let fn_res: Result<fn(i32) -> i32, NonCloneErr> = Ok(|x| x + 5);
    let val_res: Result<i32, NonCloneErr> = Ok(10);
    let applied = fn_res.apply(val_res);
    assert_eq!(applied.ok(), Some(15));

    // 4. Monad for Result with non-clone error
    let r: Result<i32, NonCloneErr> = Ok(10);
    let bound = r.bind(|x| Ok(x + 1));
    assert_eq!(bound.ok(), Some(11));

    // 5. Foldable for Result with non-clone error
    let r: Result<i32, NonCloneErr> = Ok(10);
    assert_eq!(r.fold_left(0, |acc, x| acc + x), 10);

    // 6. Monoid for Vec with move-only type
    let empty_vec: Vec<MoveOnly> = Vec::<MoveOnly>::empty();
    assert!(empty_vec.is_empty());
}

#[test]
fn test_prelude_does_not_shadow_std_command_or_slice_join() {
    use rustica::prelude::*;
    use std::process::Command;
    let _cmd = Command::new("echo");
    let _v: Validated<i32, &str> = Validated::valid(1);

    // Verify std slice join works without method resolution conflict
    let words: Vec<String> = vec!["a".into(), "b".into()];
    assert_eq!(words.join(","), "a,b");
}

#[test]
fn test_prelude_exports_handler() {
    use rustica::datatypes::operational::Command as OpCommand;
    use rustica::prelude::*;

    struct MyCmd;
    impl OpCommand for MyCmd {
        type Output = i32;
    }

    struct MyHandler;
    impl Handler<MyCmd> for MyHandler {
        fn handle(&mut self, _cmd: MyCmd) -> i32 {
            42
        }
    }

    let mut h = MyHandler;
    assert_eq!(h.handle(MyCmd), 42);
}

#[test]
fn test_validated_from_iterator_and_zip() {
    use rustica::datatypes::validated::Validated;
    use std::collections::BTreeSet;

    #[derive(Debug, PartialEq, Eq)]
    struct MoveOnly(i32);

    // 1. FromIterator: all valid
    let valids: Vec<Validated<i32, &str>> = vec![
        Validated::valid(1),
        Validated::valid(2),
        Validated::valid(3),
    ];
    let collected: Validated<Vec<i32>, &str> = valids.into_iter().collect();
    assert_eq!(collected, Validated::valid(vec![1, 2, 3]));

    // 2. FromIterator: BTreeSet
    let valids: Vec<Validated<i32, &str>> = vec![
        Validated::valid(1),
        Validated::valid(2),
        Validated::valid(2),
    ];
    let collected_set: Validated<BTreeSet<i32>, &str> = valids.into_iter().collect();
    let expected_set: BTreeSet<i32> = [1, 2].into_iter().collect();
    assert_eq!(collected_set, Validated::valid(expected_set));

    // 3. FromIterator: multiple errors accumulated
    let mixed: Vec<Validated<i32, &str>> = vec![
        Validated::valid(1),
        Validated::invalid("err1"),
        Validated::valid(2),
        Validated::invalid("err2"),
    ];
    let collected_err: Validated<Vec<i32>, &str> = mixed.into_iter().collect();
    assert!(collected_err.is_invalid());
    assert_eq!(collected_err.error_slice(), &["err1", "err2"]);

    // 4. Inherent zip and zip_with on move-only types
    let m1 = Validated::<MoveOnly, &str>::valid(MoveOnly(10));
    let m2 = Validated::<MoveOnly, &str>::valid(MoveOnly(20));
    let zipped = m1.zip_with(m2, |a, b| MoveOnly(a.0 + b.0));
    assert_eq!(zipped, Validated::valid(MoveOnly(30)));

    // 5. Inherent lift2 on move-only types
    let m1 = Validated::<MoveOnly, &str>::valid(MoveOnly(5));
    let m2 = Validated::<MoveOnly, &str>::valid(MoveOnly(15));
    let lifted = Validated::lift2(|a: MoveOnly, b: MoveOnly| MoveOnly(a.0 + b.0), m1, m2);
    assert_eq!(lifted, Validated::valid(MoveOnly(20)));

    // 6. Inherent zip3 and zip_with3 on move-only types
    let m1 = Validated::<MoveOnly, &str>::valid(MoveOnly(1));
    let m2 = Validated::<MoveOnly, &str>::valid(MoveOnly(2));
    let m3 = Validated::<MoveOnly, &str>::valid(MoveOnly(3));
    let zipped3 = m1.zip_with3(m2, m3, |a, b, c| MoveOnly(a.0 + b.0 + c.0));
    assert_eq!(zipped3, Validated::valid(MoveOnly(6)));
}
