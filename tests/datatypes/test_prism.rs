use std::cell::Cell;
use std::rc::Rc;

use quickcheck_macros::quickcheck;
use rustica::datatypes::prism::Prism;

#[derive(Clone, Debug, PartialEq, Eq)]
enum TestStatus {
    Pending,
    Active(i32),
    Completed(String),
}

fn active_prism() -> Prism<
    TestStatus,
    i32,
    impl Fn(&TestStatus) -> Option<&i32> + Clone,
    impl Fn(i32) -> TestStatus + Clone,
> {
    Prism::new(
        |s: &TestStatus| match s {
            TestStatus::Active(n) => Some(n),
            _ => None,
        },
        TestStatus::Active,
    )
}

fn completed_prism() -> Prism<
    TestStatus,
    String,
    impl Fn(&TestStatus) -> Option<&String> + Clone,
    impl Fn(String) -> TestStatus + Clone,
> {
    Prism::new(
        |s: &TestStatus| match s {
            TestStatus::Completed(msg) => Some(msg),
            _ => None,
        },
        TestStatus::Completed,
    )
}

// Law 1: Review-Preview (Reviewing and then previewing yields the exact same focus)
// preview(review(a)) == Some(&a)
#[quickcheck]
fn test_prism_review_preview_law(a: i32) -> bool {
    let p = active_prism();
    let constructed = p.review(a);
    p.preview(&constructed) == Some(&a)
}

// Law 2: Preview-Review (If preview succeeds, reviewing yields the original structure)
// If preview(s) == Some(a) then review(*a) == s
#[test]
fn test_prism_preview_review_law() {
    let p = active_prism();
    let s = TestStatus::Active(42);
    if let Some(focus) = p.preview(&s) {
        assert_eq!(p.review(*focus), s);
    } else {
        panic!("preview should have succeeded");
    }

    let non_matching = TestStatus::Pending;
    assert_eq!(p.preview(&non_matching), None);
}

// Contract C-07: C-CONV accessors preview(&S) -> Option<&A> and to_value(&S) -> Option<A>
#[test]
fn test_prism_c_conv_accessors() {
    let completed = completed_prism();
    let status = TestStatus::Completed("Alice".to_string());
    let pending = TestStatus::Pending;

    // Direct reference borrowing (0 B)
    assert_eq!(completed.preview(&status), Some(&"Alice".to_string()));
    assert_eq!(completed.preview(&pending), None);

    // Owned value extraction via to_value()
    assert_eq!(completed.to_value(&status), Some("Alice".to_string()));
    assert_eq!(completed.to_value(&pending), None);

    // Standard .cloned() on Option<&A>
    assert_eq!(
        completed.preview(&status).cloned(),
        completed.to_value(&status)
    );
}

// Law 3: Modify Identity & Composition
#[test]
fn test_prism_modify() {
    let p = active_prism();

    // Matching variant is modified
    let s1 = TestStatus::Active(10);
    assert_eq!(p.modify(s1, |x| x * 2), TestStatus::Active(20));

    // Non-matching variant is untouched
    let s2 = TestStatus::Pending;
    assert_eq!(p.modify(s2.clone(), |x| x * 2), s2);

    let s3 = TestStatus::Completed("done".to_string());
    assert_eq!(p.modify(s3.clone(), |x| x * 2), s3);
}

// Composition of Prisms
#[test]
fn test_prism_composition() {
    #[derive(Clone, Debug, PartialEq, Eq)]
    enum Outer {
        Inner(TestStatus),
        Other,
    }

    let outer_prism = Prism::new(
        |o: &Outer| match o {
            Outer::Inner(status) => Some(status),
            _ => None,
        },
        Outer::Inner,
    );

    let deep_prism = outer_prism.then(active_prism());

    let val = Outer::Inner(TestStatus::Active(42));
    assert_eq!(deep_prism.preview(&val), Some(&42));
    assert_eq!(deep_prism.to_value(&val), Some(42));

    let updated = deep_prism.set(val, 100);
    assert_eq!(updated, Outer::Inner(TestStatus::Active(100)));

    let non_matching = Outer::Other;
    assert_eq!(deep_prism.preview(&non_matching), None);
    assert_eq!(deep_prism.set(non_matching.clone(), 100), non_matching);
}

// Slice 2: Contract C-08, C-09 & Law L-06 (Zero-alloc set and single-clone modify)
thread_local! {
    static CLONES: Cell<usize> = const { Cell::new(0) };
}

#[derive(PartialEq, Debug)]
struct Tracked(u32);

impl Clone for Tracked {
    fn clone(&self) -> Self {
        CLONES.with(|c| c.set(c.get() + 1));
        Tracked(self.0)
    }
}

#[derive(Clone, PartialEq, Debug)]
enum TrackedEnum {
    Active(Tracked),
    Inactive,
}

#[derive(Clone, PartialEq, Debug)]
enum RcEnum {
    Active(Rc<String>),
    Inactive,
}

#[test]
fn test_prism_set_preserves_sharing() {
    let prism = Prism::new(
        |s: &TrackedEnum| match s {
            TrackedEnum::Active(t) => Some(t),
            TrackedEnum::Inactive => None,
        },
        TrackedEnum::Active,
    );

    let active = TrackedEnum::Active(Tracked(42));
    let inactive = TrackedEnum::Inactive;

    // Contract C-08 & Law L-06: Zero-clone set on same value
    let a1 = active.clone();
    CLONES.with(|c| c.set(0));
    let same = prism.set(a1, Tracked(42));
    assert_eq!(
        CLONES.with(|c| c.get()),
        0,
        "set on unchanged value must perform 0 clones"
    );
    assert_eq!(same, TrackedEnum::Active(Tracked(42)));

    // Zero-clone set on variant miss
    let inact1 = inactive.clone();
    CLONES.with(|c| c.set(0));
    let miss = prism.set(inact1, Tracked(99));
    assert_eq!(
        CLONES.with(|c| c.get()),
        0,
        "set on non-matching variant must perform 0 clones"
    );
    assert_eq!(miss, TrackedEnum::Inactive);

    // Mutation on different value moves new value and does not clone source focus
    let a2 = active.clone();
    CLONES.with(|c| c.set(0));
    let updated = prism.set(a2, Tracked(7));
    assert_eq!(
        CLONES.with(|c| c.get()),
        0,
        "set on different value moves new value and does not clone source focus"
    );
    assert_eq!(updated, TrackedEnum::Active(Tracked(7)));

    // set_always unconditionally reconstructs via review
    let a3 = active.clone();
    CLONES.with(|c| c.set(0));
    let always = prism.set_always(a3, Tracked(42));
    assert_eq!(always, TrackedEnum::Active(Tracked(42)));

    // Contract C-09: Exactly 1 clone on modify identity (0 for comparison)
    let a4 = active.clone();
    CLONES.with(|c| c.set(0));
    let same_mod = prism.modify(a4, |x| x);
    assert_eq!(
        CLONES.with(|c| c.get()),
        1,
        "modify on unchanged value must perform exactly 1 clone for f(current)"
    );
    assert_eq!(same_mod, TrackedEnum::Active(Tracked(42)));

    // modify on non-matching variant: 0 clones
    let inact2 = inactive.clone();
    CLONES.with(|c| c.set(0));
    let miss_mod = prism.modify(inact2, |x| x);
    assert_eq!(
        CLONES.with(|c| c.get()),
        0,
        "modify on non-matching variant must perform 0 clones"
    );
    assert_eq!(miss_mod, TrackedEnum::Inactive);

    // modify_always unconditionally reconstructs via review
    let a5 = active;
    CLONES.with(|c| c.set(0));
    let always_mod = prism.modify_always(a5, |x| x);
    assert_eq!(
        CLONES.with(|c| c.get()),
        1,
        "modify_always performs exactly 1 clone for f(current)"
    );
    assert_eq!(always_mod, TrackedEnum::Active(Tracked(42)));

    // Pointer equality preservation
    let rc_prism = Prism::new(
        |s: &RcEnum| match s {
            RcEnum::Active(rc) => Some(rc),
            RcEnum::Inactive => None,
        },
        RcEnum::Active,
    );
    let original_rc = Rc::new("shared-data".to_string());
    let rc_instance = RcEnum::Active(Rc::clone(&original_rc));

    assert_eq!(rc_prism.preview(&RcEnum::Inactive), None);

    let same_rc = rc_prism.set(rc_instance.clone(), Rc::clone(&original_rc));
    match (&rc_instance, &same_rc) {
        (RcEnum::Active(a), RcEnum::Active(b)) => {
            assert!(
                Rc::ptr_eq(a, b),
                "set on same Rc value must preserve pointer equality"
            );
        },
        _ => panic!("expected Active variant"),
    }

    let same_rc_mod = rc_prism.modify(rc_instance.clone(), |r| r);
    match (&rc_instance, &same_rc_mod) {
        (RcEnum::Active(a), RcEnum::Active(b)) => {
            assert!(
                Rc::ptr_eq(a, b),
                "modify with identity must preserve pointer equality"
            );
        },
        _ => panic!("expected Active variant"),
    }
}

// Slice 3: 3-Level Composed Chaining (Contract C-10 & Law L-07)
#[derive(Clone, PartialEq, Debug)]
enum Level1 {
    Next(Level2),
    Stop,
}

#[derive(Clone, PartialEq, Debug)]
enum Level2 {
    Next(Level3),
    Stop,
}

#[derive(Clone, PartialEq, Debug)]
enum Level3 {
    Value(Tracked),
    Stop,
}

#[test]
fn test_prism_composed_view() {
    let p1 = Prism::new(
        |s: &Level1| match s {
            Level1::Next(l2) => Some(l2),
            Level1::Stop => None,
        },
        Level1::Next,
    );
    let p2 = Prism::new(
        |s: &Level2| match s {
            Level2::Next(l3) => Some(l3),
            Level2::Stop => None,
        },
        Level2::Next,
    );
    let p3 = Prism::new(
        |s: &Level3| match s {
            Level3::Value(t) => Some(t),
            Level3::Stop => None,
        },
        Level3::Value,
    );

    let target = Level1::Next(Level2::Next(Level3::Value(Tracked(100))));
    let p12 = p1.clone().then(p2.clone());
    let deep = p12.then(p3.clone());

    // 3-level view chaining extracts leaf without cloning
    CLONES.with(|c| c.set(0));
    assert_eq!(deep.preview(&target), Some(&Tracked(100)));
    assert_eq!(
        CLONES.with(|c| c.get()),
        0,
        "preview across 3 levels must perform 0 clones"
    );
    assert_eq!(deep.to_value(&target), Some(Tracked(100)));
    assert_eq!(deep.preview(&Level1::Stop), None);
    assert_eq!(p2.preview(&Level2::Stop), None);
    assert_eq!(p3.preview(&Level3::Stop), None);

    // Unchanged set performs 0 clones
    let t1 = target.clone();
    CLONES.with(|c| c.set(0));
    let same = deep.set(t1, Tracked(100));
    assert_eq!(
        CLONES.with(|c| c.get()),
        0,
        "set with unchanged value across 3 levels must perform 0 clones"
    );
    assert_eq!(same, target);

    // Mutated set reconstructs target
    let t2 = target.clone();
    CLONES.with(|c| c.set(0));
    let mutated = deep.set(t2, Tracked(999));
    assert_eq!(
        mutated,
        Level1::Next(Level2::Next(Level3::Value(Tracked(999))))
    );
}

#[derive(Clone, Debug, PartialEq)]
struct Pair<'a> {
    x: &'a str,
}

#[derive(Clone, Debug, PartialEq)]
enum BorrowedEnum<'a> {
    Case(Pair<'a>),
    Empty,
}

#[test]
fn test_borrowed_focus_prism() {
    let p_borrowed = Prism::new(
        |s: &BorrowedEnum<'_>| match s {
            BorrowedEnum::Case(p) => Some(p),
            BorrowedEnum::Empty => None,
        },
        BorrowedEnum::Case,
    );

    let item = BorrowedEnum::Case(Pair { x: "hello" });
    assert_eq!(p_borrowed.preview(&item), Some(&Pair { x: "hello" }));
    assert_eq!(p_borrowed.preview(&BorrowedEnum::Empty), None);
    assert_eq!(p_borrowed.to_value(&item), Some(Pair { x: "hello" }));
}

#[test]
fn test_prism_float_equality_semantics() {
    #[derive(Clone, Debug, PartialEq)]
    enum Number {
        Float(f64),
    }
    let prism = Prism::new(
        |n: &Number| match n {
            Number::Float(f) => Some(f),
        },
        Number::Float,
    );

    let s = Number::Float(-0.0);
    // -0.0 == 0.0 under PartialEq, so set() short-circuits and preserves original -0.0
    let short_circuited = prism.set(s.clone(), 0.0);
    match short_circuited {
        Number::Float(f) => assert_eq!(f.to_bits(), (-0.0f64).to_bits()),
    }

    // set_always() bypasses PartialEq and assigns bit-exact 0.0
    let bit_exact = prism.set_always(s.clone(), 0.0);
    match bit_exact {
        Number::Float(f) => assert_eq!(f.to_bits(), (0.0f64).to_bits()),
    }

    // modify() on float behaves symmetrically
    let mod_short = prism.modify(s.clone(), |_| 0.0);
    match mod_short {
        Number::Float(f) => assert_eq!(f.to_bits(), (-0.0f64).to_bits()),
    }

    let mod_always = prism.modify_always(s, |_| 0.0);
    match mod_always {
        Number::Float(f) => assert_eq!(f.to_bits(), (0.0f64).to_bits()),
    }
}

#[derive(Clone, Debug, PartialEq)]
enum TaggedItem {
    Entry { id: u32, tag: String },
    None,
}

#[test]
fn test_prism_modify_with_and_set_with_preserve_non_focus_data() {
    let prism = Prism::new(
        |item: &TaggedItem| match item {
            TaggedItem::Entry { id, .. } => Some(id),
            TaggedItem::None => None,
        },
        |id| TaggedItem::Entry {
            id,
            tag: String::new(),
        },
    );

    let item = TaggedItem::Entry {
        id: 10,
        tag: "preserved".into(),
    };

    let modify_fn = |item, new_id| match item {
        TaggedItem::Entry { tag, .. } => TaggedItem::Entry { id: new_id, tag },
        TaggedItem::None => TaggedItem::None,
    };

    // modify_with preserves non-focus field "tag"
    let modified = prism.modify_with(item.clone(), modify_fn, |id| id + 5);
    assert_eq!(
        modified,
        TaggedItem::Entry {
            id: 15,
            tag: "preserved".into()
        }
    );

    // set_with preserves non-focus field "tag"
    let updated = prism.set_with(item, modify_fn, 99);
    assert_eq!(
        updated,
        TaggedItem::Entry {
            id: 99,
            tag: "preserved".into()
        }
    );
}

#[test]
fn test_prism_modify_with_and_set_with_return_source_when_focus_absent() {
    let prism = Prism::new(
        |item: &TaggedItem| match item {
            TaggedItem::Entry { id, .. } => Some(id),
            TaggedItem::None => None,
        },
        |id| TaggedItem::Entry {
            id,
            tag: String::new(),
        },
    );

    let absent = TaggedItem::None;
    let modify_fn = |item, new_id| match item {
        TaggedItem::Entry { tag, .. } => TaggedItem::Entry { id: new_id, tag },
        TaggedItem::None => TaggedItem::None,
    };

    let modified = prism.modify_with(absent.clone(), modify_fn, |id| id + 1);
    assert_eq!(modified, TaggedItem::None);

    let updated = prism.set_with(absent, modify_fn, 100);
    assert_eq!(updated, TaggedItem::None);
}

#[test]
fn test_prism_is_send_and_sync() {
    fn assert_send<T: Send>() {}
    fn assert_sync<T: Sync>() {}

    type SimplePrism =
        Prism<TestStatus, i32, fn(&TestStatus) -> Option<&i32>, fn(i32) -> TestStatus>;

    assert_send::<SimplePrism>();
    assert_sync::<SimplePrism>();

    let prism = active_prism();
    let handle = std::thread::spawn(move || {
        let s = TestStatus::Active(42);
        prism.preview(&s).copied()
    });
    assert_eq!(handle.join().unwrap(), Some(42));
}
