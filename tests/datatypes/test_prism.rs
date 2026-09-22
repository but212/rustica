use quickcheck_macros::quickcheck;
use rustica::datatypes::prism::Prism;

#[derive(Clone, Debug, PartialEq, Eq)]
enum TestStatus {
    Pending,
    Active(i32),
    Completed(String),
}

fn active_prism()
-> Prism<TestStatus, i32, impl Fn(&TestStatus) -> Option<i32>, impl Fn(i32) -> TestStatus> {
    Prism::new(
        |s: &TestStatus| match s {
            TestStatus::Active(n) => Some(*n),
            _ => None,
        },
        TestStatus::Active,
    )
}

fn completed_prism()
-> Prism<TestStatus, String, impl Fn(&TestStatus) -> Option<String>, impl Fn(String) -> TestStatus>
{
    Prism::new(
        |s: &TestStatus| match s {
            TestStatus::Completed(msg) => Some(msg.clone()),
            _ => None,
        },
        TestStatus::Completed,
    )
}

// Law 1: Review-Preview (Reviewing and then previewing yields the exact same focus)
// preview(review(a)) == Some(a)
#[quickcheck]
fn test_prism_review_preview_law(a: i32) -> bool {
    let p = active_prism();
    let constructed = p.review(a);
    p.preview(&constructed) == Some(a)
}

// Law 2: Preview-Review (If preview succeeds, reviewing yields the original structure)
// If preview(s) == Some(a) then review(a) == s
#[test]
fn test_prism_preview_review_law() {
    let p = active_prism();
    let s = TestStatus::Active(42);
    if let Some(focus) = p.preview(&s) {
        assert_eq!(p.review(focus), s);
    } else {
        panic!("preview should have succeeded");
    }

    let non_matching = TestStatus::Pending;
    assert_eq!(p.preview(&non_matching), None);
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
            Outer::Inner(status) => Some(status.clone()),
            _ => None,
        },
        Outer::Inner,
    );

    let composed = outer_prism.then(active_prism());

    // Review through composition
    let built = composed.review(99);
    assert_eq!(built, Outer::Inner(TestStatus::Active(99)));

    // Preview through composition
    assert_eq!(composed.preview(&built), Some(99));
    assert_eq!(composed.preview(&Outer::Other), None);
    assert_eq!(
        composed.preview(&Outer::Inner(TestStatus::Completed("ok".to_string()))),
        None
    );

    // Modify through composition
    let modified = composed.modify(built, |x| x + 1);
    assert_eq!(modified, Outer::Inner(TestStatus::Active(100)));
}

#[test]
fn test_string_prism_review_preview() {
    let p = completed_prism();
    let original = "Hello Rustica".to_string();
    let s = p.review(original.clone());
    assert_eq!(p.preview(&s), Some(original));
}
