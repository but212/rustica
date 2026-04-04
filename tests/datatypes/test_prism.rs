use rustica::datatypes::lens::Lens;
use rustica::datatypes::prism::Prism;

// --- Test Data Structures ---

#[derive(Clone, Debug, PartialEq)]
enum Status {
    Active(String),
    Inactive,
    Error { code: u32, message: String },
}

#[derive(Clone, Debug, PartialEq)]
struct User {
    id: u64,
    status: Status,
}

// --- Helper Factories ---

fn active_prism()
-> Prism<Status, String, impl Fn(&Status) -> Option<String>, impl Fn(&String) -> Status> {
    Prism::new(
        |s| match s {
            Status::Active(n) => Some(n.clone()),
            _ => None,
        },
        |n| Status::Active(n.clone()),
    )
}

fn error_prism() -> Prism<
    Status,
    (u32, String),
    impl Fn(&Status) -> Option<(u32, String)>,
    impl Fn(&(u32, String)) -> Status,
> {
    Prism::new(
        |s| match s {
            Status::Error { code, message } => Some((*code, message.clone())),
            _ => None,
        },
        |&(code, ref msg)| Status::Error {
            code,
            message: msg.clone(),
        },
    )
}

// --- Test Cases ---

#[test]
fn test_prism_behavior_and_laws() {
    let prism = active_prism();
    let target = Status::Active("Alice".to_string());
    let other = Status::Inactive;

    // 1. Preview: Extract value if variant matches
    assert_eq!(prism.preview(&target), Some("Alice".to_string()));
    assert_eq!(prism.preview(&other), None);

    // 2. Review: Construct variant from value
    assert_eq!(
        prism.review(&"Bob".to_string()),
        Status::Active("Bob".to_string())
    );

    // 3. Review-Preview Law: preview(review(v)) == Some(v)
    let val = "LawCheck".to_string();
    assert_eq!(prism.preview(&prism.review(&val)), Some(val));
}

#[test]
fn test_prism_updates_and_sharing() {
    let prism = error_prism();
    let error = Status::Error {
        code: 500,
        message: "Fail".to_string(),
    };

    // 1. Modify: Update value if matches
    let updated = prism.modify(error.clone(), |(c, m)| (c + 1, format!("{}-fixed", m)));
    assert_eq!(
        updated,
        Status::Error {
            code: 501,
            message: "Fail-fixed".to_string()
        }
    );

    // 2. Structural Sharing: Return original if no change
    let identical = prism.modify(error.clone(), |v| v);
    assert_eq!(identical, error);

    // 3. Set if different: Update specific focus
    let reset = prism.set_if_different(error.clone(), (200, "OK".to_string()));
    assert_eq!(
        reset,
        Status::Error {
            code: 200,
            message: "OK".to_string()
        }
    );

    // 4. Ignore mismatching variants
    let active = Status::Active("online".to_string());
    assert_eq!(
        prism.modify(active.clone(), |_| (0, "".to_string())),
        active
    );
}

#[test]
fn test_prism_composition() {
    #[derive(Debug, Clone, PartialEq)]
    enum Inner {
        Val(i32),
        Empty,
    }
    #[derive(Debug, Clone, PartialEq)]
    enum Outer {
        Nested(Inner),
        Other,
    }

    let p_outer = Prism::new(
        |o| match o {
            Outer::Nested(i) => Some(i.clone()),
            _ => None,
        },
        |i| Outer::Nested(i.clone()),
    );
    let p_inner = Prism::new(
        |i| match i {
            Inner::Val(v) => Some(*v),
            _ => None,
        },
        |v| Inner::Val(*v),
    );

    // Composite via 'compose' or 'then'
    let deep = p_outer.then(p_inner);
    let data = Outer::Nested(Inner::Val(42));

    assert_eq!(deep.preview(&data), Some(42));
    assert_eq!(deep.review(&100), Outer::Nested(Inner::Val(100)));
    assert_eq!(deep.preview(&Outer::Nested(Inner::Empty)), None);
    assert_eq!(deep.preview(&Outer::Other), None);
}

#[test]
fn test_prism_lens_integration() {
    let user = User {
        id: 1,
        status: Status::Active("online".to_string()),
    };
    let status_lens = Lens::new(|u: &User| u.status.clone(), |u, s| User { status: s, ..u });
    let active_p = active_prism();

    // Updating deep enum field through Lens + Prism
    let updated_user = status_lens.modify(user, |status| {
        active_p.modify(status, |name| format!("{}-away", name))
    });

    assert_eq!(
        updated_user.status,
        Status::Active("online-away".to_string())
    );

    // Ensure non-matching variants remain intact through the pipeline
    let inactive_user = User {
        id: 2,
        status: Status::Inactive,
    };
    let ignored_user = status_lens.modify(inactive_user.clone(), |status| {
        active_p.modify(status, |name| format!("{}-away", name))
    });
    assert_eq!(ignored_user, inactive_user);
}
