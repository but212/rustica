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

// --- Helper Prisms ---

// Prism for Status::Active(String)
fn active_prism()
-> Prism<Status, String, impl Fn(&Status) -> Option<String>, impl Fn(&String) -> Status> {
    Prism::new(
        |s: &Status| match s {
            Status::Active(name) => Some(name.clone()),
            _ => None,
        },
        |name: &String| Status::Active(name.clone()),
    )
}

// Prism for Status::Inactive (focuses on Unit `()`)
fn inactive_prism() -> Prism<Status, (), impl Fn(&Status) -> Option<()>, impl Fn(&()) -> Status> {
    Prism::for_case::<Status, ()>(
        |s: &Status| match s {
            Status::Inactive => Some(()),
            _ => None,
        },
        |_: &()| Status::Inactive,
    )
}

// Prism for Status::Error { code, message }
// Focuses on a tuple (u32, String)
// Note: Complex return type is necessary for Prism implementation
#[allow(clippy::type_complexity)]
fn error_prism() -> Prism<
    Status,
    (u32, String),
    impl Fn(&Status) -> Option<(u32, String)>,
    impl Fn(&(u32, String)) -> Status,
> {
    Prism::new(
        |s: &Status| match s {
            Status::Error { code, message } => Some((*code, message.clone())),
            _ => None,
        },
        |&(code, ref message): &(u32, String)| Status::Error {
            code,
            message: message.clone(),
        },
    )
}

// --- Helper Lens ---

// Lens for User.status
fn user_status_lens() -> Lens<User, Status, impl Fn(&User) -> Status, impl Fn(User, Status) -> User>
{
    Lens::new(
        |u: &User| u.status.clone(),
        |u: User, status: Status| User { status, ..u },
    )
}

// --- Test Cases ---

#[test]
fn test_prism_new_and_for_case() {
    // Test creating with `new` (equivalent to active_prism() helper)
    let prism1 = Prism::new(
        |s: &Status| match s {
            Status::Active(name) => Some(name.clone()),
            _ => None,
        },
        |name: &String| Status::Active(name.clone()),
    );

    // Test creating with `for_case` (equivalent to inactive_prism() helper)
    let prism2 = Prism::for_case::<Status, ()>(
        |s: &Status| match s {
            Status::Inactive => Some(()),
            _ => None,
        },
        |_: &()| Status::Inactive,
    );

    let active_status = Status::Active("test".to_string());
    let inactive_status = Status::Inactive;

    assert_eq!(prism1.preview(&active_status), Some("test".to_string()));
    assert_eq!(prism2.preview(&inactive_status), Some(()));
}

#[test]
fn test_prism_preview_success() {
    let active = Status::Active("running".to_string());
    let inactive = Status::Inactive;
    let error = Status::Error {
        code: 500,
        message: "Server Down".to_string(),
    };

    assert_eq!(active_prism().preview(&active), Some("running".to_string()));
    assert_eq!(inactive_prism().preview(&inactive), Some(()));
    assert_eq!(
        error_prism().preview(&error),
        Some((500, "Server Down".to_string()))
    );
}

#[test]
fn test_prism_preview_failure() {
    let active = Status::Active("running".to_string());
    let inactive = Status::Inactive;
    let error = Status::Error {
        code: 500,
        message: "Server Down".to_string(),
    };

    // Try to preview wrong variant
    assert_eq!(active_prism().preview(&inactive), None);
    assert_eq!(active_prism().preview(&error), None);

    assert_eq!(inactive_prism().preview(&active), None);
    assert_eq!(inactive_prism().preview(&error), None);

    assert_eq!(error_prism().preview(&active), None);
    assert_eq!(error_prism().preview(&inactive), None);
}

#[test]
fn test_prism_review() {
    // Review Active
    let name = "Alice".to_string();
    let reviewed_active = active_prism().review(&name);
    assert_eq!(reviewed_active, Status::Active("Alice".to_string()));

    // Review Inactive
    let reviewed_inactive = inactive_prism().review(&());
    assert_eq!(reviewed_inactive, Status::Inactive);

    // Review Error
    let error_data = (404, "Not Found".to_string());
    let reviewed_error = error_prism().review(&error_data);
    assert_eq!(
        reviewed_error,
        Status::Error {
            code: 404,
            message: "Not Found".to_string()
        }
    );
}

#[test]
fn test_prism_lens_composition() {
    let user_active = User {
        id: 1,
        status: Status::Active("online".to_string()),
    };
    let user_inactive = User {
        id: 2,
        status: Status::Inactive,
    };

    let status_lens = user_status_lens();
    let prism = active_prism();

    // --- Get Path: Lens -> Prism ---

    // Get status via lens, then preview via prism
    let status1 = status_lens.get(&user_active);
    let preview1 = prism.preview(&status1);
    assert_eq!(preview1, Some("online".to_string()));

    let status2 = status_lens.get(&user_inactive);
    let preview2 = prism.preview(&status2);
    assert_eq!(preview2, None);

    // --- Set/Modify Path: Lens -> Prism -> (Modify A) -> Prism -> Lens ---

    // Modify the user's status *if* it's Active
    let updated_user = status_lens.modify(user_active.clone(), |status| {
        // Try to get the string value using the prism
        match prism.preview(&status) {
            Some(current_name) => {
                // If successful, modify the name and review back to Status
                let new_name = format!("{current_name}-updated");
                prism.review(&new_name)
            },
            None => {
                // If not the 'Active' variant, return the status unchanged
                status
            },
        }
    });
    assert_eq!(
        updated_user.status,
        Status::Active("online-updated".to_string())
    );

    // Try to modify an inactive user - should remain unchanged
    let not_updated_user = status_lens.modify(user_inactive.clone(), |status| {
        match prism.preview(&status) {
            Some(current_name) => {
                let new_name = format!("{current_name}-updated");
                prism.review(&new_name)
            },
            None => {
                status // Prism preview returns None, status is unchanged
            },
        }
    });
    assert_eq!(not_updated_user.status, Status::Inactive);
}

// --- Prism modify and set_if_different Tests ---

#[test]
fn test_prism_modify() {
    let active = Status::Active("Alice".to_string());
    let prism = active_prism();

    // Value changes
    let modified = prism.modify(active.clone(), |name| format!("{}-updated", name));
    assert_eq!(modified, Status::Active("Alice-updated".to_string()));

    // Value unchanged (structural sharing)
    let unchanged = prism.modify(active.clone(), |name| name);
    assert_eq!(unchanged, active);

    // Preview fails - original returned
    let inactive = Status::Inactive;
    let still_inactive = prism.modify(inactive.clone(), |name| format!("{}-updated", name));
    assert_eq!(still_inactive, Status::Inactive);
}

#[test]
fn test_prism_set_if_different() {
    let active = Status::Active("Alice".to_string());
    let prism = active_prism();

    // Set to different value
    let changed = prism.set_if_different(active.clone(), "Bob".to_string());
    assert_eq!(changed, Status::Active("Bob".to_string()));

    // Set to same value (structural sharing)
    let same = prism.set_if_different(active.clone(), "Alice".to_string());
    assert_eq!(same, active);

    // Preview fails - create new structure
    let inactive = Status::Inactive;
    let now_active = prism.set_if_different(inactive, "Charlie".to_string());
    assert_eq!(now_active, Status::Active("Charlie".to_string()));
}

#[test]
fn test_prism_modify_error_variant() {
    let error = Status::Error {
        code: 500,
        message: "Server Down".to_string(),
    };
    let prism = error_prism();

    // Modify error variant
    let modified = prism.modify(error.clone(), |(code, msg)| {
        (code + 1, format!("{}-modified", msg))
    });
    assert_eq!(
        modified,
        Status::Error {
            code: 501,
            message: "Server Down-modified".to_string()
        }
    );
}

// --- Prism Laws Tests ---

#[test]
fn test_prism_review_preview_law() {
    // Review-Preview Law: preview(review(a)) == Some(a)
    // "If we construct a value and then extract it, we get back the original"
    let prism = active_prism();
    let value = "test_user".to_string();

    let constructed = prism.review(&value);
    assert_eq!(
        prism.preview(&constructed),
        Some(value),
        "Review-Preview law violated"
    );
}

#[test]
fn test_prism_review_preview_law_all_variants() {
    // Test Review-Preview law for all prisms

    // Active variant
    let active_p = active_prism();
    let active_val = "Alice".to_string();
    let active_constructed = active_p.review(&active_val);
    assert_eq!(active_p.preview(&active_constructed), Some(active_val));

    // Inactive variant
    let inactive_p = inactive_prism();
    let inactive_constructed = inactive_p.review(&());
    assert_eq!(inactive_p.preview(&inactive_constructed), Some(()));

    // Error variant
    let error_p = error_prism();
    let error_val = (404, "Not Found".to_string());
    let error_constructed = error_p.review(&error_val);
    assert_eq!(error_p.preview(&error_constructed), Some(error_val));
}

// --- Prism Composition Tests ---

#[test]
fn test_prism_compose() {
    // Test the compose method for prism composition
    #[derive(Debug, Clone, PartialEq)]
    enum Inner {
        Value(i32),
        Empty,
    }

    #[derive(Debug, Clone, PartialEq)]
    enum Outer {
        Nested(Inner),
        Other(String),
    }

    let nested_prism = Prism::new(
        |o: &Outer| match o {
            Outer::Nested(inner) => Some(inner.clone()),
            _ => None,
        },
        |i: &Inner| Outer::Nested(i.clone()),
    );

    let value_prism = Prism::new(
        |i: &Inner| match i {
            Inner::Value(v) => Some(*v),
            _ => None,
        },
        |v: &i32| Inner::Value(*v),
    );

    // Compose prisms
    let deep_prism = nested_prism.compose(value_prism);

    // Test preview through composed prism
    let data = Outer::Nested(Inner::Value(42));
    assert_eq!(deep_prism.preview(&data), Some(42));

    // Test preview fails for wrong variant
    let wrong = Outer::Nested(Inner::Empty);
    assert_eq!(deep_prism.preview(&wrong), None);

    let other = Outer::Other("test".to_string());
    assert_eq!(deep_prism.preview(&other), None);

    // Test review through composed prism
    let constructed = deep_prism.review(&100);
    assert_eq!(constructed, Outer::Nested(Inner::Value(100)));
}

#[test]
fn test_prism_then_chaining() {
    // Test the then method for multiple prism chaining
    #[derive(Debug, Clone, PartialEq)]
    enum Level3 {
        Data(String),
    }

    #[derive(Debug, Clone, PartialEq)]
    enum Level2 {
        Inner(Level3),
        None2,
    }

    #[derive(Debug, Clone, PartialEq)]
    enum Level1 {
        Outer(Level2),
        None1,
    }

    let l1_l2 = Prism::new(
        |l: &Level1| match l {
            Level1::Outer(l2) => Some(l2.clone()),
            _ => None,
        },
        |l2: &Level2| Level1::Outer(l2.clone()),
    );

    let l2_l3 = Prism::new(
        |l: &Level2| match l {
            Level2::Inner(l3) => Some(l3.clone()),
            _ => None,
        },
        |l3: &Level3| Level2::Inner(l3.clone()),
    );

    let l3_data = Prism::new(
        |l: &Level3| {
            let Level3::Data(s) = l;
            Some(s.clone())
        },
        |s: &String| Level3::Data(s.clone()),
    );

    // Chain multiple prisms
    let deep = l1_l2.then(l2_l3).then(l3_data);

    // Test preview
    let data = Level1::Outer(Level2::Inner(Level3::Data("hello".to_string())));
    assert_eq!(deep.preview(&data), Some("hello".to_string()));

    // Test review
    let constructed = deep.review(&"world".to_string());
    assert_eq!(
        constructed,
        Level1::Outer(Level2::Inner(Level3::Data("world".to_string())))
    );

    // Test preview fails at different levels
    let fail_at_l1 = Level1::None1;
    assert_eq!(deep.preview(&fail_at_l1), None);

    let fail_at_l2 = Level1::Outer(Level2::None2);
    assert_eq!(deep.preview(&fail_at_l2), None);
}

#[test]
fn test_prism_compose_review_preview_law() {
    // Verify that composed prisms still satisfy Review-Preview law
    #[derive(Debug, Clone, PartialEq)]
    enum Inner {
        Value(i32),
    }

    #[derive(Debug, Clone, PartialEq)]
    enum Outer {
        Nested(Inner),
    }

    let nested_prism = Prism::new(
        |o: &Outer| match o {
            Outer::Nested(inner) => Some(inner.clone()),
        },
        |i: &Inner| Outer::Nested(i.clone()),
    );

    let value_prism = Prism::new(
        |i: &Inner| match i {
            Inner::Value(v) => Some(*v),
        },
        |v: &i32| Inner::Value(*v),
    );

    let composed = nested_prism.compose(value_prism);

    // Review-Preview law for composed prism
    let value = 42;
    let constructed = composed.review(&value);
    assert_eq!(
        composed.preview(&constructed),
        Some(value),
        "Composed prism violates Review-Preview law"
    );
}
