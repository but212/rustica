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
fn active_prism(
) -> Prism<Status, String, impl Fn(&Status) -> Option<String>, impl Fn(&String) -> Status> {
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
                let new_name = format!("{}-updated", current_name);
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
                let new_name = format!("{}-updated", current_name);
                prism.review(&new_name)
            },
            None => {
                status // Prism preview returns None, status is unchanged
            },
        }
    });
    assert_eq!(not_updated_user.status, Status::Inactive);
}
