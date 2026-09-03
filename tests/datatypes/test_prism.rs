use rustica::datatypes::lens::Lens;
use rustica::datatypes::prism::Prism;
use std::collections::HashMap;

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

type ActivePrism =
    Prism<Status, String, Box<dyn Fn(&Status) -> Option<String>>, Box<dyn Fn(&String) -> Status>>;

fn active_prism() -> ActivePrism {
    Prism::new(
        Box::new(|s| match s {
            Status::Active(n) => Some(n.clone()),
            _ => None,
        }),
        Box::new(|n| Status::Active(n.clone())),
    )
}

type ErrorPrism = Prism<
    Status,
    (u32, String),
    Box<dyn Fn(&Status) -> Option<(u32, String)>>,
    Box<dyn Fn(&(u32, String)) -> Status>,
>;

fn error_prism() -> ErrorPrism {
    Prism::new(
        Box::new(|s| match s {
            Status::Error { code, message } => Some((*code, message.clone())),
            _ => None,
        }),
        Box::new(|&(code, ref msg)| Status::Error {
            code,
            message: msg.clone(),
        }),
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
    let reset = prism.set_if_different(error, (200, "OK".to_string()));
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
fn test_prism_complex_variant_extraction() {
    #[derive(Debug, Clone, PartialEq)]
    enum ConfigValue {
        Integer(i64),
        String(String),
        Dictionary(HashMap<String, ConfigValue>),
    }

    let dict_prism = Prism::new(
        |value: &ConfigValue| match value {
            ConfigValue::Dictionary(map) => Some(map.clone()),
            _ => None,
        },
        |map: &HashMap<String, ConfigValue>| ConfigValue::Dictionary(map.clone()),
    );

    let mut preferences = HashMap::new();
    preferences.insert("name".to_string(), ConfigValue::String("Alice".to_string()));
    preferences.insert("age".to_string(), ConfigValue::Integer(30));
    let config = ConfigValue::Dictionary(preferences);

    if let Some(values) = dict_prism.preview(&config) {
        assert!(matches!(values.get("name"), Some(ConfigValue::String(name)) if name == "Alice"));
        let mut updated_values = values.clone();
        updated_values.insert("theme".to_string(), ConfigValue::String("dark".to_string()));
        let updated_config = dict_prism.review(&updated_values);
        let new_values = match dict_prism.preview(&updated_config) {
            Some(values) => values,
            None => panic!("dictionary prism did not match after review"),
        };
        assert_eq!(new_values.len(), 3);
        assert!(new_values.contains_key("theme"));
    } else {
        panic!("dictionary prism did not match");
    }
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
