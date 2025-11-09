use criterion::Criterion;
use rustica::datatypes::prism::Prism;
use std::collections::HashMap;
use std::hint::black_box;

#[derive(Debug, Clone, PartialEq)]
enum Message {
    Text(String),
    Binary(Vec<u8>),
    Json(String),
    Empty,
}

#[derive(Debug, Clone, PartialEq)]
enum ConfigValue {
    Integer(i64),
    Float(f64),
    String(String),
    Dictionary(HashMap<String, ConfigValue>),
    Array(Vec<ConfigValue>),
}

#[derive(Debug, Clone, PartialEq)]
enum Status {
    Active { name: String, level: u32 },
    Inactive { name: String, since: u64 },
    Pending { name: String },
}

pub fn prism_benchmarks(c: &mut Criterion) {
    let mut group = c.benchmark_group("Prism");

    // Setup test data
    let text_msg = Message::Text("Hello, world!".to_string());
    let binary_msg = Message::Binary(vec![1, 2, 3, 4, 5]);
    let empty_msg = Message::Empty;
    let json_msg = Message::Json(r#"{"key": "value"}"#.to_string());

    let mut config_dict = HashMap::new();
    config_dict.insert("name".to_string(), ConfigValue::String("Alice".to_string()));
    config_dict.insert("age".to_string(), ConfigValue::Integer(30));
    let dict_config = ConfigValue::Dictionary(config_dict);

    let float_config = ConfigValue::Float(3.14);
    let array_config = ConfigValue::Array(vec![ConfigValue::Integer(1), ConfigValue::Integer(2)]);
    let inactive_status = Status::Inactive {
        name: "Charlie".to_string(),
        since: 1234567890,
    };
    let pending_status = Status::Pending {
        name: "Dave".to_string(),
    };

    // Create prisms
    let text_prism = Prism::new(
        |m: &Message| match m {
            Message::Text(t) => Some(t.clone()),
            _ => None,
        },
        |t: &String| Message::Text(t.clone()),
    );

    let binary_prism = Prism::new(
        |m: &Message| match m {
            Message::Binary(b) => Some(b.clone()),
            _ => None,
        },
        |b: &Vec<u8>| Message::Binary(b.clone()),
    );

    let dict_prism = Prism::new(
        |cv: &ConfigValue| match cv {
            ConfigValue::Dictionary(map) => Some(map.clone()),
            _ => None,
        },
        |map: &HashMap<String, ConfigValue>| ConfigValue::Dictionary(map.clone()),
    );

    let int_prism = Prism::new(
        |cv: &ConfigValue| match cv {
            ConfigValue::Integer(i) => Some(*i),
            _ => None,
        },
        |i: &i64| ConfigValue::Integer(*i),
    );

    let json_prism = Prism::new(
        |m: &Message| match m {
            Message::Json(s) => Some(s.clone()),
            _ => None,
        },
        |s: &String| Message::Json(s.clone()),
    );

    let float_prism = Prism::new(
        |cv: &ConfigValue| match cv {
            ConfigValue::Float(f) => Some(*f),
            _ => None,
        },
        |f: &f64| ConfigValue::Float(*f),
    );

    let array_prism = Prism::new(
        |cv: &ConfigValue| match cv {
            ConfigValue::Array(arr) => Some(arr.clone()),
            _ => None,
        },
        |arr: &Vec<ConfigValue>| ConfigValue::Array(arr.clone()),
    );

    let active_prism = Prism::for_case::<Status, (String, u32)>(
        |s: &Status| match s {
            Status::Active { name, level } => Some((name.clone(), *level)),
            _ => None,
        },
        |(name, level): &(String, u32)| Status::Active {
            name: name.clone(),
            level: *level,
        },
    );

    let inactive_prism = Prism::for_case::<Status, (String, u64)>(
        |s: &Status| match s {
            Status::Inactive { name, since } => Some((name.clone(), *since)),
            _ => None,
        },
        |(name, since): &(String, u64)| Status::Inactive {
            name: name.clone(),
            since: *since,
        },
    );

    let pending_prism = Prism::for_case::<Status, String>(
        |s: &Status| match s {
            Status::Pending { name } => Some(name.clone()),
            _ => None,
        },
        |name: &String| Status::Pending { name: name.clone() },
    );

    // Creation benchmarks
    group.bench_function("prism_new", |b| {
        b.iter(|| {
            let prism = Prism::new(
                |m: &Message| match m {
                    Message::Text(t) => Some(t.clone()),
                    _ => None,
                },
                |t: &String| Message::Text(t.clone()),
            );
            black_box(prism)
        })
    });

    group.bench_function("prism_for_case", |b| {
        b.iter(|| {
            let prism = Prism::for_case::<Message, String>(
                |m: &Message| match m {
                    Message::Text(t) => Some(t.clone()),
                    _ => None,
                },
                |t: &String| Message::Text(t.clone()),
            );
            black_box(prism)
        })
    });

    // Preview benchmarks - successful cases
    group.bench_function("prism_preview_success_simple", |b| {
        b.iter(|| {
            let result = text_prism.preview(&black_box(text_msg.clone()));
            black_box(result)
        })
    });

    group.bench_function("prism_preview_success_complex", |b| {
        b.iter(|| {
            let result = dict_prism.preview(&black_box(dict_config.clone()));
            black_box(result)
        })
    });

    group.bench_function("prism_preview_success_binary", |b| {
        b.iter(|| {
            let result = binary_prism.preview(&black_box(binary_msg.clone()));
            black_box(result)
        })
    });

    // Preview benchmarks - failure cases
    group.bench_function("prism_preview_failure", |b| {
        b.iter(|| {
            let result = text_prism.preview(&black_box(binary_msg.clone()));
            black_box(result)
        })
    });

    group.bench_function("prism_preview_failure_empty", |b| {
        b.iter(|| {
            let result = text_prism.preview(&black_box(empty_msg.clone()));
            black_box(result)
        })
    });

    // Review benchmarks
    group.bench_function("prism_review_simple", |b| {
        b.iter(|| {
            let result = text_prism.review(&black_box("Test message".to_string()));
            black_box(result)
        })
    });

    group.bench_function("prism_review_complex", |b| {
        b.iter(|| {
            let mut test_dict = HashMap::new();
            test_dict.insert("test".to_string(), ConfigValue::String("value".to_string()));
            let result = dict_prism.review(&black_box(test_dict));
            black_box(result)
        })
    });

    group.bench_function("prism_review_binary", |b| {
        b.iter(|| {
            let data = vec![10, 20, 30, 40, 50];
            let result = binary_prism.review(&black_box(data));
            black_box(result)
        })
    });

    group.bench_function("prism_review_tuple", |b| {
        b.iter(|| {
            let data = ("David".to_string(), 10u32);
            let result = active_prism.review(&black_box(data));
            black_box(result)
        })
    });

    // Round-trip benchmarks (preview then review)
    group.bench_function("prism_roundtrip_success", |b| {
        b.iter(|| {
            let original = black_box(text_msg.clone());
            let result = if let Some(extracted) = text_prism.preview(&original) {
                text_prism.review(&extracted)
            } else {
                original.clone()
            };
            black_box(result)
        })
    });

    group.bench_function("prism_roundtrip_complex", |b| {
        b.iter(|| {
            let original = black_box(dict_config.clone());
            let result = if let Some(extracted) = dict_prism.preview(&original) {
                dict_prism.review(&extracted)
            } else {
                original.clone()
            };
            black_box(result)
        })
    });

    // Prism composition benchmarks - showing prism advantages
    group.bench_function("prism_composition", |b| {
        // Compose text prism with length check
        let long_text_prism = text_prism.compose_prism(prism::Prism::new(
            |s: &String| if s.len() > 10 { Some(s.len()) } else { None },
            |len| format!("text of length {}", len),
        ));

        b.iter(|| {
            let result = long_text_prism.preview(&black_box(text_msg.clone()));
            black_box(result)
        })
    });

    group.bench_function("prism_multiple_operations", |b| {
        b.iter(|| {
            // Multiple prism operations in sequence
            let msg = black_box(text_msg.clone());
            let text_result = text_prism.preview(&msg);
            let processed = text_result.map(|s| s.to_uppercase());
            black_box(processed)
        })
    });

    // Multiple prism operations
    group.bench_function("prism_multiple_previews", |b| {
        b.iter(|| {
            let msg = black_box(text_msg.clone());
            let text_result = text_prism.preview(&msg);
            let binary_result = binary_prism.preview(&msg);
            black_box((text_result, binary_result))
        })
    });

    // Large data structure benchmarks
    group.bench_function("prism_large_binary_preview", |b| {
        let large_binary = Message::Binary((0..10000).map(|i| (i % 256) as u8).collect());
        b.iter(|| {
            let result = binary_prism.preview(&black_box(large_binary.clone()));
            black_box(result)
        })
    });

    group.bench_function("prism_large_binary_review", |b| {
        let large_data: Vec<u8> = (0..10000).map(|i| (i % 256) as u8).collect();
        b.iter(|| {
            let result = binary_prism.review(&black_box(large_data.clone()));
            black_box(result)
        })
    });

    // Nested structure benchmarks
    group.bench_function("prism_nested_config", |b| {
        let mut nested_dict = HashMap::new();
        nested_dict.insert(
            "level1".to_string(),
            ConfigValue::Dictionary({
                let mut inner = HashMap::new();
                inner.insert(
                    "level2".to_string(),
                    ConfigValue::String("deep".to_string()),
                );
                inner
            }),
        );
        let nested_config = ConfigValue::Dictionary(nested_dict);

        b.iter(|| {
            let result = dict_prism.preview(&black_box(nested_config.clone()));
            black_box(result)
        })
    });

    // Benchmarks for unused variants
    group.bench_function("prism_json_preview", |b| {
        b.iter(|| {
            let msg = black_box(json_msg.clone());
            let result = json_prism.preview(&msg);
            black_box(result)
        })
    });

    group.bench_function("prism_float_preview", |b| {
        b.iter(|| {
            let config = black_box(float_config.clone());
            let result = float_prism.preview(&config);
            black_box(result)
        })
    });

    group.bench_function("prism_array_preview", |b| {
        b.iter(|| {
            let config = black_box(array_config.clone());
            let result = array_prism.preview(&config);
            black_box(result)
        })
    });

    group.bench_function("prism_inactive_preview", |b| {
        b.iter(|| {
            let status = black_box(inactive_status.clone());
            let result = inactive_prism.preview(&status);
            black_box(result)
        })
    });

    group.bench_function("prism_pending_preview", |b| {
        b.iter(|| {
            let status = black_box(pending_status.clone());
            let result = pending_prism.preview(&status);
            black_box(result)
        })
    });

    group.bench_function("prism_int_usage", |b| {
        b.iter(|| {
            let config = black_box(ConfigValue::Integer(42));
            let result = int_prism.preview(&config);
            black_box(result)
        })
    });

    group.finish();
}
