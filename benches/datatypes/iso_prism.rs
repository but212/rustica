use criterion::Criterion;
use rustica::datatypes::iso_prism::IsoPrism;
use rustica::traits::iso::Iso;
use std::collections::HashMap;
use std::hint::black_box;

#[derive(Clone, Debug, PartialEq)]
enum ApiResponse {
    Success(String),
    Error { code: u32, message: String },
    Loading,
    NotFound,
}

#[derive(Clone, Debug, PartialEq)]
enum DataValue {
    Integer(i64),
    Float(f64),
    Text(String),
    Boolean(bool),
    Array(Vec<DataValue>),
    Object(HashMap<String, DataValue>),
}

#[derive(Clone, Debug, PartialEq)]
enum NetworkResult<T> {
    Ok(T),
    Timeout,
    ConnectionError(String),
    ParseError { line: u32, column: u32 },
}

// Iso for ApiResponse Success variant
struct SuccessIso;
impl Iso<ApiResponse, Option<String>> for SuccessIso {
    type From = ApiResponse;
    type To = Option<String>;

    fn forward(&self, from: &ApiResponse) -> Option<String> {
        match from {
            ApiResponse::Success(s) => Some(s.clone()),
            _ => None,
        }
    }

    fn backward(&self, to: &Option<String>) -> ApiResponse {
        match to {
            Some(s) => ApiResponse::Success(s.clone()),
            None => ApiResponse::Loading, // Default fallback
        }
    }
}

// Iso for ApiResponse Error variant
struct ErrorIso;
impl Iso<ApiResponse, Option<(u32, String)>> for ErrorIso {
    type From = ApiResponse;
    type To = Option<(u32, String)>;

    fn forward(&self, from: &ApiResponse) -> Option<(u32, String)> {
        match from {
            ApiResponse::Error { code, message } => Some((*code, message.clone())),
            _ => None,
        }
    }

    fn backward(&self, to: &Option<(u32, String)>) -> ApiResponse {
        match to {
            Some((code, message)) => ApiResponse::Error {
                code: *code,
                message: message.clone(),
            },
            None => ApiResponse::Loading,
        }
    }
}

// Iso for DataValue Integer variant
struct IntegerIso;
impl Iso<DataValue, Option<i64>> for IntegerIso {
    type From = DataValue;
    type To = Option<i64>;

    fn forward(&self, from: &DataValue) -> Option<i64> {
        match from {
            DataValue::Integer(i) => Some(*i),
            _ => None,
        }
    }

    fn backward(&self, to: &Option<i64>) -> DataValue {
        match to {
            Some(i) => DataValue::Integer(*i),
            None => DataValue::Boolean(false), // Default fallback
        }
    }
}

// Iso for DataValue Text variant
struct TextIso;
impl Iso<DataValue, Option<String>> for TextIso {
    type From = DataValue;
    type To = Option<String>;

    fn forward(&self, from: &DataValue) -> Option<String> {
        match from {
            DataValue::Text(s) => Some(s.clone()),
            _ => None,
        }
    }

    fn backward(&self, to: &Option<String>) -> DataValue {
        match to {
            Some(s) => DataValue::Text(s.clone()),
            None => DataValue::Boolean(false),
        }
    }
}

// Iso for NetworkResult Ok variant
struct OkIso<T: Clone> {
    _phantom: std::marker::PhantomData<T>,
}

impl<T: Clone> OkIso<T> {
    fn new() -> Self {
        Self {
            _phantom: std::marker::PhantomData,
        }
    }
}

impl<T: Clone> Iso<NetworkResult<T>, Option<T>> for OkIso<T> {
    type From = NetworkResult<T>;
    type To = Option<T>;

    fn forward(&self, from: &NetworkResult<T>) -> Option<T> {
        match from {
            NetworkResult::Ok(t) => Some(t.clone()),
            _ => None,
        }
    }

    fn backward(&self, to: &Option<T>) -> NetworkResult<T> {
        match to {
            Some(t) => NetworkResult::Ok(t.clone()),
            None => NetworkResult::Timeout,
        }
    }
}

// Iso for NetworkResult ConnectionError variant
struct ConnectionErrorIso<T> {
    _phantom: std::marker::PhantomData<T>,
}

impl<T> ConnectionErrorIso<T> {
    fn new() -> Self {
        Self {
            _phantom: std::marker::PhantomData,
        }
    }
}

impl<T> Iso<NetworkResult<T>, Option<String>> for ConnectionErrorIso<T> {
    type From = NetworkResult<T>;
    type To = Option<String>;

    fn forward(&self, from: &NetworkResult<T>) -> Option<String> {
        match from {
            NetworkResult::ConnectionError(s) => Some(s.clone()),
            _ => None,
        }
    }

    fn backward(&self, to: &Option<String>) -> NetworkResult<T> {
        match to {
            Some(s) => NetworkResult::ConnectionError(s.clone()),
            None => NetworkResult::Timeout,
        }
    }
}

pub fn iso_prism_benchmarks(c: &mut Criterion) {
    let mut group = c.benchmark_group("IsoPrism");

    // Setup test data
    let success_response = ApiResponse::Success("Operation completed".to_string());
    let error_response = ApiResponse::Error {
        code: 404,
        message: "Not found".to_string(),
    };
    let loading_response = ApiResponse::Loading;

    let integer_value = DataValue::Integer(42);
    let text_value = DataValue::Text("Hello, world!".to_string());

    let ok_result: NetworkResult<String> = NetworkResult::Ok("Success".to_string());
    let timeout_result: NetworkResult<String> = NetworkResult::Timeout;

    // Create prisms
    let success_prism = IsoPrism::new(SuccessIso);
    let error_prism = IsoPrism::new(ErrorIso);
    let integer_prism = IsoPrism::new(IntegerIso);
    let text_prism = IsoPrism::new(TextIso);
    let ok_prism = IsoPrism::new(OkIso::<String>::new());
    let connection_error_prism = IsoPrism::new(ConnectionErrorIso::<String>::new());

    // Additional test data for unused variants
    let float_data = DataValue::Float(3.14);
    let object_data = {
        let mut map = HashMap::new();
        map.insert("key".to_string(), DataValue::Integer(42));
        DataValue::Object(map)
    };
    let connection_error_result =
        NetworkResult::ConnectionError::<String>("Connection failed".to_string());
    let parse_error_result = NetworkResult::ParseError::<String> {
        line: 10,
        column: 5,
    };

    // Creation benchmarks
    group.bench_function("iso_prism_new", |b| {
        b.iter(|| {
            let prism = IsoPrism::new(SuccessIso);
            black_box(prism)
        })
    });

    group.bench_function("iso_prism_new_generic", |b| {
        b.iter(|| {
            let prism = IsoPrism::new(OkIso::<String>::new());
            black_box(prism)
        })
    });

    // Preview benchmarks - successful cases
    group.bench_function("iso_prism_preview_success_simple", |b| {
        b.iter(|| {
            let result = success_prism.preview(&black_box(success_response.clone()));
            black_box(result)
        })
    });

    group.bench_function("iso_prism_preview_success_complex", |b| {
        b.iter(|| {
            let result = error_prism.preview(&black_box(error_response.clone()));
            black_box(result)
        })
    });

    group.bench_function("iso_prism_preview_success_primitive", |b| {
        b.iter(|| {
            let result = integer_prism.preview(&black_box(integer_value.clone()));
            black_box(result)
        })
    });

    group.bench_function("iso_prism_preview_success_generic", |b| {
        b.iter(|| {
            let result = ok_prism.preview(&black_box(ok_result.clone()));
            black_box(result)
        })
    });

    // Preview benchmarks - failure cases
    group.bench_function("iso_prism_preview_failure", |b| {
        b.iter(|| {
            let result = success_prism.preview(&black_box(error_response.clone()));
            black_box(result)
        })
    });

    group.bench_function("iso_prism_preview_failure_wrong_variant", |b| {
        b.iter(|| {
            let result = integer_prism.preview(&black_box(text_value.clone()));
            black_box(result)
        })
    });

    group.bench_function("iso_prism_preview_failure_generic", |b| {
        b.iter(|| {
            let result = ok_prism.preview(&black_box(timeout_result.clone()));
            black_box(result)
        })
    });

    // Review benchmarks
    group.bench_function("iso_prism_review_simple", |b| {
        b.iter(|| {
            let result = success_prism.review(&black_box("New success message".to_string()));
            black_box(result)
        })
    });

    group.bench_function("iso_prism_review_complex", |b| {
        b.iter(|| {
            let error_data = (500u32, "Internal server error".to_string());
            let result = error_prism.review(&black_box(error_data));
            black_box(result)
        })
    });

    group.bench_function("iso_prism_review_primitive", |b| {
        b.iter(|| {
            let result = integer_prism.review(&black_box(100i64));
            black_box(result)
        })
    });

    group.bench_function("iso_prism_review_generic", |b| {
        b.iter(|| {
            let result = ok_prism.review(&black_box("Generic success".to_string()));
            black_box(result)
        })
    });

    // Round-trip benchmarks (preview then review)
    group.bench_function("iso_prism_roundtrip_success", |b| {
        b.iter(|| {
            let original = black_box(success_response.clone());
            let result = if let Some(extracted) = success_prism.preview(&original) {
                success_prism.review(&extracted)
            } else {
                original.clone()
            };
            black_box(result)
        })
    });

    group.bench_function("iso_prism_roundtrip_complex", |b| {
        b.iter(|| {
            let original = black_box(error_response.clone());
            let result = if let Some(extracted) = error_prism.preview(&original) {
                error_prism.review(&extracted)
            } else {
                original.clone()
            };
            black_box(result)
        })
    });

    group.bench_function("iso_prism_roundtrip_generic", |b| {
        b.iter(|| {
            let original = black_box(ok_result.clone());
            let result = if let Some(extracted) = ok_prism.preview(&original) {
                ok_prism.review(&extracted)
            } else {
                original.clone()
            };
            black_box(result)
        })
    });

    // IsoPrism composition and transformation benchmarks
    group.bench_function("iso_prism_composition", |b| {
        // Compose success prism with data transformation
        let transformed_prism = success_prism.compose_prism(
            iso_prism::IsoPrism::new(
                |data: &SuccessData| data.clone(),
                |data| data
            )
        );
        
        b.iter(|| {
            let result = transformed_prism.preview(&black_box(success_response.clone()));
            black_box(result)
        })
    });

    group.bench_function("iso_prism_round_trip", |b| {
        b.iter(|| {
            // Test round-trip performance (preview + review)
            let response = black_box(success_response.clone());
            if let Some(extracted) = success_prism.preview(&response) {
                let reconstructed = success_prism.review(&extracted);
                black_box(reconstructed)
            }
        })
    });

    // Multiple prism operations
    group.bench_function("iso_prism_multiple_previews", |b| {
        b.iter(|| {
            let response = black_box(success_response.clone());
            let success_result = success_prism.preview(&response);
            let error_result = error_prism.preview(&response);
            black_box((success_result, error_result))
        })
    });

    // Large data structure benchmarks
    group.bench_function("iso_prism_large_text_preview", |b| {
        let large_text = DataValue::Text("Large text content ".repeat(1000));
        b.iter(|| {
            let result = text_prism.preview(&black_box(large_text.clone()));
            black_box(result)
        })
    });

    group.bench_function("iso_prism_large_text_review", |b| {
        let large_string = "Large string content ".repeat(1000);
        b.iter(|| {
            let result = text_prism.review(&black_box(large_string.clone()));
            black_box(result)
        })
    });

    // Nested enum benchmarks
    group.bench_function("iso_prism_nested_enum", |b| {
        let nested_data = DataValue::Array(vec![
            DataValue::Integer(1),
            DataValue::Text("nested".to_string()),
            DataValue::Boolean(true),
        ]);

        // Create a prism for Array variant
        struct ArrayIso;
        impl Iso<DataValue, Option<Vec<DataValue>>> for ArrayIso {
            type From = DataValue;
            type To = Option<Vec<DataValue>>;

            fn forward(&self, from: &DataValue) -> Option<Vec<DataValue>> {
                match from {
                    DataValue::Array(arr) => Some(arr.clone()),
                    _ => None,
                }
            }

            fn backward(&self, to: &Option<Vec<DataValue>>) -> DataValue {
                match to {
                    Some(arr) => DataValue::Array(arr.clone()),
                    None => DataValue::Boolean(false),
                }
            }
        }

        let array_prism = IsoPrism::new(ArrayIso);

        b.iter(|| {
            let result = array_prism.preview(&black_box(nested_data.clone()));
            black_box(result)
        })
    });

    // Error handling benchmarks
    group.bench_function("iso_prism_error_handling", |b| {
        let responses = vec![
            success_response.clone(),
            error_response.clone(),
            loading_response.clone(),
            ApiResponse::NotFound,
        ];

        b.iter(|| {
            let results: Vec<_> = responses
                .iter()
                .map(|r| success_prism.preview(&black_box(r.clone())))
                .collect();
            black_box(results)
        })
    });

    // Composition benchmark (if compose method is available)
    group.bench_function("iso_prism_composition_setup", |b| {
        // Create a simple composition scenario
        struct StringLengthIso;
        impl Iso<String, Option<usize>> for StringLengthIso {
            type From = String;
            type To = Option<usize>;

            fn forward(&self, from: &String) -> Option<usize> {
                Some(from.len())
            }

            fn backward(&self, to: &Option<usize>) -> String {
                match to {
                    Some(len) => "x".repeat(*len),
                    None => String::new(),
                }
            }
        }

        b.iter(|| {
            // Create new prisms for composition to avoid move issues
            let success_prism_local = IsoPrism::new(SuccessIso);
            let length_prism_local = IsoPrism::new(StringLengthIso);
            let composed = success_prism_local.compose(length_prism_local);
            black_box(composed)
        })
    });

    // Benchmarks for unused variants
    group.bench_function("iso_prism_float_data", |b| {
        b.iter(|| {
            let data = black_box(float_data.clone());
            // Simulate processing float data
            match data {
                DataValue::Float(f) => black_box(f * 2.0),
                _ => black_box(0.0),
            }
        })
    });

    group.bench_function("iso_prism_object_data", |b| {
        b.iter(|| {
            let data = black_box(object_data.clone());
            // Simulate processing object data
            match data {
                DataValue::Object(ref map) => black_box(map.len()),
                _ => black_box(0),
            }
        })
    });

    group.bench_function("iso_prism_connection_error", |b| {
        b.iter(|| {
            let result = black_box(connection_error_result.clone());
            let extracted = connection_error_prism.preview(&result);
            black_box(extracted)
        })
    });

    group.bench_function("iso_prism_parse_error", |b| {
        b.iter(|| {
            let result = black_box(parse_error_result.clone());
            // Simulate processing parse error
            match result {
                NetworkResult::ParseError { line, column } => black_box(line + column),
                _ => black_box(0),
            }
        })
    });

    group.finish();
}
