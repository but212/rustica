use criterion::{black_box, Criterion};
use rustica::datatypes::maybe::Maybe;
use rustica::datatypes::prism::Prism;
use rustica::traits::monad::Monad;
use std::collections::HashMap;

// Simple test structures for benchmarking
#[derive(Debug, PartialEq, Eq, Clone)]
enum Shape {
    Circle(u32),             // radius
    Rectangle(u32, u32),     // width, height
    Triangle(u32, u32, u32), // sides
}

// More complex data structures for real-world benchmarks
#[derive(Debug, PartialEq, Eq, Clone)]
enum UserStatus {
    LoggedIn {
        username: String,
        session_id: String,
    },
    LoggedOut,
    Suspended {
        reason: String,
    },
}

#[derive(Debug, Clone)]
#[allow(dead_code)]
enum ApiResponse {
    Success {
        data: String,
        metadata: HashMap<String, String>,
    },
    Error {
        code: u32,
        message: String,
    },
    Pending {
        job_id: String,
    },
    Redirect {
        url: String,
    },
}

#[derive(Debug, PartialEq, Eq, Clone)]
#[allow(dead_code)]
enum NetworkPacket {
    Data {
        payload: Vec<u8>,
        sequence_number: u32,
    },
    Ack {
        sequence_number: u32,
    },
    SyncRequest,
    SyncResponse {
        time_ms: u64,
    },
}

pub fn prism_benchmarks(c: &mut Criterion) {
    let mut group = c.benchmark_group("Prism");

    // ======== BASIC OPERATIONS ========

    // Create basic prisms
    let circle_prism: Prism<Shape, u32> = Prism::new(
        |s: &Shape| match s {
            Shape::Circle(r) => Some(*r),
            _ => None,
        },
        |r: &u32| Shape::Circle(*r),
    );

    let rectangle_prism: Prism<Shape, (u32, u32)> = Prism::new(
        |s: &Shape| match s {
            Shape::Rectangle(w, h) => Some((*w, *h)),
            _ => None,
        },
        |&(w, h): &(u32, u32)| Shape::Rectangle(w, h),
    );

    let triangle_prism: Prism<Shape, (u32, u32, u32)> = Prism::new(
        |s: &Shape| match s {
            Shape::Triangle(a, b, c) => Some((*a, *b, *c)),
            _ => None,
        },
        |&(a, b, c): &(u32, u32, u32)| Shape::Triangle(a, b, c),
    );

    let circle = Shape::Circle(10);
    let rectangle = Shape::Rectangle(20, 30);
    let triangle = Shape::Triangle(3, 4, 5);

    // Basic preview operations (get values)
    group.bench_function("preview_success", |b| {
        b.iter(|| {
            black_box(circle_prism.preview(&circle));
        });
    });

    group.bench_function("preview_failure", |b| {
        b.iter(|| {
            black_box(circle_prism.preview(&rectangle));
        });
    });

    // Basic review operations (create values)
    group.bench_function("review", |b| {
        b.iter(|| {
            black_box(circle_prism.review(&15u32));
        });
    });

    // ======== COMPOSITE OPERATIONS ========

    // Simulate modify operations by combining preview and review
    group.bench_function("modify_success", |b| {
        b.iter(|| {
            // Only modify if preview returns Some
            let result = match circle_prism.preview(&circle) {
                Some(radius) => circle_prism.review(&(radius * 2)),
                None => circle.clone(),
            };
            black_box(result);
        });
    });

    group.bench_function("modify_failure", |b| {
        b.iter(|| {
            // This will return the original shape since preview will return None
            let result = match circle_prism.preview(&rectangle) {
                Some(radius) => circle_prism.review(&(radius * 2)),
                None => rectangle.clone(),
            };
            black_box(result);
        });
    });

    // Chain of operations
    group.bench_function("chained_operations", |b| {
        b.iter(|| {
            let opt_radius: Option<u32> = circle_prism.preview(&circle);
            let result = match opt_radius {
                Some(r) if r > 5 => {
                    let new_r = r * 2;
                    if new_r > 25 {
                        // Create a rectangle instead
                        rectangle_prism.review(&(new_r, new_r / 2))
                    } else {
                        // Create a new circle
                        circle_prism.review(&new_r)
                    }
                }
                Some(r) => circle_prism.review(&r),
                None => circle.clone(),
            };
            black_box(result);
        });
    });

    // ======== COMPLEX DATA OPERATIONS ========

    // Set up user status prisms
    let logged_in_prism: Prism<UserStatus, (String, String)> = Prism::new(
        |status: &UserStatus| match status {
            UserStatus::LoggedIn {
                username,
                session_id,
            } => Some((username.clone(), session_id.clone())),
            _ => None,
        },
        |&(ref username, ref session_id): &(String, String)| UserStatus::LoggedIn {
            username: username.clone(),
            session_id: session_id.clone(),
        },
    );

    // Create sample data
    let logged_in_user = UserStatus::LoggedIn {
        username: "alice".to_string(),
        session_id: "abc123".to_string(),
    };

    let suspended_user = UserStatus::Suspended {
        reason: "Violation of terms".to_string(),
    };

    // Complex preview operations
    group.bench_function("complex_preview_success", |b| {
        b.iter(|| {
            black_box(logged_in_prism.preview(&logged_in_user));
        });
    });

    group.bench_function("complex_preview_wrong_variant", |b| {
        b.iter(|| {
            black_box(logged_in_prism.preview(&suspended_user));
        });
    });

    // Complex review operations
    group.bench_function("complex_review", |b| {
        b.iter(|| {
            black_box(logged_in_prism.review(&("bob".to_string(), "xyz789".to_string())));
        });
    });

    // ======== API RESPONSE OPERATIONS ========

    // Set up API response prisms
    let success_prism: Prism<ApiResponse, (String, HashMap<String, String>)> = Prism::new(
        |resp: &ApiResponse| match resp {
            ApiResponse::Success { data, metadata } => Some((data.clone(), metadata.clone())),
            _ => None,
        },
        |&(ref data, ref metadata): &(String, HashMap<String, String>)| ApiResponse::Success {
            data: data.clone(),
            metadata: metadata.clone(),
        },
    );

    let error_prism: Prism<ApiResponse, (u32, String)> = Prism::new(
        |resp: &ApiResponse| match resp {
            ApiResponse::Error { code, message } => Some((*code, message.clone())),
            _ => None,
        },
        |&(code, ref message): &(u32, String)| ApiResponse::Error {
            code,
            message: message.clone(),
        },
    );

    // Create sample API responses
    let mut metadata = HashMap::new();
    metadata.insert("version".to_string(), "1.0".to_string());
    metadata.insert("timestamp".to_string(), "2025-03-17T14:30:00Z".to_string());

    let success_response = ApiResponse::Success {
        data: "{\"user\":\"alice\",\"role\":\"admin\"}".to_string(),
        metadata: metadata.clone(),
    };

    let error_response = ApiResponse::Error {
        code: 404,
        message: "Resource not found".to_string(),
    };

    // Benchmark API response handling
    group.bench_function("api_response_preview_success", |b| {
        b.iter(|| {
            black_box(success_prism.preview(&success_response));
        });
    });

    group.bench_function("api_response_preview_error", |b| {
        b.iter(|| {
            black_box(error_prism.preview(&error_response));
        });
    });

    // ======== REAL-WORLD USE CASES ========

    // Use case 1: API response handling with transformation
    group.bench_function("use_case_api_response_handling", |b| {
        b.iter(|| {
            black_box({
                // Try to get success data, or return error message
                match success_prism.preview(&success_response) {
                    Some((data, _)) => {
                        // Process the data
                        format!("Success: {}", data)
                    }
                    None => {
                        // Check for error
                        match error_prism.preview(&success_response) {
                            Some((code, message)) => {
                                format!("Error {}: {}", code, message)
                            }
                            None => "Unknown response type".to_string(),
                        }
                    }
                }
            });
        });
    });

    // Create network packet prisms
    let data_packet_prism: Prism<NetworkPacket, (Vec<u8>, u32)> = Prism::new(
        |packet: &NetworkPacket| match packet {
            NetworkPacket::Data {
                payload,
                sequence_number,
            } => Some((payload.clone(), *sequence_number)),
            _ => None,
        },
        |&(ref payload, sequence_number): &(Vec<u8>, u32)| NetworkPacket::Data {
            payload: payload.clone(),
            sequence_number,
        },
    );

    let ack_packet_prism: Prism<NetworkPacket, u32> = Prism::new(
        |packet: &NetworkPacket| match packet {
            NetworkPacket::Ack { sequence_number } => Some(*sequence_number),
            _ => None,
        },
        |&sequence_number: &u32| NetworkPacket::Ack { sequence_number },
    );

    // Create sample packets
    let data_packet = NetworkPacket::Data {
        payload: vec![1, 2, 3, 4, 5],
        sequence_number: 42,
    };

    let ack_packet = NetworkPacket::Ack {
        sequence_number: 42,
    };

    // Use case 2: Network packet processing
    group.bench_function("use_case_network_packet_processing", |b| {
        b.iter(|| {
            black_box({
                // Process a sequence of packets
                let packets = vec![
                    data_packet.clone(),
                    ack_packet.clone(),
                    NetworkPacket::SyncRequest,
                ];

                let mut processed_data: Vec<u8> = Vec::new();
                let mut acked_sequences: Vec<u32> = Vec::new();

                for packet in &packets {
                    // Try to extract data payload
                    if let Some((payload, _sequence_number)) = data_packet_prism.preview(packet) {
                        processed_data.extend_from_slice(&payload);
                    }

                    // Check for ACKs
                    if let Some(sequence_number) = ack_packet_prism.preview(packet) {
                        acked_sequences.push(sequence_number);
                    }
                }

                (processed_data, acked_sequences)
            });
        });
    });

    // Use case 3: User authentication with prisms and Maybe
    group.bench_function("use_case_authentication", |b| {
        let users: HashMap<String, UserStatus> = {
            let mut map = HashMap::new();
            map.insert("alice".to_string(), logged_in_user.clone());
            map.insert("bob".to_string(), UserStatus::LoggedOut);
            map.insert("charlie".to_string(), suspended_user.clone());
            map
        };

        b.iter(|| {
            black_box({
                let username = "alice";
                // Try to find the user
                let maybe_status = Maybe::from_option(users.get(username).cloned());

                // Use the prism with Maybe
                maybe_status
                    .bind(|status: &UserStatus| {
                        // Try to get logged in data
                        Maybe::from_option(logged_in_prism.preview(status))
                    })
                    .map_or(
                        "User not found or not logged in".to_string(),
                        |(username, session_id)| {
                            format!("User {} is logged in with session {}", username, session_id)
                        },
                    )
            });
        });
    });

    // Use case 4: Composing prisms with other operations
    group.bench_function("use_case_prism_composition", |b| {
        b.iter(|| {
            black_box({
                let shapes = vec![circle.clone(), rectangle.clone(), triangle.clone()];

                // Filter and transform shapes
                let transformed: Vec<Shape> = shapes
                    .iter()
                    .filter_map(|shape| {
                        // Try different prisms
                        if let Some(radius) = circle_prism.preview(shape) {
                            // Double circle radius
                            Some(circle_prism.review(&(radius * 2)))
                        } else if let Some((width, height)) = rectangle_prism.preview(shape) {
                            // Swap dimensions
                            Some(rectangle_prism.review(&(height, width)))
                        } else if let Some((a, b, c)) = triangle_prism.preview(shape) {
                            // Scale triangle
                            Some(triangle_prism.review(&(a * 2, b * 2, c * 2)))
                        } else {
                            None
                        }
                    })
                    .collect();

                transformed
            });
        });
    });

    group.finish();
}
