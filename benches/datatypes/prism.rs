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

    // Create prisms for basic shapes
    let circle_prism = Prism::new(
        |s: &Shape| match s {
            Shape::Circle(r) => Some(*r),
            _ => None,
        },
        |r: &u32| Shape::Circle(*r),
    );

    let rectangle_prism = Prism::new(
        |s: &Shape| match s {
            Shape::Rectangle(w, h) => Some((*w, *h)),
            _ => None,
        },
        |&(w, h): &(u32, u32)| Shape::Rectangle(w, h),
    );

    let triangle_prism = Prism::new(
        |s: &Shape| match s {
            Shape::Triangle(a, b, c) => Some((*a, *b, *c)),
            _ => None,
        },
        |&(a, b, c): &(u32, u32, u32)| Shape::Triangle(a, b, c),
    );

    // Create sample shapes
    let circle = Shape::Circle(10);
    let rectangle = Shape::Rectangle(20, 30);
    let triangle = Shape::Triangle(3, 4, 5);

    // Basic operations
    group.bench_function("preview_success", |b| {
        b.iter(|| black_box(circle_prism.preview(&circle)));
    });

    group.bench_function("preview_failure", |b| {
        b.iter(|| black_box(circle_prism.preview(&rectangle)));
    });

    group.bench_function("review", |b| {
        b.iter(|| black_box(circle_prism.review(&15u32)));
    });

    // Create user status prisms
    let logged_in_prism = Prism::new(
        |status: &UserStatus| match status {
            UserStatus::LoggedIn {
                username,
                session_id,
            } => Some((username.clone(), session_id.clone())),
        },
        |(username, session_id): &(String, String)| UserStatus::LoggedIn {
            username: username.clone(),
            session_id: session_id.clone(),
        },
    );

    // Create API response prisms
    let success_prism = Prism::new(
        |resp: &ApiResponse| match resp {
            ApiResponse::Success { data, metadata } => Some((data.clone(), metadata.clone())),
            _ => None,
        },
        |(data, metadata): &(String, HashMap<String, String>)| ApiResponse::Success {
            data: data.clone(),
            metadata: metadata.clone(),
        },
    );

    let error_prism = Prism::new(
        |resp: &ApiResponse| match resp {
            ApiResponse::Error { code, message } => Some((*code, message.clone())),
            _ => None,
        },
        |&(code, ref message): &(u32, String)| ApiResponse::Error {
            code,
            message: message.clone(),
        },
    );

    // Create network packet prisms
    let data_packet_prism = Prism::new(
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

    let ack_packet_prism = Prism::new(
        |packet: &NetworkPacket| match packet {
            NetworkPacket::Ack { sequence_number } => Some(*sequence_number),
            _ => None,
        },
        |&sequence_number: &u32| NetworkPacket::Ack { sequence_number },
    );

    // Sample data for complex benchmarks
    let logged_in_user = UserStatus::LoggedIn {
        username: "alice".to_string(),
        session_id: "abc123".to_string(),
    };

    let mut metadata = HashMap::new();
    metadata.insert("version".to_string(), "1.0".to_string());
    metadata.insert("timestamp".to_string(), "2025-03-17T14:30:00Z".to_string());

    let success_response = ApiResponse::Success {
        data: "{\"user\":\"alice\",\"role\":\"admin\"}".to_string(),
        metadata: metadata.clone(),
    };

    let data_packet = NetworkPacket::Data {
        payload: vec![1, 2, 3, 4, 5],
        sequence_number: 42,
    };

    let ack_packet = NetworkPacket::Ack {
        sequence_number: 42,
    };

    // Combined operations benchmarks
    group.bench_function("modify_shape", |b| {
        b.iter(|| {
            let result = match circle_prism.preview(&circle) {
                Some(radius) => circle_prism.review(&(radius * 2)),
                None => circle.clone(),
            };
            black_box(result);
        });
    });

    group.bench_function("complex_data_handling", |b| {
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
                    if let Some((payload, _)) = data_packet_prism.preview(packet) {
                        processed_data.extend_from_slice(&payload);
                    }

                    if let Some(seq_num) = ack_packet_prism.preview(packet) {
                        acked_sequences.push(seq_num);
                    }
                }

                (processed_data, acked_sequences)
            });
        });
    });

    group.bench_function("maybe_with_prism", |b| {
        let users: HashMap<String, UserStatus> = {
            let mut map = HashMap::new();
            map.insert("alice".to_string(), logged_in_user.clone());
            map
        };

        b.iter(|| {
            black_box({
                Maybe::from_option(users.get("alice").cloned())
                    .bind(|status: &UserStatus| Maybe::from_option(logged_in_prism.preview(status)))
                    .fmap_or("Not found".to_string(), |(username, session_id)| {
                        format!("User {} with session {}", username, session_id)
                    })
            });
        });
    });

    group.bench_function("prism_composition", |b| {
        b.iter(|| {
            black_box({
                let shapes = [circle.clone(), rectangle.clone(), triangle.clone()];
                shapes
                    .iter()
                    .filter_map(|shape| {
                        if let Some(r) = circle_prism.preview(shape) {
                            Some(circle_prism.review(&(r * 2)))
                        } else if let Some((w, h)) = rectangle_prism.preview(shape) {
                            Some(rectangle_prism.review(&(h, w)))
                        } else if let Some((a, b, c)) = triangle_prism.preview(shape) {
                            Some(triangle_prism.review(&(a * 2, b * 2, c * 2)))
                        } else {
                            None
                        }
                    })
                    .collect::<Vec<Shape>>()
            });
        });
    });

    group.bench_function("api_response_handling", |b| {
        b.iter(|| {
            black_box({
                match success_prism.preview(&success_response) {
                    Some((data, _)) => format!("Success: {}", data),
                    None => match error_prism.preview(&success_response) {
                        Some((code, message)) => format!("Error {}: {}", code, message),
                        None => "Unknown response type".to_string(),
                    },
                }
            });
        });
    });

    group.finish();
}
