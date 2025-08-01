use criterion::{BenchmarkId, Criterion};
use rustica::datatypes::validated::Validated;
use std::collections::HashMap;
use std::hint::black_box;

pub fn validated_benchmarks(c: &mut Criterion) {
    // Basic operations
    c.bench_function("validated_create_valid", |b| {
        b.iter(|| black_box(Validated::<String, i32>::valid(42)));
    });

    c.bench_function("validated_create_invalid", |b| {
        b.iter(|| black_box(Validated::<String, i32>::invalid("error".to_string())));
    });

    c.bench_function("validated_is_valid", |b| {
        let valid = Validated::<String, i32>::valid(42);
        let invalid = Validated::<String, i32>::invalid("error".to_string());
        b.iter(|| {
            black_box(valid.is_valid());
            black_box(invalid.is_valid());
        });
    });

    c.bench_function("validated_unwrap_or", |b| {
        let valid = Validated::<String, i32>::valid(42);
        let invalid = Validated::<String, i32>::invalid("error".to_string());
        b.iter(|| {
            black_box(valid.unwrap_or(&0));
            black_box(invalid.unwrap_or(&0));
        });
    });

    // Error handling
    c.bench_function("validated_error_accumulation", |b| {
        b.iter(|| {
            let validated1 = Validated::<String, i32>::invalid("error 1".to_string());
            let validated2 = Validated::<String, i32>::invalid("error 2".to_string());
            let combined = validated1.combine_errors(&validated2);
            black_box(combined)
        });
    });

    // Practical validation
    c.bench_function("validated_form_validation", |b| {
        // Static error messages
        static USERNAME_ERROR: &str = "Username must be at least 3 characters";
        static EMAIL_ERROR: &str = "Email must contain @ symbol";

        // Validation functions
        let validate_username = |username: &str| -> Validated<String, String> {
            if username.len() >= 3 {
                Validated::valid(username.to_string())
            } else {
                Validated::invalid(USERNAME_ERROR.to_string())
            }
        };

        let validate_email = |email: &str| -> Validated<String, String> {
            if email.contains('@') {
                Validated::valid(email.to_string())
            } else {
                Validated::invalid(EMAIL_ERROR.to_string())
            }
        };

        // Test data
        let valid_username = "user";
        let valid_email = "user@example.com";
        let invalid_username = "ab";
        let invalid_email = "invalid-email";

        b.iter(|| {
            let username_validation = validate_username(valid_username);
            let email_validation = validate_email(valid_email);
            let invalid_username_validation = validate_username(invalid_username);
            let invalid_email_validation = validate_email(invalid_email);

            black_box((
                username_validation,
                email_validation,
                invalid_username_validation,
                invalid_email_validation,
            ))
        });
    });

    // Performance comparison with Result
    c.bench_function("validated_vs_result_single_error", |b| {
        b.iter(|| {
            // Validated approach
            let validated_result = Validated::<String, i32>::invalid("error".to_string());
            let _ = black_box(validated_result);

            // Result approach
            let result_result: Result<i32, String> = Err("error".to_string());
            let _ = black_box(result_result);
        });
    });

    // Error accumulation performance comparison
    c.bench_function("validated_vs_vec_error_accumulation", |b| {
        let errors = vec!["error1", "error2", "error3", "error4", "error5"];

        b.iter(|| {
            // Validated approach with SmallVec optimization
            let mut validated = Validated::<String, i32>::valid(0);
            for error in &errors {
                let error_validated = Validated::<String, i32>::invalid(error.to_string());
                validated = validated.combine_errors(&error_validated);
            }
            black_box(validated);

            // Manual Vec approach
            let mut error_vec: Vec<String> = Vec::new();
            for error in &errors {
                error_vec.push(error.to_string());
            }
            black_box(error_vec);
        });
    });

    // Memory usage comparison for different error counts
    for error_count in [1, 4, 8, 16, 32].iter() {
        c.bench_with_input(
            BenchmarkId::new("validated_memory_usage", error_count),
            error_count,
            |b, &count| {
                let errors: Vec<String> = (0..count).map(|i| format!("error_{}", i)).collect();

                b.iter(|| {
                    let validated = Validated::<String, i32>::invalid_many(errors.clone());
                    black_box(validated)
                });
            },
        );
    }

    // Functional operations performance
    c.bench_function("validated_functional_operations", |b| {
        let valid = Validated::<String, i32>::valid(42);
        let invalid = Validated::<String, i32>::invalid("error".to_string());

        b.iter(|| {
            // Map operations
            let mapped_valid = valid.fmap(|x| x * 2);
            let mapped_invalid = invalid.fmap(|x| x * 2);

            // Applicative operations
            let add_fn = Validated::<String, fn(i32) -> fn(i32) -> i32>::valid(|x| move |y| x + y);
            let applied = add_fn.apply(&valid).apply(&valid);

            black_box((mapped_valid, mapped_invalid, applied))
        });
    });

    // Real-world scenario: Complex form validation
    c.bench_function("validated_complex_form_validation", |b| {
        #[derive(Debug, Clone)]
        struct User {
            username: String,
            email: String,
            age: u32,
            password: String,
        }

        let validate_user =
            |username: &str, email: &str, age: u32, password: &str| -> Validated<String, User> {
                let username_validation = if username.len() >= 3 {
                    Validated::valid(username.to_string())
                } else {
                    Validated::invalid("Username must be at least 3 characters".to_string())
                };

                let email_validation = if email.contains('@') && email.contains('.') {
                    Validated::valid(email.to_string())
                } else {
                    Validated::invalid("Email must be valid".to_string())
                };

                let age_validation = if age >= 18 {
                    Validated::valid(age)
                } else {
                    Validated::invalid("Age must be at least 18".to_string())
                };

                let password_validation = if password.len() >= 8 {
                    Validated::valid(password.to_string())
                } else {
                    Validated::invalid("Password must be at least 8 characters".to_string())
                };

                // Combine all validations using applicative style
                username_validation.lift4(
                    email_validation,
                    age_validation,
                    password_validation,
                    |u, e, a, p| User {
                        username: u,
                        email: e,
                        age: a,
                        password: p,
                    },
                )
            };

        b.iter(|| {
            // Valid case
            let valid_user = validate_user("john_doe", "john@example.com", 25, "password123");

            // Invalid case (multiple errors)
            let invalid_user = validate_user("ab", "invalid-email", 16, "123");

            black_box((valid_user, invalid_user))
        });
    });
}
