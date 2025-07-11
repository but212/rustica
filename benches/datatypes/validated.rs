use criterion::Criterion;
use rustica::datatypes::validated::Validated;
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
}
