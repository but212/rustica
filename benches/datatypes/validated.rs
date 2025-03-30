use criterion::{black_box, Criterion};
use rustica::datatypes::validated::Validated;
use rustica::traits::applicative::Applicative;
use rustica::traits::foldable::Foldable;
use rustica::traits::functor::Functor;
use rustica::traits::monad::Monad;
use rustica::traits::pure::Pure;
use smallvec::smallvec;

pub fn validated_benchmarks(c: &mut Criterion) {
    // Section 1: Basic Creation and Access Operations
    let mut group = c.benchmark_group("Validated - Basic Creation and Access");

    // Benchmark creating valid values
    group.bench_function("create_valid", |b| {
        b.iter(|| {
            let validated: Validated<String, i32> = Validated::valid(42);
            black_box(validated)
        });
    });

    // Benchmark creating single invalid value
    group.bench_function("create_single_invalid", |b| {
        b.iter(|| {
            let validated: Validated<String, i32> =
                Validated::invalid("validation error".to_string());
            black_box(validated)
        });
    });

    // Benchmark creating multi-invalid values
    group.bench_function("create_multi_invalid", |b| {
        b.iter(|| {
            let errors = smallvec![
                "error 1".to_string(),
                "error 2".to_string(),
                "error 3".to_string()
            ];
            let validated: Validated<String, i32> = Validated::MultiInvalid(errors);
            black_box(validated)
        });
    });

    // Check if a value is valid
    group.bench_function("is_valid", |b| {
        let valid: Validated<String, i32> = Validated::valid(42);
        let invalid: Validated<String, i32> = Validated::invalid("error".to_string());

        b.iter(|| {
            let result1 = black_box(valid.is_valid());
            let result2 = black_box(invalid.is_valid());
            (result1, result2)
        });
    });

    // Check if a value is invalid
    group.bench_function("is_invalid", |b| {
        let valid: Validated<String, i32> = Validated::valid(42);
        let invalid: Validated<String, i32> = Validated::invalid("error".to_string());

        b.iter(|| {
            let result1 = black_box(valid.is_invalid());
            let result2 = black_box(invalid.is_invalid());
            (result1, result2)
        });
    });

    // Get errors from validated values
    group.bench_function("errors", |b| {
        let single_error: Validated<String, i32> = Validated::invalid("error".to_string());
        let multi_errors = Validated::<String, i32>::MultiInvalid(smallvec![
            "error 1".to_string(),
            "error 2".to_string(),
            "error 3".to_string()
        ]);

        b.iter(|| {
            let errors1 = black_box(single_error.errors());
            let errors2 = black_box(multi_errors.errors());
            (errors1, errors2)
        });
    });

    // Unwrap valid values with default
    group.bench_function("unwrap_or", |b| {
        let valid: Validated<String, i32> = Validated::valid(42);
        let invalid: Validated<String, i32> = Validated::invalid("error".to_string());
        let default = 0;

        b.iter(|| {
            let result1 = black_box(valid.unwrap_or(&default));
            let result2 = black_box(invalid.unwrap_or(&default));
            (result1, result2)
        });
    });

    group.finish();

    // Section 2: Core Operations (Functor, Applicative, Monad, etc.)
    let mut group = c.benchmark_group("Validated - Core Operations");

    // Functor operations

    // Benchmark fmap with valid values
    group.bench_function("fmap_valid", |b| {
        let valid: Validated<String, i32> = Validated::valid(42);

        b.iter(|| {
            let result = valid.fmap(|x: &i32| x * 2);
            black_box(result)
        });
    });

    // Benchmark fmap with invalid values
    group.bench_function("fmap_invalid", |b| {
        let invalid: Validated<String, i32> = Validated::invalid("error".to_string());

        b.iter(|| {
            let result = invalid.fmap(|x: &i32| x * 2);
            black_box(result)
        });
    });

    // Benchmark map_valid
    group.bench_function("map_valid", |b| {
        let valid: Validated<String, i32> = Validated::valid(42);
        let invalid: Validated<String, i32> = Validated::invalid("error".to_string());

        b.iter(|| {
            let result1 = valid.fmap(&|x: &i32| x * 2);
            let result2 = invalid.fmap(&|x: &i32| x * 2);
            black_box((result1, result2))
        });
    });

    // Benchmark map_invalid
    group.bench_function("map_invalid", |b| {
        let valid: Validated<String, i32> = Validated::valid(42);
        let invalid: Validated<String, i32> = Validated::invalid("error".to_string());

        b.iter(|| {
            let result1 = valid.fmap_invalid(&|e: &String| format!("Wrapped: {}", e));
            let result2 = invalid.fmap_invalid(&|e: &String| format!("Wrapped: {}", e));
            black_box((result1, result2))
        });
    });

    // Pure operation (Applicative)
    group.bench_function("pure", |b| {
        b.iter(|| {
            let value = 42;
            let result: Validated<String, i32> = Validated::<String, i32>::pure(&value);
            black_box(result)
        });
    });

    // Apply operation (Applicative)
    group.bench_function("apply", |b| {
        let valid_fn: Validated<String, fn(&i32) -> i32> = Validated::valid(|x: &i32| x + 10);
        let valid_value: Validated<String, i32> = Validated::valid(42);
        let invalid_fn: Validated<String, fn(&i32) -> i32> =
            Validated::invalid("fn error".to_string());
        let invalid_value: Validated<String, i32> = Validated::invalid("value error".to_string());

        b.iter(|| {
            let result1 = valid_value.clone().apply(&valid_fn);
            let result2 = invalid_value.clone().apply(&valid_fn);
            let result3 = valid_value.clone().apply(&invalid_fn);
            black_box((result1, result2, result3))
        });
    });

    // Bind operation (Monad)
    group.bench_function("bind", |b| {
        let valid: Validated<String, i32> = Validated::valid(42);
        let invalid: Validated<String, i32> = Validated::invalid("error".to_string());

        b.iter(|| {
            let result1 = valid.bind(|x| Validated::<String, i32>::valid(x * 2));
            let result2 = invalid.bind(|x| Validated::<String, i32>::valid(x * 2));
            black_box((result1, result2))
        });
    });

    // Fold operation (Foldable)
    group.bench_function("fold", |b| {
        let valid: Validated<String, i32> = Validated::valid(42);
        let invalid: Validated<String, i32> = Validated::invalid("error".to_string());

        b.iter(|| {
            let result1 = valid.fold_left(&0, |acc, x| acc + x);
            let result2 = invalid.fold_left(&0, |acc, x| acc + x);
            black_box((result1, result2))
        });
    });

    // Lift operations
    group.bench_function("lift2", |b| {
        let valid1: Validated<String, i32> = Validated::valid(10);
        let valid2: Validated<String, i32> = Validated::valid(20);
        let invalid: Validated<String, i32> = Validated::invalid("error".to_string());

        b.iter(|| {
            let combined1 = valid1.lift2(&valid2, |x, y| x + y);
            let combined2 = valid1.lift2(&invalid, |x, y| x + y);
            black_box((combined1, combined2))
        });
    });

    group.finish();

    // Section 3: Error Handling and Accumulation
    let mut group = c.benchmark_group("Validated - Error Handling and Accumulation");

    // Benchmarking error accumulation with few errors (SmallVec optimization)
    group.bench_function("combine_few_errors", |b| {
        b.iter(|| {
            let validated1 = Validated::<String, i32>::SingleInvalid("error 1".to_string());
            let validated2 = Validated::<String, i32>::SingleInvalid("error 2".to_string());

            // Manual combination of errors to benchmark the core mechanism
            let combined = match (validated1, validated2) {
                (Validated::SingleInvalid(e1), Validated::SingleInvalid(e2)) => {
                    let mut errors: smallvec::SmallVec<[String; 4]> = smallvec![e1];
                    errors.push(e2);
                    Validated::MultiInvalid(errors)
                }
                (Validated::SingleInvalid(e1), Validated::MultiInvalid(e2)) => {
                    let mut errors: smallvec::SmallVec<[String; 4]> = e2;
                    errors.insert(0, e1);
                    Validated::MultiInvalid(errors)
                }
                (Validated::MultiInvalid(e1), Validated::SingleInvalid(e2)) => {
                    let mut errors: smallvec::SmallVec<[String; 4]> = e1;
                    errors.push(e2);
                    Validated::MultiInvalid(errors)
                }
                (Validated::MultiInvalid(e1), Validated::MultiInvalid(e2)) => {
                    let mut errors: smallvec::SmallVec<[String; 4]> = e1;
                    errors.extend(e2);
                    Validated::MultiInvalid(errors)
                }
                (v @ Validated::Valid(_), _) => v,
                (_, v @ Validated::Valid(_)) => v,
            };
            black_box(combined)
        });
    });

    // Benchmarking error accumulation with many errors (SmallVec vs Vec performance)
    group.bench_function("combine_many_errors", |b| {
        b.iter(|| {
            let errors1 = smallvec!["error 1".to_string(), "error 2".to_string()];
            let errors2 = smallvec![
                "error 3".to_string(),
                "error 4".to_string(),
                "error 5".to_string()
            ];

            let validated1 = Validated::<String, i32>::MultiInvalid(errors1);
            let validated2 = Validated::<String, i32>::MultiInvalid(errors2);

            // Combine the multi-invalid values
            let combined: Validated<String, i32> = match (validated1, validated2) {
                (Validated::MultiInvalid(e1), Validated::MultiInvalid(e2)) => {
                    let mut errors: smallvec::SmallVec<[String; 4]> = e1;
                    errors.extend(e2);
                    Validated::MultiInvalid(errors)
                }
                // Other cases omitted as we're testing specific case
                _ => unreachable!(),
            };
            black_box(combined)
        });
    });

    // Sequential validation with error accumulation
    group.bench_function("sequential_validation", |b| {
        // Setup validation functions
        let validate_positive = |x: &i32| -> Validated<String, i32> {
            if *x > 0 {
                Validated::valid(*x)
            } else {
                Validated::invalid("Value must be positive".to_string())
            }
        };

        let validate_even = |x: &i32| -> Validated<String, i32> {
            if x % 2 == 0 {
                Validated::valid(*x)
            } else {
                Validated::invalid("Value must be even".to_string())
            }
        };

        let validate_less_than_100 = |x: &i32| -> Validated<String, i32> {
            if *x < 100 {
                Validated::valid(*x)
            } else {
                Validated::invalid("Value must be less than 100".to_string())
            }
        };

        b.iter(|| {
            // Valid case
            let valid_input = 42;
            let valid_result = validate_positive(&valid_input)
                .bind(validate_even)
                .bind(validate_less_than_100);

            // Invalid case (multiple failures)
            let invalid_input = -99;
            let invalid_result = validate_positive(&invalid_input)
                .bind(validate_even)
                .bind(validate_less_than_100);

            black_box((valid_result, invalid_result))
        });
    });

    // Parallel validation with error accumulation
    group.bench_function("parallel_validation", |b| {
        // Setup validation functions that return Validated
        let validate_positive = |x: &i32| -> Validated<String, i32> {
            if *x > 0 {
                Validated::valid(*x)
            } else {
                Validated::invalid("Value must be positive".to_string())
            }
        };

        let validate_even = |x: &i32| -> Validated<String, i32> {
            if x % 2 == 0 {
                Validated::valid(*x)
            } else {
                Validated::invalid("Value must be even".to_string())
            }
        };

        let validate_less_than_100 = |x: &i32| -> Validated<String, i32> {
            if *x < 100 {
                Validated::valid(*x)
            } else {
                Validated::invalid("Value must be less than 100".to_string())
            }
        };

        b.iter(|| {
            // Valid input should pass all validations
            let valid_input = 42;

            // Invalid input should fail all validations
            let invalid_input = -99;

            // Perform validations on valid input
            let valid_res1 = validate_positive(&valid_input);
            let valid_res2 = validate_even(&valid_input);
            let valid_res3 = validate_less_than_100(&valid_input);

            // Combine validation results for valid input
            let mut errors: smallvec::SmallVec<[String; 4]> = smallvec![];

            match &valid_res1 {
                Validated::SingleInvalid(single_error) => {
                    errors.push(single_error.clone());
                }
                Validated::MultiInvalid(multi_errors) => {
                    errors.extend(multi_errors.iter().cloned());
                }
                _ => {}
            }

            match &valid_res2 {
                Validated::SingleInvalid(single_error) => {
                    errors.push(single_error.clone());
                }
                Validated::MultiInvalid(multi_errors) => {
                    errors.extend(multi_errors.iter().cloned());
                }
                _ => {}
            }

            match &valid_res3 {
                Validated::SingleInvalid(single_error) => {
                    errors.push(single_error.clone());
                }
                Validated::MultiInvalid(multi_errors) => {
                    errors.extend(multi_errors.iter().cloned());
                }
                _ => {}
            }

            let valid_combined = if errors.len() == 1 {
                Validated::<String, i32>::SingleInvalid(errors[0].clone())
            } else {
                Validated::<String, i32>::MultiInvalid(errors)
            };

            // Perform validations on invalid input
            let invalid_res1 = validate_positive(&invalid_input);
            let invalid_res2 = validate_even(&invalid_input);
            let invalid_res3 = validate_less_than_100(&invalid_input);

            // Collect all validation errors
            let mut errors: smallvec::SmallVec<[String; 4]> = smallvec![];

            match &invalid_res1 {
                Validated::SingleInvalid(single_error) => {
                    errors.push(single_error.clone());
                }
                Validated::MultiInvalid(multi_errors) => {
                    errors.extend(multi_errors.iter().cloned());
                }
                _ => {}
            }

            match &invalid_res2 {
                Validated::SingleInvalid(single_error) => {
                    errors.push(single_error.clone());
                }
                Validated::MultiInvalid(multi_errors) => {
                    errors.extend(multi_errors.iter().cloned());
                }
                _ => {}
            }

            match &invalid_res3 {
                Validated::SingleInvalid(single_error) => {
                    errors.push(single_error.clone());
                }
                Validated::MultiInvalid(multi_errors) => {
                    errors.extend(multi_errors.iter().cloned());
                }
                _ => {}
            }

            let invalid_combined = if errors.len() == 1 {
                Validated::<String, i32>::SingleInvalid(errors[0].clone())
            } else {
                Validated::<String, i32>::MultiInvalid(errors)
            };

            black_box((valid_combined, invalid_combined))
        });
    });

    // Test error accumulation with various data types
    group.bench_function("error_accumulation_data_types", |b| {
        b.iter(|| {
            // String errors
            let string_error1 = Validated::<String, i32>::invalid("String error 1".to_string());
            let string_error2 = Validated::<String, i32>::invalid("String error 2".to_string());

            // Using numeric errors
            let num_error1 = Validated::<i32, String>::invalid(1);
            let num_error2 = Validated::<i32, String>::invalid(2);

            // Combine string errors
            let mut errors: smallvec::SmallVec<[String; 4]> = smallvec![];

            match &string_error1 {
                Validated::SingleInvalid(single_error) => {
                    errors.push(single_error.clone());
                }
                Validated::MultiInvalid(multi_errors) => {
                    errors.extend(multi_errors.iter().cloned());
                }
                _ => {}
            }

            match &string_error2 {
                Validated::SingleInvalid(single_error) => {
                    errors.push(single_error.clone());
                }
                Validated::MultiInvalid(multi_errors) => {
                    errors.extend(multi_errors.iter().cloned());
                }
                _ => {}
            }

            let combined_strings = if errors.len() == 1 {
                Validated::<String, i32>::SingleInvalid(errors[0].clone())
            } else {
                Validated::<String, i32>::MultiInvalid(errors)
            };

            // Combine numeric errors
            let mut errors: smallvec::SmallVec<[i32; 4]> = smallvec![];

            match &num_error1 {
                Validated::SingleInvalid(single_error) => {
                    errors.push(single_error.clone());
                }
                Validated::MultiInvalid(multi_errors) => {
                    errors.extend(multi_errors.iter().cloned());
                }
                _ => {}
            }

            match &num_error2 {
                Validated::SingleInvalid(single_error) => {
                    errors.push(single_error.clone());
                }
                Validated::MultiInvalid(multi_errors) => {
                    errors.extend(multi_errors.iter().cloned());
                }
                _ => {}
            }

            let combined_nums = if errors.len() == 1 {
                Validated::<i32, String>::SingleInvalid(errors[0].clone())
            } else {
                Validated::<i32, String>::MultiInvalid(errors)
            };

            black_box((combined_strings, combined_nums))
        });
    });

    group.finish();

    // Section 4: Conversion Operations
    let mut group = c.benchmark_group("Validated - Conversion Operations");

    // Benchmark conversion from Result to Validated
    group.bench_function("from_result", |b| {
        let ok_result: Result<i32, String> = Ok(42);
        let err_result: Result<i32, String> = Err("error".to_string());

        b.iter(|| {
            let valid = Validated::<String, i32>::from_result(&ok_result);
            let invalid = Validated::<String, i32>::from_result(&err_result);
            black_box((valid, invalid))
        });
    });

    // Benchmark conversion from Validated to Result
    group.bench_function("to_result", |b| {
        let valid: Validated<String, i32> = Validated::valid(42);
        let single_invalid: Validated<String, i32> = Validated::invalid("error".to_string());
        let multi_invalid = Validated::<String, i32>::MultiInvalid(smallvec![
            "error 1".to_string(),
            "error 2".to_string()
        ]);

        b.iter(|| {
            let result1 = valid.to_result();
            let result2 = single_invalid.to_result();
            let result3 = multi_invalid.to_result();
            black_box((result1, result2, result3))
        });
    });

    // Benchmark conversion from Option to Validated
    group.bench_function("from_option", |b| {
        let some_value: Option<i32> = Some(42);
        let none_value: Option<i32> = None;
        let error_msg = "No value provided";

        b.iter(|| {
            let valid = Validated::<String, i32>::from_option(&some_value, &error_msg.to_string());
            let invalid =
                Validated::<String, i32>::from_option(&none_value, &error_msg.to_string());
            black_box((valid, invalid))
        });
    });

    // Benchmark conversion from Validated to Option
    group.bench_function("to_option", |b| {
        let valid: Validated<String, i32> = Validated::valid(42);
        let invalid: Validated<String, i32> = Validated::invalid("error".to_string());

        b.iter(|| {
            let some_result = valid.to_option();
            let none_result = invalid.to_option();
            black_box((some_result, none_result))
        });
    });

    // Benchmark converting between different error types
    group.bench_function("map_error_type", |b| {
        let invalid_str: Validated<String, i32> = Validated::invalid("error message".to_string());

        b.iter(|| {
            // Convert String errors to i32 errors
            let invalid_num = invalid_str.fmap_invalid(&|s: &String| s.len() as i32);
            black_box(invalid_num)
        });
    });

    // Benchmark converting between different valid types
    group.bench_function("map_valid_type", |b| {
        let valid_int: Validated<String, i32> = Validated::valid(42);

        b.iter(|| {
            // Convert i32 valid to String valid
            let valid_str = valid_int.fmap(&|i: &i32| i.to_string());
            black_box(valid_str)
        });
    });

    // Benchmark complex conversion chain
    group.bench_function("conversion_chain", |b| {
        // Start with a Result
        let result: Result<i32, String> = Ok(42);

        b.iter(|| {
            // Convert Result to Validated
            let validated = Validated::<String, i32>::from_result(&result);

            // Map the valid value
            let mapped = validated.fmap(&|i: &i32| i * 2);

            // Convert back to Result
            let final_result = mapped.to_result();

            black_box(final_result)
        });
    });

    // Benchmark conversion with validation
    group.bench_function("convert_with_validation", |b| {
        // A function that converts a string to an integer with validation
        let parse_int = |s: &String| -> Validated<String, i32> {
            match s.parse::<i32>() {
                Ok(i) => Validated::valid(i),
                Err(_) => Validated::invalid(format!("'{}' is not a valid integer", s)),
            }
        };

        let valid_str = "42".to_string();
        let invalid_str = "not_a_number".to_string();

        b.iter(|| {
            let valid_result = parse_int(&valid_str);
            let invalid_result = parse_int(&invalid_str);
            black_box((valid_result, invalid_result))
        });
    });

    group.finish();

    // Section 5: Real-world Use Cases
    let mut group = c.benchmark_group("Validated - Real-world Use Cases");

    // Form Validation Use Case
    group.bench_function("form_validation", |b| {
        #[derive(Clone)]
        #[allow(dead_code)]
        struct UserForm {
            username: String,
            email: String,
            age: i32,
        }

        // Individual field validators
        let validate_username = |username: &String| -> Validated<String, String> {
            if username.len() >= 3 {
                Validated::valid(username.clone())
            } else {
                Validated::invalid("Username must be at least 3 characters".to_string())
            }
        };

        let validate_email = |email: &String| -> Validated<String, String> {
            if email.contains('@') {
                Validated::valid(email.clone())
            } else {
                Validated::invalid("Email must contain @ symbol".to_string())
            }
        };

        let validate_age = |age: &i32| -> Validated<String, i32> {
            if *age >= 18 {
                Validated::valid(*age)
            } else {
                Validated::invalid("Age must be at least 18".to_string())
            }
        };

        // Valid form data
        let valid_form = UserForm {
            username: "validuser".to_string(),
            email: "valid@example.com".to_string(),
            age: 25,
        };

        // Invalid form data with multiple problems
        let invalid_form = UserForm {
            username: "ab".to_string(),
            email: "invalidemail".to_string(),
            age: 16,
        };

        b.iter(|| {
            // Validate valid form
            let valid_username = validate_username(&valid_form.username);
            let valid_email = validate_email(&valid_form.email);
            let valid_age = validate_age(&valid_form.age);

            // For valid data, all validations should pass
            let mut errors: smallvec::SmallVec<[String; 4]> = smallvec![];

            match &valid_username {
                Validated::SingleInvalid(single_error) => {
                    errors.push(single_error.clone());
                }
                Validated::MultiInvalid(multi_errors) => {
                    errors.extend(multi_errors.iter().cloned());
                }
                _ => {}
            }

            match &valid_email {
                Validated::SingleInvalid(single_error) => {
                    errors.push(single_error.clone());
                }
                Validated::MultiInvalid(multi_errors) => {
                    errors.extend(multi_errors.iter().cloned());
                }
                _ => {}
            }

            match &valid_age {
                Validated::SingleInvalid(single_error) => {
                    errors.push(single_error.clone());
                }
                Validated::MultiInvalid(multi_errors) => {
                    errors.extend(multi_errors.iter().cloned());
                }
                _ => {}
            }

            let valid_combined = if errors.len() == 1 {
                Validated::<String, UserForm>::SingleInvalid(errors[0].clone())
            } else {
                Validated::<String, UserForm>::MultiInvalid(errors)
            };

            // Validate invalid form
            let invalid_username = validate_username(&invalid_form.username);
            let invalid_email = validate_email(&invalid_form.email);
            let invalid_age = validate_age(&invalid_form.age);

            // For invalid data, collect all validation errors
            let mut errors: smallvec::SmallVec<[String; 4]> = smallvec![];

            match &invalid_username {
                Validated::SingleInvalid(single_error) => {
                    errors.push(single_error.clone());
                }
                Validated::MultiInvalid(multi_errors) => {
                    errors.extend(multi_errors.iter().cloned());
                }
                _ => {}
            }

            match &invalid_email {
                Validated::SingleInvalid(single_error) => {
                    errors.push(single_error.clone());
                }
                Validated::MultiInvalid(multi_errors) => {
                    errors.extend(multi_errors.iter().cloned());
                }
                _ => {}
            }

            match &invalid_age {
                Validated::SingleInvalid(single_error) => {
                    errors.push(single_error.clone());
                }
                Validated::MultiInvalid(multi_errors) => {
                    errors.extend(multi_errors.iter().cloned());
                }
                _ => {}
            }

            let invalid_combined = if errors.len() == 1 {
                Validated::<String, UserForm>::SingleInvalid(errors[0].clone())
            } else {
                Validated::<String, UserForm>::MultiInvalid(errors)
            };

            black_box((valid_combined, invalid_combined))
        });
    });

    // Data Validation Use Case
    group.bench_function("data_validation", |b| {
        // Suppose we're parsing and validating a configuration file
        #[derive(Clone)]
        #[allow(dead_code)]
        struct ServerConfig {
            host: String,
            port: u16,
            max_connections: u32,
            timeout_seconds: u32,
        }

        // Raw input data (strings)
        let raw_valid_data = [
            ("host", "localhost"),
            ("port", "8080"),
            ("max_connections", "1000"),
            ("timeout_seconds", "30"),
        ];

        let raw_invalid_data = [
            ("host", ""),               // Empty host
            ("port", "999999"),         // Port too large
            ("max_connections", "-5"),  // Negative value
            ("timeout_seconds", "abc"), // Not a number
        ];

        // Validation functions
        let validate_host = |host: &str| -> Validated<String, String> {
            if !host.is_empty() {
                Validated::valid(host.to_string())
            } else {
                Validated::invalid("Host cannot be empty".to_string())
            }
        };

        let validate_port = |port_str: &str| -> Validated<String, u16> {
            match port_str.parse::<u16>() {
                Ok(port) => Validated::valid(port),
                Err(_) => Validated::invalid(format!("Invalid port number: {}", port_str)),
            }
        };

        let validate_max_connections = |conn_str: &str| -> Validated<String, u32> {
            match conn_str.parse::<u32>() {
                Ok(conn) if conn > 0 => Validated::valid(conn),
                Ok(_) => Validated::invalid("Max connections must be greater than 0".to_string()),
                Err(_) => Validated::invalid(format!("Invalid max connections: {}", conn_str)),
            }
        };

        let validate_timeout = |timeout_str: &str| -> Validated<String, u32> {
            match timeout_str.parse::<u32>() {
                Ok(timeout) => Validated::valid(timeout),
                Err(_) => Validated::invalid(format!("Invalid timeout: {}", timeout_str)),
            }
        };

        b.iter(|| {
            // Process valid data
            let valid_host = validate_host(raw_valid_data[0].1);
            let valid_port = validate_port(raw_valid_data[1].1);
            let valid_max_conn = validate_max_connections(raw_valid_data[2].1);
            let valid_timeout = validate_timeout(raw_valid_data[3].1);

            // Combine valid results
            let mut errors: smallvec::SmallVec<[String; 4]> = smallvec![];

            match &valid_host {
                Validated::SingleInvalid(single_error) => {
                    errors.push(single_error.clone());
                }
                Validated::MultiInvalid(multi_errors) => {
                    errors.extend(multi_errors.iter().cloned());
                }
                _ => {}
            }

            match &valid_port {
                Validated::SingleInvalid(single_error) => {
                    errors.push(single_error.clone());
                }
                Validated::MultiInvalid(multi_errors) => {
                    errors.extend(multi_errors.iter().cloned());
                }
                _ => {}
            }

            match &valid_max_conn {
                Validated::SingleInvalid(single_error) => {
                    errors.push(single_error.clone());
                }
                Validated::MultiInvalid(multi_errors) => {
                    errors.extend(multi_errors.iter().cloned());
                }
                _ => {}
            }

            match &valid_timeout {
                Validated::SingleInvalid(single_error) => {
                    errors.push(single_error.clone());
                }
                Validated::MultiInvalid(multi_errors) => {
                    errors.extend(multi_errors.iter().cloned());
                }
                _ => {}
            }

            let valid_config = if errors.len() == 1 {
                Validated::<String, ServerConfig>::SingleInvalid(errors[0].clone())
            } else {
                Validated::<String, ServerConfig>::MultiInvalid(errors)
            };

            // Process invalid data
            let invalid_host = validate_host(raw_invalid_data[0].1);
            let invalid_port = validate_port(raw_invalid_data[1].1);
            let invalid_max_conn = validate_max_connections(raw_invalid_data[2].1);
            let invalid_timeout = validate_timeout(raw_invalid_data[3].1);

            // Collect all validation errors
            let mut errors: smallvec::SmallVec<[String; 4]> = smallvec![];

            match &invalid_host {
                Validated::SingleInvalid(single_error) => {
                    errors.push(single_error.clone());
                }
                Validated::MultiInvalid(multi_errors) => {
                    errors.extend(multi_errors.iter().cloned());
                }
                _ => {}
            }

            match &invalid_port {
                Validated::SingleInvalid(single_error) => {
                    errors.push(single_error.clone());
                }
                Validated::MultiInvalid(multi_errors) => {
                    errors.extend(multi_errors.iter().cloned());
                }
                _ => {}
            }

            match &invalid_max_conn {
                Validated::SingleInvalid(single_error) => {
                    errors.push(single_error.clone());
                }
                Validated::MultiInvalid(multi_errors) => {
                    errors.extend(multi_errors.iter().cloned());
                }
                _ => {}
            }

            match &invalid_timeout {
                Validated::SingleInvalid(single_error) => {
                    errors.push(single_error.clone());
                }
                Validated::MultiInvalid(multi_errors) => {
                    errors.extend(multi_errors.iter().cloned());
                }
                _ => {}
            }

            let invalid_config = if errors.len() == 1 {
                Validated::<String, ServerConfig>::SingleInvalid(errors[0].clone())
            } else {
                Validated::<String, ServerConfig>::MultiInvalid(errors)
            };

            black_box((valid_config, invalid_config))
        });
    });

    // API Response Validation
    group.bench_function("api_response_validation", |b| {
        // Simulate an API response structure
        #[derive(Clone)]
        struct ApiResponse {
            status: String,
            data: Option<String>,
            error_messages: Vec<String>,
        }

        // Validator function for API responses
        let validate_api_response = |response: &ApiResponse| -> Validated<String, String> {
            // Check status
            let status_validation = if response.status == "success" {
                Validated::valid(())
            } else {
                Validated::invalid(format!("Invalid status: {}", response.status))
            };

            // Check data is present for success status
            let data_validation = if response.status == "success" && response.data.is_none() {
                Validated::invalid("Data missing for successful response".to_string())
            } else {
                Validated::valid(())
            };

            // If success, should have no error messages
            let error_validation = if response.status == "success"
                && !response.error_messages.is_empty()
            {
                Validated::invalid("Success response should not contain error messages".to_string())
            } else {
                Validated::valid(())
            };

            // Collect all validation errors
            let mut errors: smallvec::SmallVec<[String; 4]> = smallvec![];

            match &status_validation {
                Validated::SingleInvalid(single_error) => {
                    errors.push(single_error.clone());
                }
                Validated::MultiInvalid(multi_errors) => {
                    errors.extend(multi_errors.iter().cloned());
                }
                _ => {}
            }

            match &data_validation {
                Validated::SingleInvalid(single_error) => {
                    errors.push(single_error.clone());
                }
                Validated::MultiInvalid(multi_errors) => {
                    errors.extend(multi_errors.iter().cloned());
                }
                _ => {}
            }

            match &error_validation {
                Validated::SingleInvalid(single_error) => {
                    errors.push(single_error.clone());
                }
                Validated::MultiInvalid(multi_errors) => {
                    errors.extend(multi_errors.iter().cloned());
                }
                _ => {}
            }

            // Return validation result
            if errors.is_empty() {
                Validated::valid(response.data.clone().unwrap_or_default())
            } else if errors.len() == 1 {
                Validated::SingleInvalid(errors[0].clone())
            } else {
                Validated::MultiInvalid(errors)
            }
        };

        // Valid API response
        let valid_response = ApiResponse {
            status: "success".to_string(),
            data: Some("Response data".to_string()),
            error_messages: vec![],
        };

        // Invalid API response with multiple problems
        let invalid_response = ApiResponse {
            status: "partial_success".to_string(),
            data: None,
            error_messages: vec!["Warning: partial data".to_string()],
        };

        b.iter(|| {
            let valid_result = validate_api_response(&valid_response);
            let invalid_result = validate_api_response(&invalid_response);
            black_box((valid_result, invalid_result))
        });
    });

    // Business Rule Validation
    group.bench_function("business_rule_validation", |b| {
        // A financial transaction with business rules
        #[derive(Clone)]
        struct Transaction {
            amount: f64,
            account_balance: f64,
            daily_limit: f64,
            daily_spent: f64,
            is_flagged: bool,
        }

        // Business rules to validate a transaction
        let validate_positive_amount = |tx: &Transaction| -> Validated<String, ()> {
            if tx.amount > 0.0 {
                Validated::valid(())
            } else {
                Validated::invalid("Transaction amount must be positive".to_string())
            }
        };

        let validate_sufficient_funds = |tx: &Transaction| -> Validated<String, ()> {
            if tx.account_balance >= tx.amount {
                Validated::valid(())
            } else {
                Validated::invalid("Insufficient funds".to_string())
            }
        };

        let validate_daily_limit = |tx: &Transaction| -> Validated<String, ()> {
            if tx.daily_spent + tx.amount <= tx.daily_limit {
                Validated::valid(())
            } else {
                Validated::invalid("Daily spending limit exceeded".to_string())
            }
        };

        let validate_not_flagged = |tx: &Transaction| -> Validated<String, ()> {
            if !tx.is_flagged {
                Validated::valid(())
            } else {
                Validated::invalid("Account is flagged for suspicious activity".to_string())
            }
        };

        // Valid transaction
        let valid_tx = Transaction {
            amount: 100.0,
            account_balance: 1000.0,
            daily_limit: 500.0,
            daily_spent: 200.0,
            is_flagged: false,
        };

        // Invalid transaction that violates multiple rules
        let invalid_tx = Transaction {
            amount: 400.0,
            account_balance: 300.0,
            daily_limit: 500.0,
            daily_spent: 300.0,
            is_flagged: true,
        };

        b.iter(|| {
            // Validate valid transaction
            let valid_amount = validate_positive_amount(&valid_tx);
            let valid_funds = validate_sufficient_funds(&valid_tx);
            let valid_limit = validate_daily_limit(&valid_tx);
            let valid_flag = validate_not_flagged(&valid_tx);

            // Combine validations for valid transaction
            let mut errors: smallvec::SmallVec<[String; 4]> = smallvec![];

            match &valid_amount {
                Validated::SingleInvalid(single_error) => {
                    errors.push(single_error.clone());
                }
                Validated::MultiInvalid(multi_errors) => {
                    errors.extend(multi_errors.iter().cloned());
                }
                _ => {}
            }

            match &valid_funds {
                Validated::SingleInvalid(single_error) => {
                    errors.push(single_error.clone());
                }
                Validated::MultiInvalid(multi_errors) => {
                    errors.extend(multi_errors.iter().cloned());
                }
                _ => {}
            }

            match &valid_limit {
                Validated::SingleInvalid(single_error) => {
                    errors.push(single_error.clone());
                }
                Validated::MultiInvalid(multi_errors) => {
                    errors.extend(multi_errors.iter().cloned());
                }
                _ => {}
            }

            match &valid_flag {
                Validated::SingleInvalid(single_error) => {
                    errors.push(single_error.clone());
                }
                Validated::MultiInvalid(multi_errors) => {
                    errors.extend(multi_errors.iter().cloned());
                }
                _ => {}
            }

            let valid_result = if errors.len() == 1 {
                Validated::<String, Transaction>::SingleInvalid(errors[0].clone())
            } else {
                Validated::<String, Transaction>::MultiInvalid(errors)
            };

            // Validate invalid transaction
            let invalid_amount = validate_positive_amount(&invalid_tx);
            let invalid_funds = validate_sufficient_funds(&invalid_tx);
            let invalid_limit = validate_daily_limit(&invalid_tx);
            let invalid_flag = validate_not_flagged(&invalid_tx);

            // Collect all validation errors
            let mut errors: smallvec::SmallVec<[String; 4]> = smallvec![];

            match &invalid_amount {
                Validated::SingleInvalid(single_error) => {
                    errors.push(single_error.clone());
                }
                Validated::MultiInvalid(multi_errors) => {
                    errors.extend(multi_errors.iter().cloned());
                }
                _ => {}
            }

            match &invalid_funds {
                Validated::SingleInvalid(single_error) => {
                    errors.push(single_error.clone());
                }
                Validated::MultiInvalid(multi_errors) => {
                    errors.extend(multi_errors.iter().cloned());
                }
                _ => {}
            }

            match &invalid_limit {
                Validated::SingleInvalid(single_error) => {
                    errors.push(single_error.clone());
                }
                Validated::MultiInvalid(multi_errors) => {
                    errors.extend(multi_errors.iter().cloned());
                }
                _ => {}
            }

            match &invalid_flag {
                Validated::SingleInvalid(single_error) => {
                    errors.push(single_error.clone());
                }
                Validated::MultiInvalid(multi_errors) => {
                    errors.extend(multi_errors.iter().cloned());
                }
                _ => {}
            }

            let invalid_result = if errors.len() == 1 {
                Validated::<String, Transaction>::SingleInvalid(errors[0].clone())
            } else {
                Validated::<String, Transaction>::MultiInvalid(errors)
            };

            black_box((valid_result, invalid_result))
        });
    });

    group.finish();
}
