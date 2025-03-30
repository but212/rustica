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
    let mut group = c.benchmark_group("Validated - Basic Operations");

    // Creation benchmarks
    group.bench_function("create_valid", |b| {
        b.iter(|| {
            let validated: Validated<String, i32> = Validated::valid(42);
            black_box(validated)
        });
    });

    group.bench_function("create_invalid", |b| {
        b.iter(|| {
            let validated: Validated<String, i32> =
                Validated::invalid("validation error".to_string());
            black_box(validated)
        });
    });

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

    // Access benchmarks
    group.bench_function("is_valid_invalid", |b| {
        let valid: Validated<String, i32> = Validated::valid(42);
        let invalid: Validated<String, i32> = Validated::invalid("error".to_string());

        b.iter(|| {
            let result1 = black_box(valid.is_valid());
            let result2 = black_box(invalid.is_invalid());
            (result1, result2)
        });
    });

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
    group.bench_function("fmap", |b| {
        let valid: Validated<String, i32> = Validated::valid(42);
        let invalid: Validated<String, i32> = Validated::invalid("error".to_string());

        b.iter(|| {
            let result1 = valid.fmap(|x: &i32| x * 2);
            let result2 = invalid.fmap(|x: &i32| x * 2);
            black_box((result1, result2))
        });
    });

    // Applicative operations
    group.bench_function("pure_apply", |b| {
        let valid_fn: Validated<String, fn(&i32) -> i32> = Validated::valid(|x: &i32| x + 10);
        let valid_value: Validated<String, i32> = Validated::valid(42);
        let invalid_value: Validated<String, i32> = Validated::invalid("value error".to_string());

        b.iter(|| {
            let result1 = Validated::<String, i32>::pure(&42);
            let result2 = valid_value.clone().apply(&valid_fn);
            let result3 = invalid_value.clone().apply(&valid_fn);
            black_box((result1, result2, result3))
        });
    });

    // Monad and Foldable operations
    group.bench_function("bind_fold", |b| {
        let valid: Validated<String, i32> = Validated::valid(42);
        let invalid: Validated<String, i32> = Validated::invalid("error".to_string());

        b.iter(|| {
            let result1 = valid.bind(|x| Validated::<String, i32>::valid(x * 2));
            let result2 = valid.fold_left(&0, |acc, x| acc + x);
            let result3 = invalid.fold_left(&0, |acc, x| acc + x);
            black_box((result1, result2, result3))
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
    let mut group = c.benchmark_group("Validated - Error Handling");

    // Error accumulation benchmarks
    group.bench_function("error_accumulation", |b| {
        b.iter(|| {
            let validated1 = Validated::<String, i32>::SingleInvalid("error 1".to_string());
            let validated2 = Validated::<String, i32>::SingleInvalid("error 2".to_string());
            let errors1 = smallvec!["error 1".to_string(), "error 2".to_string()];
            let errors2 = smallvec!["error 3".to_string(), "error 4".to_string()];
            let multi1 = Validated::<String, i32>::MultiInvalid(errors1);
            let multi2 = Validated::<String, i32>::MultiInvalid(errors2);

            // Test different error combination scenarios
            let combined1: Validated<String, i32> = match (validated1, validated2) {
                (Validated::SingleInvalid(e1), Validated::SingleInvalid(e2)) => {
                    let mut errors = smallvec![e1];
                    errors.push(e2);
                    Validated::MultiInvalid(errors)
                }
                _ => unreachable!(),
            };

            let combined2: Validated<String, i32> = match (multi1, multi2) {
                (Validated::MultiInvalid(e1), Validated::MultiInvalid(e2)) => {
                    let mut errors = e1;
                    errors.extend(e2);
                    Validated::MultiInvalid(errors)
                }
                _ => unreachable!(),
            };

            black_box((combined1, combined2))
        });
    });

    // Validation chain benchmarks
    group.bench_function("validation_chains", |b| {
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

        b.iter(|| {
            // Sequential validation
            let valid_input = 42;
            let invalid_input = -99;

            let valid_result = validate_positive(&valid_input).bind(validate_even);
            let invalid_result = validate_positive(&invalid_input).bind(validate_even);

            // Parallel validation
            let valid_res1 = validate_positive(&valid_input);
            let valid_res2 = validate_even(&valid_input);
            let invalid_res1 = validate_positive(&invalid_input);
            let invalid_res2 = validate_even(&invalid_input);

            black_box((
                valid_result,
                invalid_result,
                valid_res1,
                valid_res2,
                invalid_res1,
                invalid_res2,
            ))
        });
    });

    group.finish();

    // Section 4: Conversion and Real-world Use Cases
    let mut group = c.benchmark_group("Validated - Conversion & Use Cases");

    // Conversion benchmarks
    group.bench_function("conversions", |b| {
        let ok_result: Result<i32, String> = Ok(42);
        let err_result: Result<i32, String> = Err("error".to_string());
        let some_value: Option<i32> = Some(42);
        let none_value: Option<i32> = None;
        let error_msg = "No value provided";

        let valid: Validated<String, i32> = Validated::valid(42);
        let invalid: Validated<String, i32> = Validated::invalid("error".to_string());

        b.iter(|| {
            // Result conversions
            let valid_from_result = Validated::<String, i32>::from_result(&ok_result);
            let invalid_from_result = Validated::<String, i32>::from_result(&err_result);
            let result_from_valid = valid.to_result();
            let result_from_invalid = invalid.to_result();

            // Option conversions
            let valid_from_option =
                Validated::<String, i32>::from_option(&some_value, &error_msg.to_string());
            let invalid_from_option =
                Validated::<String, i32>::from_option(&none_value, &error_msg.to_string());
            let option_from_valid = valid.to_option();
            let option_from_invalid = invalid.to_option();

            black_box((
                valid_from_result,
                invalid_from_result,
                result_from_valid,
                result_from_invalid,
                valid_from_option,
                invalid_from_option,
                option_from_valid,
                option_from_invalid,
            ))
        });
    });

    // Form validation use case
    group.bench_function("form_validation", |b| {
        #[derive(Clone)]
        struct UserForm {
            username: String,
            email: String,
            age: i32,
        }

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

        // Valid and invalid form data
        let valid_form = UserForm {
            username: "validuser".to_string(),
            email: "valid@example.com".to_string(),
            age: 25,
        };

        let invalid_form = UserForm {
            username: "ab".to_string(),
            email: "invalidemail".to_string(),
            age: 16,
        };

        b.iter(|| {
            // Validate both forms
            let valid_results = (
                validate_username(&valid_form.username),
                validate_email(&valid_form.email),
                validate_age(&valid_form.age),
            );

            let invalid_results = (
                validate_username(&invalid_form.username),
                validate_email(&invalid_form.email),
                validate_age(&invalid_form.age),
            );

            black_box((valid_results, invalid_results))
        });
    });

    group.finish();
}
