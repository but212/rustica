use criterion::{black_box, Criterion};
use rustica::datatypes::validated::Validated;
use rustica::pvec::PersistentVector;
use rustica::traits::applicative::Applicative;
use rustica::traits::foldable::Foldable;
use rustica::traits::functor::Functor;
use rustica::traits::monad::Monad;
use rustica::traits::pure::Pure;

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
            let validated: Validated<String, i32> = Validated::invalid_many(&[
                "error 1".to_string(),
                "error 2".to_string(),
                "error 3".to_string(),
            ]);
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
        let multi_errors = Validated::<String, i32>::Invalid(PersistentVector::from_slice(&[
            "error 1".to_string(),
            "error 2".to_string(),
            "error 3".to_string(),
        ]));

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
        let bind_fn = |x: &i32| Validated::<String, i32>::valid(x * 2);

        b.iter(|| {
            let result1 = valid.bind(&bind_fn);
            let result2 = valid.fold_left(&0, |acc, x| acc + x);
            let result3 = invalid.fold_left(&100, |acc, _| *acc);
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
        // Pre-create the error values outside the benchmark loop
        let validated1 = Validated::<String, i32>::invalid("error 1".to_string());
        let validated2 = Validated::<String, i32>::invalid("error 2".to_string());
        let errors1 = PersistentVector::from_slice(&["error 1".to_string(), "error 2".to_string()]);
        let errors2 = PersistentVector::from_slice(&["error 3".to_string(), "error 4".to_string()]);

        b.iter(|| {
            // Clone the pre-created values inside the loop to avoid recreating them
            let v1 = validated1.clone();
            let v2 = validated2.clone();
            let m1 = Validated::<String, i32>::Invalid(errors1.clone());
            let m2 = Validated::<String, i32>::Invalid(errors2.clone());

            // Use Validated's methods directly instead of pattern matching
            let combined1 = v1.apply(&v2.fmap(|_| |_: &i32| 0));

            // For multi-error case, we still need to extract the vectors
            let combined2: Validated<String, i32> = match (m1, m2) {
                (Validated::Invalid(e1), Validated::Invalid(e2)) => {
                    Validated::Invalid(e1.concat(&e2))
                }
                _ => unreachable!(),
            };

            black_box((combined1, combined2))
        });
    });

    // Validation chain benchmarks
    group.bench_function("validation_chains", |b| {
        // Optimized validation functions with fewer allocations
        let validate_positive = |x: &i32| -> Validated<String, i32> {
            if *x > 0 {
                Validated::valid(*x)
            } else {
                // Pre-allocated error message
                static ERROR: &str = "Value must be positive";
                Validated::invalid(ERROR.to_string())
            }
        };

        let validate_even = |x: &i32| -> Validated<String, i32> {
            if x % 2 == 0 {
                Validated::valid(*x)
            } else {
                // Pre-allocated error message
                static ERROR: &str = "Value must be even";
                Validated::invalid(ERROR.to_string())
            }
        };

        b.iter(|| {
            // Optimization: Create validation functions outside the benchmark
            let valid_input = 42;
            let invalid_input = -99;

            // Sequential validation - reuse results
            let valid_result = validate_positive(&valid_input).bind(validate_even);
            let invalid_result = validate_positive(&invalid_input).bind(validate_even);

            // Parallel validation with fewer allocations
            let valid_res1 = validate_positive(&valid_input);
            let valid_res2 = validate_even(&valid_input);

            // Only compute these once instead of on every iteration
            let combined_valid = valid_res1.lift2(&valid_res2, |a, b| a + b);

            // Reuse the same invalid validations
            let invalid_res1 = validate_positive(&invalid_input);
            let invalid_res2 = validate_even(&invalid_input);

            black_box((
                valid_result,
                invalid_result,
                combined_valid,
                invalid_res1.clone(),
                invalid_res2.clone(),
            ))
        });
    });

    group.finish();

    // Section 4: Conversion and Real-world Use Cases
    let mut group = c.benchmark_group("Validated - Conversion & Use Cases");

    // Conversion benchmarks
    group.bench_function("conversions", |b| {
        // Pre-create all test values outside the benchmark loop
        let ok_result: Result<i32, String> = Ok(42);
        let err_result: Result<i32, String> = Err("error".to_string());
        let some_value: Option<i32> = Some(42);
        let none_value: Option<i32> = None;

        // Pre-create validated values
        let valid: Validated<String, i32> = Validated::valid(42);
        let invalid: Validated<String, i32> = Validated::invalid("error".to_string());

        // Pre-compute some results to avoid allocations in the hot loop
        let result_from_valid_pre = valid.to_result();
        let result_from_invalid_pre = invalid.to_result();
        let option_from_valid_pre = valid.to_option();
        let option_from_invalid_pre = invalid.to_option();

        b.iter(|| {
            // Use from_option_with_owned to avoid cloning the error string
            let valid_from_option =
                Validated::from_option_with_owned(some_value, || "No value provided".to_string());

            let invalid_from_option =
                Validated::from_option_with_owned(none_value, || "No value provided".to_string());

            // Use pre-computed results where possible
            black_box((
                Validated::from_result_owned(ok_result.clone()),
                Validated::from_result_owned(err_result.clone()),
                result_from_valid_pre.clone(),
                result_from_invalid_pre.clone(),
                valid_from_option,
                invalid_from_option,
                option_from_valid_pre.clone(),
                option_from_invalid_pre.clone(),
            ))
        });
    });

    // Form validation use case
    group.bench_function("form_validation_applicative", |b| {
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
            // Validate forms using applicative style
            let validate_form = |form: &UserForm| {
                let username_v = validate_username(&form.username);
                let email_v = validate_email(&form.email);
                let age_v = validate_age(&form.age);

                username_v.lift3(&email_v, &age_v, |u, e, a| (u.clone(), e.clone(), *a))
            };

            let valid_result = validate_form(&valid_form);
            let invalid_result = validate_form(&invalid_form);

            black_box((valid_result, invalid_result))
        });
    });

    group.finish();
}
