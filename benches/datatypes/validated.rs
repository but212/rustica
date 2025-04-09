use criterion::{black_box, Criterion};
use rustica::datatypes::validated::Validated;
use rustica::datatypes::wrapper::memoize::MemoizeFn;
use rustica::traits::applicative::Applicative;
use rustica::traits::monad::Monad;

pub fn validated_benchmarks(c: &mut Criterion) {
    // Section 1: Basic Creation and Access Operations
    let mut group = c.benchmark_group("Validated - Basic Operations");

    // Creation benchmarks
    group.bench_function("create_valid", |b| {
        b.iter(|| black_box(Validated::<String, i32>::valid(42)));
    });

    group.bench_function("create_invalid", |b| {
        b.iter(|| black_box(Validated::<String, i32>::invalid("error".to_string())));
    });

    group.bench_function("create_multi_invalid", |b| {
        b.iter(|| {
            black_box(Validated::<String, i32>::invalid_vec(vec![
                "error1".to_string(),
                "error2".to_string(),
            ]))
        });
    });

    // Access benchmarks
    group.bench_function("is_valid_on_valid", |b| {
        let valid = Validated::<String, i32>::valid(42);
        b.iter(|| black_box(valid.is_valid()));
    });

    group.bench_function("errors", |b| {
        let invalid =
            Validated::<String, i32>::invalid_vec(vec!["error1".to_string(), "error2".to_string()]);
        b.iter(|| black_box(invalid.errors()));
    });

    group.bench_function("unwrap_or", |b| {
        let valid = Validated::<String, i32>::valid(42);
        let invalid = Validated::<String, i32>::invalid("error".to_string());
        b.iter(|| {
            black_box(valid.unwrap_or(&0));
            black_box(invalid.unwrap_or(&0));
        });
    });

    group.finish();

    // Section 2: Core Operations (Functor, Applicative, Monad, etc.)
    let mut group = c.benchmark_group("Validated - Core Operations");

    // Functor operations
    group.bench_function("fmap", |b| {
        use rustica::traits::functor::Functor;

        b.iter(|| {
            black_box(Validated::<String, i32>::valid(42).fmap(|x| x * 2));
            black_box(Validated::<String, i32>::invalid("error".to_string()).fmap(|x| x * 2));
        });
    });

    // Applicative operations
    group.bench_function("pure_apply", |b| {
        use rustica::traits::applicative::Applicative;
        use rustica::traits::pure::Pure;

        let valid_fn = Validated::<String, fn(&i32) -> i32>::valid(|x: &i32| x + 10);
        let valid_value = Validated::<String, i32>::valid(42);
        let invalid_value = Validated::<String, i32>::invalid("value error".to_string());

        b.iter(|| {
            black_box(Validated::<String, i32>::pure(&42));
            black_box(valid_value.apply(&valid_fn));
            black_box(invalid_value.apply(&valid_fn));
        });
    });

    // Monad and Foldable operations
    group.bench_function("bind_fold", |b| {
        use rustica::traits::foldable::Foldable;
        use rustica::traits::monad::Monad;

        let valid = Validated::<String, i32>::valid(42);
        let invalid = Validated::<String, i32>::invalid("error".to_string());

        b.iter(|| {
            black_box((
                valid.bind(|x| Validated::<String, i32>::valid(x * 2)),
                valid.fold_left(&0, |acc, x| acc + x),
                invalid.fold_left(&0, |acc, _| *acc),
            ))
        });
    });

    // Lift operations
    group.bench_function("lift2", |b| {
        let valid1: Validated<String, i32> = Validated::valid(10);
        let valid2: Validated<String, i32> = Validated::valid(20);
        let invalid: Validated<String, i32> = Validated::invalid("error".to_string());

        b.iter(|| {
            black_box(valid1.lift2(&valid2, |x, y| x + y));
            black_box(valid1.lift2(&invalid, |x, y| x + y));
        });
    });

    group.finish();

    // Section 3: Error Handling and Accumulation
    let mut group = c.benchmark_group("Validated - Error Handling");

    // Error accumulation benchmarks
    group.bench_function("error_accumulation", |b| {
        b.iter(|| {
            let validated1 = Validated::<String, i32>::invalid("error 1".to_string());
            let validated2 = Validated::<String, i32>::invalid("error 2".to_string());

            let multi1 = Validated::<String, i32>::invalid_many([
                "error 1".to_string(),
                "error 2".to_string(),
            ]);
            let multi2 = Validated::<String, i32>::invalid_many([
                "error 3".to_string(),
                "error 4".to_string(),
            ]);

            // Test different error combination scenarios
            let combined1 = validated1.combine_errors(&validated2);
            let combined2 = multi1.combine_errors(&multi2);

            black_box((combined1, combined2))
        });
    });

    // Validation chain benchmarks
    group.bench_function("validation_chains", |b| {
        // Static error messages to avoid repeated allocations
        static POS_ERROR: &str = "Value must be positive";
        static EVEN_ERROR: &str = "Value must be even";

        // Pre-computed validation functions
        let validate_positive = |x: &i32| -> Validated<String, i32> {
            if *x > 0 {
                Validated::valid(*x)
            } else {
                Validated::invalid(POS_ERROR.to_string())
            }
        };

        let validate_even = |x: &i32| -> Validated<String, i32> {
            if x % 2 == 0 {
                Validated::valid(*x)
            } else {
                Validated::invalid(EVEN_ERROR.to_string())
            }
        };

        // Pre-compute validation results outside benchmark loop
        let valid_input = 42;
        let invalid_input = -99;

        let valid_res1 = validate_positive(&valid_input);
        let valid_res2 = validate_even(&valid_input);
        let invalid_res1 = validate_positive(&invalid_input);
        let invalid_res2 = validate_even(&invalid_input);

        b.iter(|| {
            // Reuse pre-computed validations
            let valid_result = valid_res1.bind(|x| validate_even(x));
            let invalid_result = invalid_res1.clone().bind(|x| validate_even(x));
            let combined_valid = valid_res1.lift2(&valid_res2, |a, b| a + b);

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

        // Static error message to avoid allocations
        static ERROR_MSG: &str = "No value provided";

        // Pre-create validated values
        let valid: Validated<String, i32> = Validated::valid(42);
        let invalid: Validated<String, i32> = Validated::invalid(ERROR_MSG.to_string());

        // Pre-compute conversions to avoid allocations in the benchmark loop
        let valid_from_option =
            Validated::from_option_with_owned(some_value, || ERROR_MSG.to_string());
        let invalid_from_option =
            Validated::from_option_with_owned(none_value, || ERROR_MSG.to_string());
        let valid_from_result = Validated::from_result_owned(ok_result.clone());
        let invalid_from_result = Validated::from_result_owned(err_result.clone());
        let result_from_valid = valid.to_result();
        let result_from_invalid = invalid.to_result();
        let option_from_valid = valid.to_option();
        let option_from_invalid = invalid.to_option();

        b.iter(|| {
            black_box((
                valid_from_result.clone(),
                invalid_from_result.clone(),
                result_from_valid.clone(),
                result_from_invalid.clone(),
                valid_from_option.clone(),
                invalid_from_option.clone(),
                option_from_valid,
                option_from_invalid,
            ))
        });
    });

    // Form validation use case
    group.bench_function("form_validation_applicative", |b| {
        #[derive(PartialEq, Eq, Hash, Clone)]
        struct UserForm {
            username: String,
            email: String,
            age: i32,
        }

        // Static error messages to avoid allocations
        static USERNAME_ERROR: &str = "Username must be at least 3 characters";
        static EMAIL_ERROR: &str = "Email must contain @ symbol";
        static AGE_ERROR: &str = "Age must be at least 18";

        // Create memoized validation functions
        let validate_username = MemoizeFn::new(|username: String| -> Validated<String, String> {
            if username.len() >= 3 {
                Validated::valid(username)
            } else {
                Validated::invalid(USERNAME_ERROR.to_string())
            }
        });

        let validate_email = MemoizeFn::new(|email: String| -> Validated<String, String> {
            if email.contains('@') {
                Validated::valid(email)
            } else {
                Validated::invalid(EMAIL_ERROR.to_string())
            }
        });

        let validate_age = MemoizeFn::new(|age: i32| -> Validated<String, i32> {
            if age >= 18 {
                Validated::valid(age)
            } else {
                Validated::invalid(AGE_ERROR.to_string())
            }
        });

        // Create form data outside benchmark loop
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

        // Memoized form validation function
        let validate_form = MemoizeFn::new(move |form: UserForm| {
            let username_v = validate_username.clone().call(form.username);
            let email_v = validate_email.clone().call(form.email);
            let age_v = validate_age.clone().call(form.age);

            username_v.lift3(&email_v, &age_v, |u, e, a| (u.clone(), e.clone(), *a))
        });

        // Pre-compute results to avoid repeated work
        let valid_result = validate_form.clone().call(valid_form.clone());
        let invalid_result = validate_form.call(invalid_form.clone());

        b.iter(|| black_box((valid_result.clone(), invalid_result.clone())));
    });

    group.finish();
}
