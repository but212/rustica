use criterion::{BenchmarkId, Criterion};
use rustica::datatypes::validated::Validated;
use rustica::traits::applicative::Applicative;
use rustica::traits::functor::Functor;
use rustica::traits::pure::Pure;
use std::hint::black_box;

// Helper functions for generating test data
fn gen_validated_vec(len: usize, error_rate: usize) -> Vec<Validated<String, i32>> {
    (0..len)
        .map(|i| {
            if (i % 100) < error_rate {
                Validated::invalid(format!("error_{}", i))
            } else {
                Validated::valid(i as i32)
            }
        })
        .collect()
}

pub fn validated_benchmarks(c: &mut Criterion) {
    let mut group = c.benchmark_group("Validated");

    group.bench_function("creation", |b| {
        b.iter(|| {
            black_box(Validated::<String, i32>::valid(42));
            black_box(Validated::<String, i32>::invalid("error".to_string()));
        });
    });

    group.bench_function("functor_ops", |b| {
        let valid = Validated::<String, i32>::valid(42);
        let invalid = Validated::<String, i32>::invalid("error".to_string());
        b.iter(|| {
            black_box(valid.fmap(|x: &i32| x * 2));
            black_box(invalid.fmap(|x: &i32| x * 2));
        });
    });

    group.bench_function("applicative_ops", |b| {
        let valid = Validated::<String, i32>::valid(42);
        let invalid = Validated::<String, i32>::invalid("error".to_string());
        let func = Validated::<String, fn(&i32) -> i32>::valid(|x: &i32| x + 1);
        b.iter(|| {
            black_box(Validated::<String, i32>::pure(&42));
            black_box(func.apply(&valid));
            black_box(Validated::<String, i32>::lift2(
                |x, y| x + y,
                &valid,
                &invalid,
            ));
        });
    });

    group.bench_function("error_accumulation", |b| {
        let invalid1 = Validated::<String, i32>::invalid("error 1".to_string());
        let invalid2 = Validated::<String, i32>::invalid("error 2".to_string());
        b.iter(|| {
            black_box(invalid1.combine_errors(&invalid2));
        });
    });

    // Parametric benchmarks for different error rates
    for error_rate in [10, 50, 90].iter() {
        group.bench_with_input(
            BenchmarkId::new("bulk_validation", error_rate),
            error_rate,
            |b, &rate| {
                let data = gen_validated_vec(1000, rate);
                b.iter(|| {
                    let count = data.iter().filter(|v| v.is_valid()).count();
                    black_box(count);
                });
            },
        );
    }

    group.bench_function("vs_result", |b| {
        let valid_data = 42;
        let error_msg = "error".to_string();
        b.iter(|| {
            // Validated operations
            let validated_result = {
                let validated = Validated::<String, i32>::valid(valid_data);
                let validated_err = Validated::<String, i32>::invalid(error_msg.clone());
                let mapped = validated.fmap(|x| x + 1);
                (mapped, validated_err.is_invalid())
            };

            // Result operations
            let result_result = {
                let result = Result::<i32, String>::Ok(valid_data);
                let result_err = Result::<i32, String>::Err(error_msg.clone());
                let mapped = result.map(|x| x + 1).unwrap_or_default();
                (mapped, result_err.is_err())
            };

            black_box((validated_result, result_result));
        });
    });

    group.bench_function("vs_vec_accumulation", |b| {
        let errors = vec!["error1", "error2", "error3", "error4", "error5"];
        b.iter(|| {
            let mut validated = Validated::<String, i32>::valid(0);
            for error in &errors {
                let error_validated = Validated::<String, i32>::invalid(error.to_string());
                validated = validated.combine_errors(&error_validated);
            }
            black_box(validated);
        });
    });

    for error_count in [1, 4, 8, 16, 32].iter() {
        group.bench_with_input(
            BenchmarkId::new("invalid_many", error_count),
            error_count,
            |b, &count| {
                let errors: Vec<String> = (0..count).map(|i| format!("error_{}", i)).collect();
                b.iter(|| {
                    black_box(Validated::<String, i32>::invalid_many(errors.clone()));
                });
            },
        );
    }

    group.bench_function("mixed_operations", |b| {
        let valid = Validated::<String, i32>::valid(42);
        let invalid = Validated::<String, i32>::invalid("error".to_string());
        b.iter(|| {
            black_box(valid.fmap(|x| x * 2));
            black_box(invalid.fmap(|x| x * 2));
            black_box(valid.combine_errors(&invalid));
        });
    });

    group.finish();
}
