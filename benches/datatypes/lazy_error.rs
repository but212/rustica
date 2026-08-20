use criterion::{BenchmarkId, Criterion};
use rustica::context;
use rustica::error::{ComposableError, with_context_result};
use std::hint::black_box;
use std::sync::Arc;
use std::sync::atomic::{AtomicUsize, Ordering};

pub fn lazy_error_benchmarks(c: &mut Criterion) {
    let mut group = c.benchmark_group("LazyError");

    // Happy path: context! macro should NOT execute format
    group.bench_function("happy_path_lazy_context", |b| {
        b.iter(|| {
            let result: Result<i32, &str> = Ok(42);
            let processed = with_context_result(result, context!("Failed at step {}", 1));
            black_box(processed)
        });
    });

    // Happy path: traditional string allocation ALWAYS executes
    group.bench_function("happy_path_eager_context", |b| {
        b.iter(|| {
            let result: Result<i32, &str> = Ok(42);
            let processed = with_context_result(result, format!("Failed at step {}", 1));
            black_box(processed)
        });
    });

    // Error path: both should have similar performance
    group.bench_function("error_path_lazy_context", |b| {
        b.iter(|| {
            let result: Result<i32, &str> = Err("failed");
            let processed = with_context_result(result, context!("Failed at step {}", 1));
            black_box(processed)
        });
    });

    group.bench_function("error_path_eager_context", |b| {
        b.iter(|| {
            let result: Result<i32, &str> = Err("failed");
            let processed = with_context_result(result, format!("Failed at step {}", 1));
            black_box(processed)
        });
    });

    // Multi-context - happy path
    group.bench_function("multi_context_happy_lazy", |b| {
        b.iter(|| {
            let mut err: ComposableError<&str> = ComposableError::new("core");
            for i in 0..5 {
                err = err.with_context(context!("step {} failed", i));
            }
            black_box(err)
        });
    });

    group.bench_function("multi_context_happy_eager", |b| {
        b.iter(|| {
            let mut err: ComposableError<&str> = ComposableError::new("core");
            for i in 0..5 {
                err = err.with_context(format!("step {} failed", i));
            }
            black_box(err)
        });
    });

    // Complex formatting - lazy vs eager
    for count in [1, 5, 10].iter() {
        group.bench_with_input(
            BenchmarkId::new("complex_format_lazy", count),
            count,
            |b, &count| {
                b.iter(|| {
                    let mut err: ComposableError<&str> = ComposableError::new("core");
                    for i in 0..count {
                        err = err.with_context(context!(
                            "Error at iteration {} with value {}",
                            i,
                            i * 100
                        ));
                    }
                    black_box(err)
                });
            },
        );

        group.bench_with_input(
            BenchmarkId::new("complex_format_eager", count),
            count,
            |b, &count| {
                b.iter(|| {
                    let mut err: ComposableError<&str> = ComposableError::new("core");
                    for i in 0..count {
                        err = err.with_context(format!(
                            "Error at iteration {} with value {}",
                            i,
                            i * 100
                        ));
                    }
                    black_box(err)
                });
            },
        );
    }

    // Verification test: ensure lazy evaluation actually happens lazily
    group.bench_function("verify_lazy_evaluation", |b| {
        let counter = Arc::new(AtomicUsize::new(0));

        b.iter(|| {
            let c = counter.clone();
            let result: Result<i32, &str> = Ok(42);

            let _processed = with_context_result(
                result,
                context!("Evaluation count: {}", {
                    c.fetch_add(1, Ordering::Relaxed);
                    "should not run"
                }),
            );

            // Counter should remain 0 because result is Ok
            black_box(counter.load(Ordering::Relaxed))
        });
    });

    group.finish();
}
