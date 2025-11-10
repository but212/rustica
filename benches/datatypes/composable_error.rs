use criterion::{BenchmarkId, Criterion};
use rustica::error::{ComposableError, error_pipeline, with_context};
use std::hint::black_box;

pub fn composable_error_benchmarks(c: &mut Criterion) {
    let mut group = c.benchmark_group("ComposableError");

    // Context accumulation - O(1) push optimization verification
    for count in [1, 10, 50, 100].iter() {
        group.bench_with_input(
            BenchmarkId::new("context_accumulation", count),
            count,
            |b, &count| {
                b.iter(|| {
                    let mut error = ComposableError::new("core error");
                    for i in 0..count {
                        error = error.with_context(format!("context {}", i));
                    }
                    black_box(error)
                });
            },
        );
    }

    // Bulk context addition
    for count in [10, 50, 100].iter() {
        group.bench_with_input(
            BenchmarkId::new("bulk_context_addition", count),
            count,
            |b, &count| {
                let contexts: Vec<String> = (0..count).map(|i| format!("context {}", i)).collect();

                b.iter(|| {
                    let error = ComposableError::new("core error").with_contexts(contexts.clone());
                    black_box(error)
                });
            },
        );
    }

    // Error chain formatting
    for count in [1, 10, 50].iter() {
        group.bench_with_input(
            BenchmarkId::new("error_chain_formatting", count),
            count,
            |b, &count| {
                let mut error = ComposableError::new("core error");
                for i in 0..count {
                    error = error.with_context(format!("context {}", i));
                }

                b.iter(|| {
                    let chain = error.error_chain();
                    black_box(chain)
                });
            },
        );
    }

    // Context access: context() vs context_iter()
    group.bench_function("context_copy", |b| {
        let mut error = ComposableError::new("core error");
        for i in 0..50 {
            error = error.with_context(format!("context {}", i));
        }

        b.iter(|| {
            let contexts = error.context();
            black_box(contexts)
        });
    });

    group.bench_function("context_iter", |b| {
        let mut error = ComposableError::new("core error");
        for i in 0..50 {
            error = error.with_context(format!("context {}", i));
        }

        b.iter(|| {
            let count = error.context_iter().count();
            black_box(count)
        });
    });

    group.bench_function("context_iter_collect", |b| {
        let mut error = ComposableError::new("core error");
        for i in 0..50 {
            error = error.with_context(format!("context {}", i));
        }

        b.iter(|| {
            let contexts: Vec<&String> = error.context_iter().collect();
            black_box(contexts)
        });
    });

    // Error pipeline operations
    group.bench_function("simple_pipeline", |b| {
        b.iter(|| {
            let result: Result<i32, &str> = Err("initial error");
            let processed = error_pipeline(result)
                .with_context("step 1 failed".to_string())
                .with_context("step 2 failed".to_string())
                .recover(|_| Ok(42))
                .finish();
            black_box(processed)
        });
    });

    group.bench_function("deep_pipeline", |b| {
        b.iter(|| {
            let result: Result<i32, &str> = Err("initial error");

            let processed = error_pipeline(result)
                .with_context("step 0 failed".to_string())
                .with_context("step 1 failed".to_string())
                .with_context("step 2 failed".to_string())
                .with_context("step 3 failed".to_string())
                .with_context("step 4 failed".to_string())
                .with_context("step 5 failed".to_string())
                .with_context("step 6 failed".to_string())
                .with_context("step 7 failed".to_string())
                .with_context("step 8 failed".to_string())
                .with_context("step 9 failed".to_string())
                .map_error(|e| format!("Error: {}", e))
                .recover(|_| Ok(100))
                .finish();

            black_box(processed)
        });
    });

    // with_context helper function
    group.bench_function("with_context_single", |b| {
        b.iter(|| {
            let error = "io error";
            let contextual = with_context(error, "failed to read file");
            black_box(contextual)
        });
    });

    group.bench_function("with_context_chained", |b| {
        b.iter(|| {
            let error = "io error";
            let contextual = with_context(error, "failed to read file")
                .with_context("configuration load failed".to_string())
                .with_context("application startup failed".to_string());
            black_box(contextual)
        });
    });

    // Error type conversions
    group.bench_function("result_to_composable", |b| {
        b.iter(|| {
            let result: Result<i32, &str> = Err("error");
            let composable = result.map_err(ComposableError::new);
            black_box(composable)
        });
    });

    group.bench_function("composable_with_context", |b| {
        b.iter(|| {
            let result: Result<i32, &str> = Err("error");
            let composable = result.map_err(|e| {
                ComposableError::new(e)
                    .with_context("operation failed".to_string())
                    .with_context("request processing failed".to_string())
            });
            black_box(composable)
        });
    });

    // Deep context chains (stress test)
    for count in [100, 500, 1000].iter() {
        group.bench_with_input(
            BenchmarkId::new("deep_context_chain", count),
            count,
            |b, &count| {
                b.iter(|| {
                    let mut error = ComposableError::new("core error");
                    for i in 0..count {
                        error = error.with_context(format!("ctx {}", i));
                    }
                    // Access contexts to ensure proper storage
                    let _ = error.context_iter().count();
                    black_box(error)
                });
            },
        );
    }

    // SmallVec optimization verification
    group.bench_function("inline_storage", |b| {
        b.iter(|| {
            let error = ComposableError::new("error")
                .with_context("ctx1".to_string())
                .with_context("ctx2".to_string())
                .with_context("ctx3".to_string())
                .with_context("ctx4".to_string());
            black_box(error)
        });
    });

    group.bench_function("heap_storage", |b| {
        b.iter(|| {
            let mut error = ComposableError::new("error");
            for i in 0..8 {
                error = error.with_context(format!("ctx{}", i));
            }
            black_box(error)
        });
    });

    group.finish();
}
