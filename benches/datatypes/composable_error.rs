use criterion::{BenchmarkId, Criterion};
use rustica::context;
use rustica::error::ComposableError;
use std::hint::black_box;

pub fn composable_error_benchmarks(c: &mut Criterion) {
    let mut group = c.benchmark_group("ComposableError");

    // Two contexts fit inline; three exercise heap growth.
    for count in [2, 3, 50] {
        group.bench_with_input(
            BenchmarkId::new("context_accumulation", count),
            &count,
            |b, &count| {
                b.iter(|| {
                    let mut error = ComposableError::new("core error");
                    for index in 0..count {
                        error = error.with_context(context!("context {index}"));
                    }
                    black_box(error)
                });
            },
        );

        group.bench_with_input(
            BenchmarkId::new("context_iteration", count),
            &count,
            |b, &count| {
                let mut error = ComposableError::new("core error");
                for index in 0..count {
                    error = error.with_context(context!("context {index}"));
                }
                b.iter(|| black_box(error.context_iter().count()));
            },
        );
    }

    for count in [3, 50] {
        group.bench_with_input(
            BenchmarkId::new("error_chain_formatting", count),
            &count,
            |b, &count| {
                let mut error = ComposableError::new("core error");
                for index in 0..count {
                    error = error.with_context(context!("context {index}"));
                }
                b.iter(|| black_box(error.error_chain()));
            },
        );
    }

    group.finish();
}
