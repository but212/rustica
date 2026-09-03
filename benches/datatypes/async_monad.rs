//! Focused AsyncM versus Future comparisons.

use criterion::Criterion;
use rustica::datatypes::async_monad::AsyncM;
use std::hint::black_box;

async fn computation(value: i32) -> i32 {
    value * 2
}

fn new_runtime() -> tokio::runtime::Runtime {
    match tokio::runtime::Runtime::new() {
        Ok(runtime) => runtime,
        Err(error) => panic!("benchmark runtime should initialize: {error}"),
    }
}

pub fn asyncm_benchmarks(c: &mut Criterion) {
    let mut group = c.benchmark_group("AsyncM");

    group.bench_function("future_creation", |b| {
        b.iter(|| black_box(computation(black_box(42))));
    });

    group.bench_function("asyncm_creation", |b| {
        b.iter(|| black_box(AsyncM::new(|| computation(black_box(42)))));
    });

    let runtime = new_runtime();
    group.bench_function("future_execution", |b| {
        b.iter(|| runtime.block_on(async { black_box(computation(black_box(42)).await) }));
    });

    group.bench_function("asyncm_execution", |b| {
        b.iter(|| {
            runtime.block_on(async {
                let value = AsyncM::new(|| computation(black_box(42)));
                black_box(value.try_get().await)
            })
        });
    });

    group.bench_function("future_chaining", |b| {
        b.iter(|| {
            runtime.block_on(async {
                let value = computation(computation(computation(black_box(42)).await).await).await;
                black_box(value)
            })
        });
    });

    group.bench_function("asyncm_chaining", |b| {
        b.iter(|| {
            runtime.block_on(async {
                let value = AsyncM::pure(black_box(42))
                    .bind(|value| async move { AsyncM::pure(computation(value).await) })
                    .bind(|value| async move { AsyncM::pure(computation(value).await) })
                    .bind(|value| async move { AsyncM::pure(computation(value).await) });
                black_box(value.try_get().await)
            })
        });
    });

    group.bench_function("future_parallel", |b| {
        b.iter(|| {
            runtime.block_on(async {
                black_box(tokio::join!(
                    computation(black_box(42)),
                    computation(black_box(24)),
                ))
            })
        });
    });

    group.bench_function("asyncm_parallel", |b| {
        b.iter(|| {
            runtime.block_on(async {
                let values = AsyncM::new(|| computation(black_box(42)))
                    .zip(AsyncM::new(|| computation(black_box(24))));
                black_box(values.try_get().await)
            })
        });
    });

    group.finish();
}
