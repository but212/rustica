//! Benchmark for AsyncM vs Future performance comparison
//!
//! This benchmark compares the performance of AsyncM monad against standard Rust Future
//! for various async operations including creation, chaining, parallel execution, and error handling.

use criterion::{BenchmarkId, Criterion};
use rustica::datatypes::async_monad::AsyncM;
use std::hint::black_box;
use std::time::Duration;

// Simple async function for testing
async fn simple_computation(x: i32) -> i32 {
    x * 2
}

// Async function that simulates I/O delay
async fn delayed_computation(x: i32) -> i32 {
    tokio::time::sleep(Duration::from_nanos(100)).await;
    x * 2
}

// Async function that might fail
async fn fallible_computation(x: i32) -> Result<i32, &'static str> {
    if x < 0 {
        Err("negative value")
    } else {
        Ok(x * 2)
    }
}

fn new_runtime() -> tokio::runtime::Runtime {
    match tokio::runtime::Runtime::new() {
        Ok(runtime) => runtime,
        Err(error) => panic!("failed to create benchmark runtime: {error}"),
    }
}

pub fn asyncm_benchmarks(c: &mut Criterion) {
    let mut group = c.benchmark_group("AsyncM");

    group.bench_function("creation", |b| {
        b.iter(|| {
            black_box(AsyncM::new(|| async {
                simple_computation(black_box(42)).await
            }));
            black_box(AsyncM::pure(black_box(42)));
        });
    });

    group.bench_function("simple_execution", |b| {
        let rt = new_runtime();
        b.iter(|| {
            rt.block_on(async {
                let asyncm = AsyncM::new(|| async { simple_computation(black_box(42)).await });
                black_box(asyncm.try_get().await)
            });
        });
    });

    group.bench_function("chaining", |b| {
        let rt = new_runtime();
        b.iter(|| {
            rt.block_on(async {
                let asyncm = AsyncM::pure(black_box(42))
                    .bind(|x| async move { AsyncM::pure(simple_computation(x).await) })
                    .bind(|x| async move { AsyncM::pure(simple_computation(x).await) })
                    .bind(|x| async move { AsyncM::pure(simple_computation(x).await) });
                black_box(asyncm.try_get().await)
            });
        });
    });

    group.bench_function("parallel_execution", |b| {
        let rt = new_runtime();
        b.iter(|| {
            rt.block_on(async {
                let asyncm = AsyncM::new(|| async { simple_computation(black_box(42)).await }).zip(
                    AsyncM::new(|| async { simple_computation(black_box(24)).await }),
                );
                black_box(asyncm.try_get().await)
            });
        });
    });

    group.bench_function("error_handling", |b| {
        let rt = new_runtime();
        b.iter(|| {
            rt.block_on(async {
                let asyncm_success =
                    AsyncM::from_result_or_default(move || fallible_computation(black_box(42)), 0);
                let asyncm_error =
                    AsyncM::from_result_or_default(move || fallible_computation(black_box(-1)), 0);
                black_box(asyncm_success.try_get().await);
                black_box(asyncm_error.try_get().await)
            });
        });
    });

    group.bench_function("future_creation", |b| {
        b.iter(|| {
            let future = async { simple_computation(black_box(42)).await };
            drop(black_box(future));
        });
    });

    group.bench_function("asyncm_creation", |b| {
        b.iter(|| {
            let asyncm = AsyncM::new(|| async { simple_computation(black_box(42)).await });
            black_box(asyncm);
        });
    });

    let rt = new_runtime();
    group.bench_function("future_execution", |b| {
        b.iter(|| {
            rt.block_on(async {
                black_box(simple_computation(black_box(42)).await);
            });
        });
    });

    group.bench_function("asyncm_execution", |b| {
        b.iter(|| {
            rt.block_on(async {
                let asyncm = AsyncM::new(|| async { simple_computation(black_box(42)).await });
                black_box(asyncm.try_get().await);
            });
        });
    });

    group.bench_function("future_chaining", |b| {
        b.iter(|| {
            rt.block_on(async {
                let result = simple_computation(
                    simple_computation(simple_computation(black_box(42)).await).await,
                )
                .await;
                black_box(result);
            });
        });
    });

    group.bench_function("asyncm_chaining", |b| {
        b.iter(|| {
            rt.block_on(async {
                let asyncm = AsyncM::pure(black_box(42))
                    .bind(|x| async move { AsyncM::pure(simple_computation(x).await) })
                    .bind(|x| async move { AsyncM::pure(simple_computation(x).await) })
                    .bind(|x| async move { AsyncM::pure(simple_computation(x).await) });
                black_box(asyncm.try_get().await);
            });
        });
    });

    group.bench_function("future_parallel", |b| {
        b.iter(|| {
            rt.block_on(async {
                let results = tokio::join!(
                    simple_computation(black_box(42)),
                    simple_computation(black_box(24))
                );
                black_box(results);
            });
        });
    });

    group.bench_function("asyncm_parallel", |b| {
        b.iter(|| {
            rt.block_on(async {
                let asyncm = AsyncM::new(|| async { simple_computation(black_box(42)).await }).zip(
                    AsyncM::new(|| async { simple_computation(black_box(24)).await }),
                );
                black_box(asyncm.try_get().await);
            });
        });
    });

    // Add delayed computation benchmarks for realistic I/O simulation
    group.bench_function("delayed_execution", |b| {
        let rt = new_runtime();
        b.iter(|| {
            rt.block_on(async {
                let asyncm = AsyncM::new(|| async { delayed_computation(black_box(42)).await });
                black_box(asyncm.try_get().await)
            });
        });
    });

    group.bench_function("delayed_parallel", |b| {
        let rt = new_runtime();
        b.iter(|| {
            rt.block_on(async {
                let asyncm = AsyncM::new(|| async { delayed_computation(black_box(42)).await })
                    .zip(AsyncM::new(|| async {
                        delayed_computation(black_box(24)).await
                    }));
                black_box(asyncm.try_get().await)
            });
        });
    });

    // Memory allocation benchmarks
    #[allow(clippy::excessive_nesting)]
    for chain_len in [5, 10, 20].iter() {
        group.bench_with_input(
            BenchmarkId::new("chain_allocation", chain_len),
            chain_len,
            |b, &len| {
                let rt = new_runtime();
                b.iter(|| {
                    rt.block_on(async {
                        let mut asyncm = AsyncM::pure(black_box(42));
                        for _ in 0..len {
                            asyncm = asyncm
                                .bind(|x| async move { AsyncM::pure(simple_computation(x).await) });
                        }
                        black_box(asyncm.try_get().await)
                    });
                });
            },
        );
    }

    group.finish();
}
