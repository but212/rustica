use crate::harness::Harness;
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

pub fn asyncm_benchmarks(harness: &Harness) {
    let mut group = harness.benchmark_group("AsyncM");

    group.bench_fn("future_creation", || {
        drop(black_box(computation(black_box(42))));
    });

    group.bench_fn("asyncm_creation", || {
        black_box(AsyncM::new(|| computation(black_box(42))));
    });

    let runtime = new_runtime();
    group.bench_fn("future_execution", || {
        runtime.block_on(async { black_box(computation(black_box(42)).await) });
    });

    group.bench_fn("asyncm_execution", || {
        runtime.block_on(async {
            let value = AsyncM::new(|| computation(black_box(42)));
            black_box(value.try_get().await);
        });
    });

    group.bench_fn("future_chaining", || {
        runtime.block_on(async {
            let value = computation(computation(computation(black_box(42)).await).await).await;
            black_box(value);
        });
    });

    group.bench_fn("asyncm_chaining", || {
        runtime.block_on(async {
            let value = AsyncM::pure(black_box(42))
                .bind(|value| async move { AsyncM::pure(computation(value).await) })
                .bind(|value| async move { AsyncM::pure(computation(value).await) })
                .bind(|value| async move { AsyncM::pure(computation(value).await) });
            black_box(value.try_get().await);
        });
    });

    group.bench_fn("future_parallel", || {
        runtime.block_on(async {
            black_box(tokio::join!(
                computation(black_box(42)),
                computation(black_box(24)),
            ));
        });
    });

    group.bench_fn("asyncm_parallel", || {
        runtime.block_on(async {
            let values = AsyncM::new(|| computation(black_box(42)))
                .zip(AsyncM::new(|| computation(black_box(24))));
            black_box(values.try_get().await);
        });
    });
}
