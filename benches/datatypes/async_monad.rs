#[cfg(feature = "async")]
use criterion::{black_box, Criterion};
#[cfg(feature = "async")]
use futures::future::join_all;
#[cfg(feature = "async")]
use rustica::datatypes::async_monad::AsyncM;
#[cfg(feature = "async")]
use std::sync::{Arc, Mutex};

#[cfg(feature = "async")]
pub fn async_monad_benchmarks(c: &mut Criterion) {
    // Section 1: Basic Operations
    let mut group = c.benchmark_group("AsyncM - Basic Operations");

    group.bench_function("pure with i32", |b| {
        b.iter(|| black_box(AsyncM::<i32>::pure(black_box(42))));
    });

    group.bench_function("pure with complex type", |b| {
        b.iter(|| {
            black_box(AsyncM::<(i32, String)>::pure(black_box((
                42,
                "hello".to_string(),
            ))))
        });
    });

    group.bench_function("new with computation", |b| {
        b.iter(|| black_box(AsyncM::new(|| async { black_box(42) })));
    });

    group.bench_function("fmap operation", |b| {
        let async_m = AsyncM::pure(42);
        b.iter(|| black_box(async_m.fmap(|x: i32| async move { x + 1 })));
    });

    group.bench_function("bind operation", |b| {
        let async_m = AsyncM::pure(42);
        b.iter(|| black_box(async_m.bind(|x: i32| async move { AsyncM::pure(x + 1) })));
    });

    group.bench_function("apply operation", |b| {
        let async_m_fn = AsyncM::pure(|x: i32| x + 1);
        let async_m_val = AsyncM::pure(42);
        b.iter(|| black_box(async_m_val.apply(async_m_fn.clone())));
    });

    group.finish();

    // Section 2: Composition and Chaining
    let mut group = c.benchmark_group("AsyncM - Composition");

    group.bench_function("chained operations", |b| {
        let async_m = AsyncM::pure(42);
        b.iter(|| {
            black_box(
                async_m
                    .fmap(|x: i32| async move { x * 2 })
                    .bind(|x| async move { AsyncM::pure(x + 10) })
                    .fmap(|x: i32| async move { x.to_string() }),
            );
        });
    });

    group.bench_function("error handling", |b| {
        b.iter(|| {
            black_box(
                AsyncM::from_result_or_default(|| async { Ok::<i32, &str>(42) }, 0).bind(
                    |x: i32| async move {
                        AsyncM::from_result_or_default(
                            move || async move {
                                if x > 40 {
                                    Ok(x * 2)
                                } else {
                                    Err("Value too small")
                                }
                            },
                            0,
                        )
                    },
                ),
            );
        });
    });

    group.finish();

    // Section 3: Real-world Use Cases
    let mut group = c.benchmark_group("AsyncM - Use Cases");

    group.bench_function("data_processing_pipeline", |b| {
        #[derive(Clone)]
        struct Data {
            values: Vec<i32>,
        }

        let data = Data {
            values: vec![1, 2, 3, 4, 5],
        };

        b.iter(|| {
            let async_data = AsyncM::pure(data.clone());
            black_box(
                async_data
                    .fmap(|d| async move {
                        Data {
                            values: d.values.into_iter().filter(|&x| x % 2 == 0).collect(),
                        }
                    })
                    .fmap(|d| async move {
                        Data {
                            values: d.values.into_iter().map(|x| x * 3).collect(),
                        }
                    }),
            );
        });
    });

    group.bench_function("async_caching", |b| {
        let cache = Arc::new(Mutex::new(std::collections::HashMap::<String, i32>::new()));

        b.iter(|| {
            let key = "test_key".to_string();
            let cache_clone = Arc::clone(&cache);

            black_box(AsyncM::new(move || {
                let key = key.clone();
                let cache_clone = Arc::clone(&cache_clone);
                async move {
                    let cache_value = {
                        let cache_guard = cache_clone.lock().unwrap();
                        cache_guard.get(&key).cloned()
                    };

                    match cache_value {
                        Some(value) => value,
                        None => {
                            let computed_value = 42;
                            let mut cache_guard = cache_clone.lock().unwrap();
                            cache_guard.insert(key, computed_value);
                            computed_value
                        },
                    }
                }
            }));
        });
    });

    group.bench_function("parallel_operations", |b| {
        b.iter(|| {
            black_box(AsyncM::new(|| async {
                let op1 = AsyncM::pure(1).fmap(|x| async move { x * 2 });
                let op2 = AsyncM::pure(2).fmap(|x| async move { x * 3 });
                let op3 = AsyncM::pure(3).fmap(|x| async move { x * 4 });

                let futures = vec![op1.try_get(), op2.try_get(), op3.try_get()];
                join_all(futures).await.into_iter().sum::<i32>()
            }));
        });
    });

    group.finish();
}

#[cfg(not(feature = "async"))]
pub fn async_monad_benchmarks(_c: &mut Criterion) {
    // Benchmarks disabled when async feature is not enabled
}
