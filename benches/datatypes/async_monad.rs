#[cfg(feature = "async")]
use criterion::{black_box, Criterion};
#[cfg(feature = "async")]
use futures::future::join_all;
#[cfg(feature = "async")]
use rustica::datatypes::async_monad::AsyncM;
#[cfg(feature = "async")]
use std::sync::{Arc, Mutex};
#[cfg(feature = "async")]
use std::time::Duration;

#[cfg(feature = "async")]
pub fn async_monad_benchmarks(c: &mut Criterion) {
    // Section 1: Creation and Initialization Operations
    let mut group = c.benchmark_group("AsyncM - Creation and Initialization");

    group.bench_function("pure with i32", |b| {
        b.iter(|| {
            black_box(AsyncM::<i32>::pure(black_box(42)));
        });
    });

    group.bench_function("pure with string", |b| {
        b.iter(|| {
            black_box(AsyncM::<String>::pure(black_box("hello world".to_string())));
        });
    });

    group.bench_function("pure with tuple", |b| {
        b.iter(|| {
            black_box(AsyncM::<(i32, String)>::pure(black_box((
                42,
                "hello".to_string(),
            ))));
        });
    });

    group.bench_function("new with simple computation", |b| {
        b.iter(|| {
            black_box(AsyncM::new(|| async { black_box(42) }));
        });
    });

    group.bench_function("new with complex computation", |b| {
        b.iter(|| {
            black_box(AsyncM::new(|| async {
                let mut sum = 0;
                for i in 0..100 {
                    sum += i;
                }
                sum
            }));
        });
    });

    group.bench_function("try_get preparation", |b| {
        let async_m = AsyncM::pure(42);
        b.iter(|| {
            let _future = black_box(async {
                let _ = async_m.try_get().await;
            });
        });
    });

    group.finish();

    // Section 2: Functor Operations
    let mut group = c.benchmark_group("AsyncM - Functor Operations");

    group.bench_function("fmap with simple transformation", |b| {
        let async_m = AsyncM::pure(42);
        b.iter(|| {
            black_box(async_m.fmap(|x: i32| async move { x + 1 }));
        });
    });

    group.bench_function("fmap with complex transformation", |b| {
        let async_m = AsyncM::pure(42);
        b.iter(|| {
            black_box(async_m.fmap(|x: i32| async move {
                let mut result = 0;
                for i in 0..x {
                    result += i;
                }
                result
            }));
        });
    });

    group.bench_function("fmap with type conversion", |b| {
        let async_m = AsyncM::pure(42);
        b.iter(|| {
            black_box(async_m.fmap(|x: i32| async move { x.to_string() }));
        });
    });

    group.bench_function("chained fmaps", |b| {
        let async_m = AsyncM::pure(42);
        b.iter(|| {
            black_box(
                async_m
                    .fmap(|x: i32| async move { x * 2 })
                    .fmap(|x: i32| async move { x + 10 })
                    .fmap(|x: i32| async move { x - 5 }),
            );
        });
    });

    group.finish();

    // Section 3: Applicative Operations
    let mut group = c.benchmark_group("AsyncM - Applicative Operations");

    group.bench_function("apply with simple function", |b| {
        let async_m_fn = AsyncM::pure(|x: i32| x + 1);
        let async_m_val = AsyncM::pure(42);
        b.iter(|| {
            black_box(async_m_val.apply(async_m_fn.clone()));
        });
    });

    group.bench_function("apply with complex function", |b| {
        let async_m_fn = AsyncM::pure(|x: i32| {
            let mut result = 0;
            for i in 0..x {
                result += i * i;
            }
            result
        });
        let async_m_val = AsyncM::pure(42);
        b.iter(|| {
            black_box(async_m_val.apply(async_m_fn.clone()));
        });
    });

    group.bench_function("apply with function returning string", |b| {
        let async_m_fn = AsyncM::pure(|x: i32| x.to_string());
        let async_m_val = AsyncM::pure(42);
        b.iter(|| {
            black_box(async_m_val.apply(async_m_fn.clone()));
        });
    });

    group.bench_function("apply with async function in AsyncM", |b| {
        // Function that would be executed asynchronously
        let async_fn = AsyncM::new(|| async { |x: i32| async move { x * 2 } });

        b.iter(|| {
            // 매 루프마다 새로운 인스턴스 생성
            let async_val = AsyncM::pure(42);
            let async_fn_clone = async_fn.clone();
            let async_val_clone = async_val.clone();

            // 소유권 문제를 해결하기 위해 Clone 타입으로 변경
            black_box(AsyncM::new(move || {
                // 클로저 내에서 사용하는 변수를 먼저 클론
                let fn_clone = async_fn_clone.clone();
                let val_clone = async_val_clone.clone();

                async move {
                    let f = fn_clone.try_get().await;
                    let x = val_clone.try_get().await;
                    f(x).await
                }
            }));
        });
    });

    group.finish();

    // Section 4: Monad Operations
    let mut group = c.benchmark_group("AsyncM - Monad Operations");

    group.bench_function("bind with simple function", |b| {
        let async_m = AsyncM::pure(42);
        b.iter(|| {
            black_box(async_m.bind(|x: i32| async move { AsyncM::pure(x + 1) }));
        });
    });

    group.bench_function("bind with complex function", |b| {
        let async_m = AsyncM::pure(42);
        b.iter(|| {
            black_box(async_m.bind(|x: i32| async move {
                let result = x * 2;
                if result > 50 {
                    AsyncM::pure(result / 2)
                } else {
                    AsyncM::pure(result * 2)
                }
            }));
        });
    });

    group.bench_function("chained binds", |b| {
        let async_m = AsyncM::pure(42);
        b.iter(|| {
            black_box(
                async_m
                    .bind(|x: i32| async move { AsyncM::pure(x * 2) })
                    .bind(|x: i32| async move { AsyncM::pure(x + 10) })
                    .bind(|x: i32| async move { AsyncM::pure(x.to_string()) }),
            );
        });
    });

    group.bench_function("nested binds", |b| {
        let async_m = AsyncM::pure(42);
        b.iter(|| {
            black_box(async_m.bind(|x: i32| async move {
                AsyncM::pure(x + 10).bind(|y| async move { AsyncM::pure(y * 2) })
            }));
        });
    });

    group.finish();

    // Section 5: Error Handling
    let mut group = c.benchmark_group("AsyncM - Error Handling");

    group.bench_function("from_result_or_default with Ok", |b| {
        b.iter(|| {
            black_box(AsyncM::from_result_or_default(
                || async { Ok::<_, &str>(42) },
                0,
            ));
        });
    });

    group.bench_function("from_result_or_default with Err", |b| {
        b.iter(|| {
            black_box(AsyncM::from_result_or_default(
                || async { Err::<i32, _>("error") },
                0,
            ));
        });
    });

    group.bench_function("error handling with complex validation", |b| {
        b.iter(|| {
            black_box(AsyncM::from_result_or_default(
                || async {
                    let value = 42;
                    if value % 2 == 0 && value > 10 && value < 100 {
                        Ok(value)
                    } else {
                        Err("Invalid value")
                    }
                },
                0,
            ));
        });
    });

    group.bench_function("chained error handling", |b| {
        b.iter(|| {
            black_box(
                AsyncM::from_result_or_default(|| async { Ok::<i32, &str>(42) }, 0).bind(
                    |x: i32| {
                        // 바깥 클로저는 x 값을 소유
                        async move {
                            // 값을 미리 계산하여 클로저 내에서 참조 사용 없이 구현
                            let condition = x > 40;
                            let doubled = x * 2;

                            AsyncM::from_result_or_default(
                                move || async move {
                                    if condition {
                                        Ok(doubled)
                                    } else {
                                        Err("Value too small")
                                    }
                                },
                                0,
                            )
                        }
                    },
                ),
            )
        });
    });

    group.finish();

    // Section 6: Combination Operations
    let mut group = c.benchmark_group("AsyncM - Combination Operations");

    group.bench_function("functor and monad combination", |b| {
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

    group.bench_function("applicative and monad combination", |b| {
        let async_m_fn = AsyncM::pure(|x: i32| x * 3);
        let async_m_val = AsyncM::pure(42);
        b.iter(|| {
            black_box(
                async_m_val
                    .apply(async_m_fn.clone())
                    .bind(|x| async move { AsyncM::pure(x + 10) }),
            );
        });
    });

    group.bench_function("error handling with transformations", |b| {
        b.iter(|| {
            black_box(
                AsyncM::from_result_or_default(|| async { Ok::<i32, &str>(42) }, 0)
                    .fmap(|x: i32| async move { x * 2 })
                    .bind(|x| async move {
                        AsyncM::from_result_or_default(
                            move || async move {
                                if x > 80 {
                                    Ok(x.to_string())
                                } else {
                                    Err("Value too small")
                                }
                            },
                            "error".to_string(),
                        )
                    }),
            );
        });
    });

    group.finish();

    // Section 7: Real-world Use Cases
    let mut group = c.benchmark_group("AsyncM - Real-world Use Cases");

    // Delayed computation to simulate network request
    group.bench_function("simulated_network_request", |b| {
        b.iter(|| {
            black_box(AsyncM::new(|| async {
                // Simulate a network request delay (without actually sleeping in benchmarks)
                if cfg!(test) {
                    #[cfg(test)]
                    tokio::time::sleep(Duration::from_millis(100)).await;
                }
                // Return simulated API response
                #[derive(Clone)]
                #[allow(dead_code)]
                struct ApiResponse {
                    status: i32,
                    data: String,
                }

                ApiResponse {
                    status: 200,
                    data: "Success".to_string(),
                }
            }));
        });
    });

    // Asynchronous data processing pipeline
    group.bench_function("data_processing_pipeline", |b| {
        // Define a simple data structure
        #[derive(Clone)]
        struct Data {
            values: Vec<i32>,
        }

        // Initial data
        let data = Data {
            values: vec![1, 2, 3, 4, 5],
        };

        b.iter(|| {
            let async_data = AsyncM::pure(data.clone());

            black_box(
                async_data
                    // Step 1: Filter values
                    .fmap(|d| async move {
                        Data {
                            values: d.values.into_iter().filter(|&x| x % 2 == 0).collect(),
                        }
                    })
                    // Step 2: Transform values
                    .fmap(|d| async move {
                        Data {
                            values: d.values.into_iter().map(|x| x * 3).collect(),
                        }
                    })
                    // Step 3: Add additional processing with conditional logic
                    .bind(|d| async move {
                        let sum: i32 = d.values.iter().sum();
                        if sum > 20 {
                            AsyncM::pure(Data { values: vec![sum] })
                        } else {
                            AsyncM::pure(d)
                        }
                    }),
            );
        });
    });

    // Asynchronous caching system
    group.bench_function("async_caching_system", |b| {
        // Simulated cache
        let cache = Arc::new(Mutex::new(std::collections::HashMap::<String, i32>::new()));

        b.iter(|| {
            let key = "test_key".to_string();
            let cache_clone = Arc::clone(&cache);

            black_box(AsyncM::new(move || {
                let key = key.clone();
                let cache_clone = Arc::clone(&cache_clone);
                async move {
                    // Check if value exists in cache
                    let cache_value = {
                        let cache_guard = cache_clone.lock().unwrap();
                        cache_guard.get(&key).cloned()
                    };

                    match cache_value {
                        Some(value) => value,
                        None => {
                            // Value not in cache, compute it
                            let computed_value = 42;

                            // Store in cache for future use
                            let mut cache_guard = cache_clone.lock().unwrap();
                            cache_guard.insert(key, computed_value);

                            computed_value
                        }
                    }
                }
            }));
        });
    });

    // Asynchronous retry mechanism
    group.bench_function("async_retry_mechanism", |b| {
        b.iter(|| {
            // 클론 가능한 Operation 정의를 위해 타입 명시
            #[derive(Clone)]
            struct RetryOperation;

            impl RetryOperation {
                fn call(&self, attempt: i32) -> AsyncM<Result<String, String>> {
                    AsyncM::new(move || async move {
                        if attempt < 3 {
                            Err(format!("Failed on attempt {}", attempt))
                        } else {
                            Ok(format!("Succeeded on attempt {}", attempt))
                        }
                    })
                }
            }

            let operation = RetryOperation;

            // Implement retry logic
            black_box(AsyncM::new(move || {
                let op = operation.clone();
                async move {
                    let mut attempt = 1;
                    let max_retries = 5;
                    let mut result = op.call(attempt).try_get().await;

                    while result.is_err() && attempt < max_retries {
                        attempt += 1;
                        result = op.call(attempt).try_get().await;
                    }

                    result.unwrap_or_else(|e| format!("All retries failed: {}", e))
                }
            }));
        });
    });

    // Parallel async operations
    group.bench_function("parallel_async_operations", |b| {
        b.iter(|| {
            black_box(AsyncM::new(|| async {
                // Create multiple async operations
                let op1 = AsyncM::pure(1).fmap(|x| async move { x * 2 });
                let op2 = AsyncM::pure(2).fmap(|x| async move { x * 3 });
                let op3 = AsyncM::pure(3).fmap(|x| async move { x * 4 });

                // Execute them in parallel and collect results
                let futures = vec![op1.try_get(), op2.try_get(), op3.try_get()];

                let results = join_all(futures).await;
                results.into_iter().sum::<i32>()
            }));
        });
    });

    // State machine with async transitions
    group.bench_function("async_state_machine", |b| {
        // Define states
        #[derive(Clone, Debug, PartialEq)]
        #[allow(dead_code)]
        enum State {
            Initial,
            Processing,
            Completed,
            Error,
        }

        b.iter(|| {
            // Start with initial state
            let initial = AsyncM::pure(State::Initial);

            black_box(
                initial
                    // Transition from Initial to Processing
                    .bind(|state| async move {
                        match state {
                            State::Initial => AsyncM::pure(State::Processing),
                            _ => AsyncM::pure(state),
                        }
                    })
                    // Perform processing
                    .bind(|state| async move {
                        match state {
                            State::Processing => {
                                // Simulate processing success (this would normally be conditional)
                                AsyncM::pure(State::Completed)
                            }
                            _ => AsyncM::pure(state),
                        }
                    })
                    // Handle completion
                    .bind(|state| async move {
                        match state {
                            State::Completed => {
                                // Perform final actions
                                AsyncM::pure(state)
                            }
                            _ => AsyncM::pure(state),
                        }
                    }),
            );
        });
    });

    // Compare with traditional patterns
    group.bench_function("traditional_async_pattern", |b| {
        b.iter(|| {
            #[allow(unused_must_use)]
            black_box(async {
                let x = 42;
                let y = x + 1;
                y
            });
        });
    });

    group.bench_function("async_monad_pattern", |b| {
        b.iter(|| {
            black_box(AsyncM::pure(42).fmap(|x: i32| async move { x + 1 }));
        });
    });

    group.finish();
}

#[cfg(not(feature = "async"))]
pub fn async_monad_benchmarks(_c: &mut Criterion) {
    // Benchmarks disabled when async feature is not enabled
}
