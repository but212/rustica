#[cfg(feature = "advanced")]
use criterion::{black_box, Criterion};
#[cfg(feature = "advanced")]
use rustica::datatypes::io::IO;

#[cfg(feature = "advanced")]
pub fn io_benchmarks(c: &mut Criterion) {
    let mut group = c.benchmark_group("IO");

    // ======== CONSTRUCTION OPERATIONS ========

    group.bench_function("pure_creation", |b| {
        b.iter(|| black_box(IO::pure(42)));
    });

    group.bench_function("new_creation", |b| {
        b.iter(|| black_box(IO::new(|| 42)));
    });

    group.bench_function("delay_creation", |b| {
        b.iter(|| black_box(IO::delay(std::time::Duration::from_nanos(1), 42)));
    });

    group.bench_function("new_with_computation", |b| {
        b.iter(|| {
            black_box(IO::new(|| {
                let mut sum = 0;
                for i in 0..100 {
                    sum += i;
                }
                sum
            }))
        });
    });

    // ======== BASIC OPERATIONS ========

    group.bench_function("run", |b| {
        let io = IO::pure(42);
        b.iter(|| black_box(io.run()));
    });

    group.bench_function("try_get", |b| {
        let io = IO::pure(42);
        b.iter(|| black_box(io.try_get()));
    });

    group.bench_function("run_with_computation", |b| {
        let io = IO::new(|| {
            let mut sum = 0;
            for i in 0..10 {
                sum += i;
            }
            sum
        });
        b.iter(|| black_box(io.run()));
    });

    // ======== FUNCTOR OPERATIONS ========

    group.bench_function("fmap", |b| {
        let io = IO::pure(42);
        b.iter(|| black_box(io.fmap(|x: i32| x * 2)));
    });

    group.bench_function("fmap_chain", |b| {
        let io = IO::pure(42);
        b.iter(|| black_box(io.fmap(|x: i32| x * 2).fmap(|x: i32| x + 10)));
    });

    group.bench_function("fmap_with_complex_operation", |b| {
        let io = IO::pure(42);
        b.iter(|| {
            black_box(io.fmap(|x: i32| {
                let mut result = x;
                for i in 0..5 {
                    result += i;
                }
                result
            }))
        });
    });

    // ======== APPLICATIVE OPERATIONS ========

    group.bench_function("apply", |b| {
        let io = IO::pure(42);
        b.iter(|| black_box(io.apply(|x: i32| IO::pure(x * 2))));
    });

    group.bench_function("apply_chain", |b| {
        let io = IO::pure(42);
        b.iter(|| {
            black_box(
                io.apply(|x: i32| IO::pure(x * 2))
                    .apply(|x: i32| IO::pure(x + 10)),
            )
        });
    });

    group.bench_function("apply_vs_bind", |b| {
        let io = IO::pure(42);
        b.iter_batched(
            || (io.clone(), io.clone()),
            |(io1, io2)| {
                let with_apply = io1.apply(|x: i32| IO::pure(x * 2));
                let with_bind = io2.bind(|x: i32| IO::pure(x * 2));
                black_box((with_apply, with_bind))
            },
            criterion::BatchSize::SmallInput,
        );
    });

    // ======== MONAD OPERATIONS ========

    group.bench_function("bind", |b| {
        let io = IO::pure(42);
        b.iter(|| black_box(io.bind(|x: i32| IO::pure(x * 2))));
    });

    group.bench_function("bind_chain", |b| {
        let io = IO::pure(42);
        b.iter(|| {
            black_box(
                io.bind(|x: i32| IO::pure(x * 2))
                    .bind(|x: i32| IO::pure(x + 10)),
            )
        });
    });

    group.bench_function("bind_with_complex_operation", |b| {
        let io = IO::pure(42);
        b.iter(|| {
            black_box(io.bind(|x: i32| {
                IO::new(move || {
                    let mut result = x;
                    for i in 0..5 {
                        result += i;
                    }
                    result
                })
            }))
        });
    });

    // ======== COMPLEX OPERATIONS ========

    group.bench_function("chain_operations", |b| {
        let io = IO::pure(10);
        b.iter(|| {
            black_box(
                io.fmap(|x: i32| x + 5)
                    .bind(|x: i32| IO::pure(x * 2))
                    .fmap(|x: i32| x.to_string()),
            )
        });
    });

    group.bench_function("nested_operations", |b| {
        b.iter(|| {
            black_box(IO::pure(10).bind(|x: i32| {
                IO::pure(x * 2).bind(|y: i32| IO::pure(y + 5).bind(|z: i32| IO::pure(z * z)))
            }))
        });
    });

    // ======== STRING OPERATIONS ========

    group.bench_function("string_operations", |b| {
        let s = "Hello, world!".to_string();
        b.iter(|| {
            black_box(
                IO::pure(s.clone())
                    .fmap(|s: String| s.to_uppercase())
                    .fmap(|s: String| s + "!"),
            )
        });
    });

    group.bench_function("string_processing", |b| {
        let text = "The quick brown fox jumps over the lazy dog".to_string();
        b.iter(|| {
            black_box(
                IO::pure(text.clone())
                    .fmap(|s: String| {
                        s.split_whitespace()
                            .map(|w| w.to_owned())
                            .collect::<Vec<String>>()
                    })
                    .fmap(|words: Vec<String>| words.iter().filter(|w| w.len() > 3).count())
                    .bind(|count: usize| {
                        IO::pure(format!("Words longer than 3 characters: {}", count))
                    }),
            )
        });
    });

    // ======== REAL-WORLD USE CASES ========

    // Data processing pipeline
    group.bench_function("data_processing_pipeline", |b| {
        b.iter(|| {
            black_box(
                IO::pure(vec![1, 2, 3, 4, 5])
                    .fmap(|nums: Vec<i32>| {
                        // Transform data
                        nums.iter().map(|n| n * 2).collect::<Vec<_>>()
                    })
                    .fmap(|nums: Vec<i32>| {
                        // Filter data
                        nums.iter().filter(|&&n| n > 5).cloned().collect::<Vec<_>>()
                    })
                    .fmap(|nums: Vec<i32>| {
                        // Aggregate
                        nums.iter().sum::<i32>()
                    })
                    .bind(|sum: i32| {
                        // Simulate logging results
                        IO::new(move || format!("Processed sum: {}", sum))
                    }),
            )
        });
    });

    // Input validation pattern
    group.bench_function("input_validation", |b| {
        let input = (25, "Username".to_string());
        b.iter(|| {
            black_box(IO::pure(input.clone()).bind(|(age, name): (i32, String)| {
                // Validate inputs
                let age_valid = age >= 18 && age < 100;
                let name_valid = !name.is_empty() && name.len() <= 50;

                if age_valid && name_valid {
                    IO::pure(format!("Valid input: Age {} Name {}", age, name))
                } else {
                    IO::pure(format!("Invalid input"))
                }
            }))
        });
    });

    // Resource management pattern
    group.bench_function("resource_management", |b| {
        b.iter(|| {
            black_box(
                // Simulate resource acquisition
                IO::new(|| {
                    println!("Acquiring resource (not actually printing)");
                    "resource data"
                })
                .bind(|resource: &str| {
                    // Use resource
                    IO::new(move || {
                        let processed = format!("Processed {}", resource);
                        processed
                    })
                })
                .bind(|result: String| {
                    // Simulate resource cleanup
                    IO::new(move || {
                        println!("Releasing resource (not actually printing)");
                        result.clone()
                    })
                }),
            )
        });
    });

    // Error handling pattern
    group.bench_function("error_handling", |b| {
        b.iter(|| {
            // Simulate an operation that might fail
            let io_operation = IO::new(|| -> Result<i32, &'static str> {
                // Always succeed in this example
                Ok(42)
            });

            black_box(
                io_operation.bind(|result: Result<i32, &'static str>| match result {
                    Ok(value) => IO::pure(format!("Success: {}", value)),
                    Err(err) => IO::pure(format!("Failure: {}", err)),
                }),
            )
        });
    });

    group.finish();
}

#[cfg(not(feature = "advanced"))]
pub fn io_benchmarks(_c: &mut Criterion) {
    // Empty function when advanced feature is not enabled
}
