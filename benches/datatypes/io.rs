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

    // ======== BASIC OPERATIONS ========
    group.bench_function("run", |b| {
        let io = IO::pure(42);
        b.iter(|| black_box(io.run()));
    });

    group.bench_function("try_get", |b| {
        let io = IO::pure(42);
        b.iter(|| black_box(io.try_get()));
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

    // ======== APPLICATIVE OPERATIONS ========
    group.bench_function("apply", |b| {
        let io = IO::pure(42);
        b.iter(|| black_box(io.apply(|x: i32| IO::pure(x * 2))));
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

    // ======== REAL-WORLD USE CASES ========
    group.bench_function("data_processing_pipeline", |b| {
        b.iter(|| {
            black_box(
                IO::pure(vec![1, 2, 3, 4, 5])
                    .fmap(|nums: Vec<i32>| nums.iter().map(|n| n * 2).collect::<Vec<_>>())
                    .fmap(|nums: Vec<i32>| {
                        nums.iter().filter(|&&n| n > 5).cloned().collect::<Vec<_>>()
                    })
                    .fmap(|nums: Vec<i32>| nums.iter().sum::<i32>())
                    .bind(|sum: i32| IO::new(move || format!("Processed sum: {}", sum))),
            )
        });
    });

    // Error handling pattern
    group.bench_function("error_handling", |b| {
        b.iter(|| {
            let io_operation = IO::new(|| -> Result<i32, &'static str> { Ok(42) });
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
