use criterion::Criterion;
use rustica::datatypes::io::IO;
use std::hint::black_box;
use std::time::Duration;

pub fn io_benchmarks(c: &mut Criterion) {
    let mut group = c.benchmark_group("IO");

    // Creation benchmarks
    group.bench_function("io_new", |b| {
        b.iter(|| {
            let io = IO::new(|| black_box(42));
            black_box(io)
        })
    });

    group.bench_function("io_pure", |b| {
        b.iter(|| {
            let io = IO::pure(black_box(42));
            black_box(io)
        })
    });

    // Execution benchmarks
    group.bench_function("io_run", |b| {
        b.iter(|| {
            let io = IO::pure(black_box(42));
            let result = io.run();
            black_box(result)
        })
    });

    group.bench_function("io_run_with_computation", |b| {
        b.iter(|| {
            let io = IO::new(|| {
                let x = black_box(10);
                x * x + 5
            });
            let result = io.run();
            black_box(result)
        })
    });

    // Functor benchmarks
    group.bench_function("io_fmap", |b| {
        b.iter(|| {
            let io = IO::pure(black_box(10));
            let result = io.fmap(|x| x * 2);
            black_box(result)
        })
    });

    group.bench_function("io_fmap_and_run", |b| {
        b.iter(|| {
            let io = IO::pure(black_box(10));
            let result = io.fmap(|x| x * 2).run();
            black_box(result)
        })
    });

    // Monad benchmarks
    group.bench_function("io_bind", |b| {
        b.iter(|| {
            let io = IO::pure(black_box(10));
            let result = io.bind(|x| IO::pure(x * 2));
            black_box(result)
        })
    });

    group.bench_function("io_bind_and_run", |b| {
        b.iter(|| {
            let io = IO::pure(black_box(10));
            let result = io.bind(|x| IO::pure(x * 2)).run();
            black_box(result)
        })
    });

    // Apply benchmarks
    group.bench_function("io_apply", |b| {
        b.iter(|| {
            let io = IO::pure(black_box(10));
            let result = io.apply(|x| IO::pure(x + 5));
            black_box(result)
        })
    });

    // Error handling benchmarks
    group.bench_function("io_try_get_success", |b| {
        b.iter(|| {
            let io = IO::pure(black_box(42));
            let result = io.try_get();
            black_box(result)
        })
    });

    group.bench_function("io_try_get_with_context", |b| {
        b.iter(|| {
            let io = IO::pure(black_box(42));
            let result = io.try_get_with_context("test context");
            black_box(result)
        })
    });

    // Delay benchmarks (synchronous)
    group.bench_function("io_delay_sync", |b| {
        b.iter(|| {
            let io = IO::delay_sync(Duration::from_nanos(1), black_box(42));
            black_box(io)
        })
    });

    group.bench_function("io_delay_sync_run", |b| {
        b.iter(|| {
            let io = IO::delay_sync(Duration::from_nanos(1), black_box(42));
            let result = io.run();
            black_box(result)
        })
    });

    // Chaining benchmarks
    group.bench_function("io_chain_operations", |b| {
        b.iter(|| {
            let io = IO::pure(black_box(1))
                .fmap(|x| x + 1)
                .bind(|x| IO::pure(x * 2))
                .fmap(|x| x + 3);
            black_box(io)
        })
    });

    group.bench_function("io_chain_and_run", |b| {
        b.iter(|| {
            let io = IO::pure(black_box(1))
                .fmap(|x| x + 1)
                .bind(|x| IO::pure(x * 2))
                .fmap(|x| x + 3);
            let result = io.run();
            black_box(result)
        })
    });

    // Complex computation benchmarks
    group.bench_function("io_complex_computation", |b| {
        b.iter(|| {
            let io = IO::new(|| {
                let n = black_box(100);
                (0..n).map(|i| i * i).sum::<i32>()
            });
            let result = io.run();
            black_box(result)
        })
    });

    group.bench_function("io_nested_bind", |b| {
        b.iter(|| {
            let io = IO::pure(black_box(5))
                .bind(|x| IO::pure(x + 1))
                .bind(|x| IO::pure(x * 2))
                .bind(|x| IO::pure(x - 3));
            let result = io.run();
            black_box(result)
        })
    });

    group.finish();
}
