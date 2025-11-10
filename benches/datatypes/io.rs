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

    // Functor benchmarks - Pure vs Effect comparison
    group.bench_function("io_fmap_pure", |b| {
        b.iter(|| {
            let io = IO::pure(black_box(10));
            let result = io.fmap(|x| x * 2);
            black_box(result)
        })
    });

    group.bench_function("io_fmap_pure_run", |b| {
        b.iter(|| {
            let io = IO::pure(black_box(10));
            let result = io.fmap(|x| x * 2).run();
            black_box(result)
        })
    });

    group.bench_function("io_fmap_effect", |b| {
        b.iter(|| {
            let io = IO::new(|| black_box(10));
            let result = io.fmap(|x| x * 2);
            black_box(result)
        })
    });

    group.bench_function("io_fmap_effect_run", |b| {
        b.iter(|| {
            let io = IO::new(|| black_box(10));
            let result = io.fmap(|x| x * 2).run();
            black_box(result)
        })
    });

    // Monad benchmarks - Pure vs Effect comparison
    group.bench_function("io_bind_pure_pure", |b| {
        b.iter(|| {
            let io = IO::pure(black_box(10));
            let result = io.bind(|x| IO::pure(x * 2));
            black_box(result)
        })
    });

    group.bench_function("io_bind_pure_pure_run", |b| {
        b.iter(|| {
            let io = IO::pure(black_box(10));
            let result = io.bind(|x| IO::pure(x * 2)).run();
            black_box(result)
        })
    });

    group.bench_function("io_bind_pure_effect", |b| {
        b.iter(|| {
            let io = IO::pure(black_box(10));
            let result = io.bind(|x| IO::new(move || x * 2));
            black_box(result)
        })
    });

    group.bench_function("io_bind_effect_pure", |b| {
        b.iter(|| {
            let io = IO::new(|| black_box(10));
            let result = io.bind(|x| IO::pure(x * 2));
            black_box(result)
        })
    });

    // Apply benchmarks - Testing Applicative pattern with different combinations
    group.bench_function("io_apply_pure_pure", |b| {
        b.iter(|| {
            let io_value = IO::pure(black_box(10));
            let io_func = IO::pure(|x: i32| x * 2);
            let result = io_value.apply(io_func);
            black_box(result)
        })
    });

    group.bench_function("io_apply_pure_pure_run", |b| {
        b.iter(|| {
            let io_value = IO::pure(black_box(10));
            let io_func = IO::pure(|x: i32| x * 2);
            let result = io_value.apply(io_func).run();
            black_box(result)
        })
    });

    group.bench_function("io_apply_pure_effect", |b| {
        b.iter(|| {
            let io_value = IO::pure(black_box(10));
            let io_func = IO::new(|| |x: i32| x * 2);
            let result = io_value.apply(io_func);
            black_box(result)
        })
    });

    group.bench_function("io_apply_effect_pure", |b| {
        b.iter(|| {
            let io_value = IO::new(|| black_box(10));
            let io_func = IO::pure(|x: i32| x * 2);
            let result = io_value.apply(io_func);
            black_box(result)
        })
    });

    group.bench_function("io_apply_effect_effect", |b| {
        b.iter(|| {
            let io_value = IO::new(|| black_box(10));
            let io_func = IO::new(|| |x: i32| x * 2);
            let result = io_value.apply(io_func);
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

    // Chaining benchmarks - Testing optimization impact
    group.bench_function("io_chain_pure_operations", |b| {
        b.iter(|| {
            let io = IO::pure(black_box(1))
                .fmap(|x| x + 1)
                .bind(|x| IO::pure(x * 2))
                .fmap(|x| x + 3);
            black_box(io)
        })
    });

    group.bench_function("io_chain_pure_run", |b| {
        b.iter(|| {
            let io = IO::pure(black_box(1))
                .fmap(|x| x + 1)
                .bind(|x| IO::pure(x * 2))
                .fmap(|x| x + 3);
            let result = io.run();
            black_box(result)
        })
    });

    // Mixed Pure/Effect chains to test optimization paths
    group.bench_function("io_chain_mixed_operations", |b| {
        b.iter(|| {
            let io = IO::new(|| black_box(1))
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

    // Test Pure fast path optimization (all Pure values)
    group.bench_function("io_nested_bind_pure_only", |b| {
        b.iter(|| {
            let io = IO::pure(black_box(5))
                .bind(|x| IO::pure(x + 1))
                .bind(|x| IO::pure(x * 2))
                .bind(|x| IO::pure(x - 3));
            let result = io.run();
            black_box(result)
        })
    });

    // Compare with Effect chain
    group.bench_function("io_nested_bind_effect_chain", |b| {
        b.iter(|| {
            let io = IO::new(|| black_box(5))
                .bind(|x| IO::new(move || x + 1))
                .bind(|x| IO::new(move || x * 2))
                .bind(|x| IO::new(move || x - 3));
            let result = io.run();
            black_box(result)
        })
    });

    group.finish();
}
