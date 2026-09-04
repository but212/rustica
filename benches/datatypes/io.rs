use criterion::Criterion;
use rustica::datatypes::io::IO;
use std::hint::black_box;

pub fn io_benchmarks(c: &mut Criterion) {
    let mut group = c.benchmark_group("IO");

    group.bench_function("pure_creation", |b| {
        b.iter(|| black_box(IO::pure(black_box(42))));
    });

    group.bench_function("effect_creation", |b| {
        b.iter(|| black_box(IO::new(|| black_box(42))));
    });

    group.bench_function("pure_execution", |b| {
        b.iter(|| black_box(IO::pure(black_box(42)).run()));
    });

    group.bench_function("effect_execution", |b| {
        b.iter(|| black_box(IO::new(|| black_box(42)).run()));
    });

    group.bench_function("fmap_pure_run", |b| {
        b.iter(|| black_box(IO::pure(black_box(10)).fmap(|value| value * 2).run()));
    });

    group.bench_function("fmap_effect_run", |b| {
        b.iter(|| black_box(IO::new(|| black_box(10)).fmap(|value| value * 2).run()));
    });

    group.bench_function("bind_pure_run", |b| {
        b.iter(|| {
            black_box(
                IO::pure(black_box(10))
                    .bind(|value| IO::pure(value * 2))
                    .run(),
            )
        });
    });

    group.bench_function("bind_effect_run", |b| {
        b.iter(|| {
            black_box(
                IO::new(|| black_box(10))
                    .bind(|value| IO::new(move || value * 2))
                    .run(),
            )
        });
    });

    group.bench_function("apply_pure_run", |b| {
        b.iter(|| {
            let value = IO::pure(black_box(10));
            let function = IO::pure(|value: i32| value * 2);
            black_box(value.apply(function).run())
        });
    });

    group.bench_function("apply_effect_run", |b| {
        b.iter(|| {
            let value = IO::new(|| black_box(10));
            let function = IO::new(|| |value: i32| value * 2);
            black_box(value.apply(function).run())
        });
    });

    group.finish();
}
