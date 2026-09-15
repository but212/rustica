#![allow(deprecated)]

use crate::harness::Harness;
use rustica::datatypes::io::IO;
use std::hint::black_box;

pub fn io_benchmarks(harness: &Harness) {
    let mut group = harness.benchmark_group("IO");

    group.bench_fn("pure_creation", || {
        black_box(IO::pure(black_box(42)));
    });

    group.bench_fn("effect_creation", || {
        black_box(IO::new(|| black_box(42)));
    });

    group.bench_fn("pure_execution", || {
        black_box(IO::pure(black_box(42)).run());
    });

    group.bench_fn("effect_execution", || {
        black_box(IO::new(|| black_box(42)).run());
    });

    group.bench_fn("fmap_pure_run", || {
        black_box(IO::pure(black_box(10)).fmap(|value| value * 2).run());
    });

    group.bench_fn("fmap_effect_run", || {
        black_box(IO::new(|| black_box(10)).fmap(|value| value * 2).run());
    });

    group.bench_fn("bind_pure_run", || {
        black_box(
            IO::pure(black_box(10))
                .bind(|value| IO::pure(value * 2))
                .run(),
        );
    });

    group.bench_fn("bind_effect_run", || {
        black_box(
            IO::new(|| black_box(10))
                .bind(|value| IO::new(move || value * 2))
                .run(),
        );
    });

    group.bench_fn("apply_pure_run", || {
        let value = IO::pure(black_box(10));
        let function = IO::pure(|value: i32| value * 2);
        black_box(value.apply(function).run());
    });

    group.bench_fn("apply_effect_run", || {
        let value = IO::new(|| black_box(10));
        let function = IO::new(|| |value: i32| value * 2);
        black_box(value.apply(function).run());
    });
}
