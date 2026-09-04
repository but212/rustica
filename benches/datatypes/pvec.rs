use criterion::{BatchSize, BenchmarkId, Criterion, Throughput};
use rustica::pvec::PersistentVector;
use std::hint::black_box;

pub fn pvec_benchmarks(c: &mut Criterion) {
    let mut group = c.benchmark_group("PersistentVector");

    group.bench_function("creation", |b| {
        b.iter(|| black_box(PersistentVector::<i32>::new()));
    });

    // 64 is the inline/tree representation boundary.
    for size in [64usize, 65, 10_000] {
        group.throughput(Throughput::Elements(size as u64));
        group.bench_with_input(BenchmarkId::new("push_back", size), &size, |b, &size| {
            b.iter(|| {
                let mut vec = PersistentVector::new();
                for value in 0..size {
                    vec = vec.push_back(black_box(value));
                }
                black_box(vec)
            });
        });
    }

    for size in [1_000usize, 100_000] {
        group.throughput(Throughput::Elements(size as u64));
        for direction in ["forward", "reverse"] {
            group.bench_with_input(
                BenchmarkId::new(format!("iter_{direction}"), size),
                &size,
                |b, &size| {
                    b.iter_batched_ref(
                        || (0..size).collect::<PersistentVector<usize>>(),
                        |vec| {
                            if direction == "reverse" {
                                black_box(
                                    vec.iter()
                                        .rev()
                                        .fold(0usize, |sum, value| sum + black_box(value)),
                                )
                            } else {
                                black_box(
                                    vec.iter().fold(0usize, |sum, value| sum + black_box(value)),
                                )
                            }
                        },
                        BatchSize::SmallInput,
                    );
                },
            );
        }

        group.bench_with_input(
            BenchmarkId::new("indexed_access", size),
            &size,
            |b, &size| {
                b.iter_batched_ref(
                    || (0..size).collect::<PersistentVector<usize>>(),
                    |vec| {
                        black_box((0..size).fold(0usize, |sum, index| {
                            let value = match vec.get(index) {
                                Some(value) => value,
                                None => unreachable!("benchmark index must exist"),
                            };
                            sum + black_box(value)
                        }))
                    },
                    BatchSize::SmallInput,
                );
            },
        );
    }

    for size in [1_000, 10_000] {
        group.bench_with_input(BenchmarkId::new("update", size), &size, |b, &size| {
            let vec: PersistentVector<usize> = (0..size).collect();
            b.iter(|| {
                let mut updated = vec.clone();
                for index in (0..size).step_by(size / 10) {
                    updated = updated.update(black_box(index), black_box(index * 2));
                }
                black_box(updated)
            });
        });
    }

    group.bench_function("pop_back", |b| {
        let vec: PersistentVector<usize> = (0..1_000).collect();
        b.iter(|| {
            let mut current = vec.clone();
            for _ in 0..100 {
                current = match current.pop_back() {
                    Some((next, _)) => next,
                    None => unreachable!("benchmark vector is non-empty"),
                };
            }
            black_box(current)
        });
    });

    group.bench_function("pvec_sharing", |b| {
        let base: PersistentVector<usize> = (0..1_000).collect();
        b.iter(|| {
            let versions: Vec<_> = (0..10)
                .map(|index| base.update(index * 100, black_box(index * 1_000)))
                .collect();
            black_box(versions)
        });
    });

    group.bench_function("std_vec_copying", |b| {
        let base: Vec<usize> = (0..1_000).collect();
        b.iter(|| {
            let versions: Vec<_> = (0..10)
                .map(|index| {
                    let mut copy = base.clone();
                    copy[index * 100] = black_box(index * 1_000);
                    copy
                })
                .collect();
            black_box(versions)
        });
    });

    group.finish();
}
