use crate::harness::{Harness, Throughput};
use rustica::pvec::PersistentVector;
use std::hint::black_box;

pub fn pvec_benchmarks(harness: &Harness) {
    let mut group = harness.benchmark_group("PersistentVector");

    group.bench_fn("creation", || {
        black_box(PersistentVector::<i32>::new());
    });

    // 64 is the inline/tree representation boundary.
    for size in [64usize, 65, 10_000] {
        group.throughput(Throughput::Elements(size as u64));
        group.bench_with_input("pvec_push_back", &size, |&size| {
            let mut vec = PersistentVector::new();
            for value in 0..size {
                vec = vec.push_back(black_box(value));
            }
            black_box(vec);
        });
    }

    for size in [1_000usize, 100_000] {
        group.throughput(Throughput::Elements(size as u64));
        for direction in ["forward", "reverse"] {
            let bench_name = format!("pvec_iter_{direction}/{size}");
            group.bench_batched(
                &bench_name,
                || (0..size).collect::<PersistentVector<usize>>(),
                |vec| {
                    if direction == "reverse" {
                        black_box(
                            vec.iter()
                                .rev()
                                .fold(0usize, |sum, value| sum + black_box(value)),
                        );
                    } else {
                        black_box(vec.iter().fold(0usize, |sum, value| sum + black_box(value)));
                    }
                },
            );
        }

        let bench_name = format!("pvec_indexed_access/{size}");
        group.bench_batched(
            &bench_name,
            || (0..size).collect::<PersistentVector<usize>>(),
            |vec| {
                black_box((0..size).fold(0usize, |sum, index| {
                    let value = match vec.get(index) {
                        Some(value) => value,
                        None => unreachable!("benchmark index must exist"),
                    };
                    sum + black_box(value)
                }));
            },
        );
    }

    group.clear_throughput();

    for size in [1_000, 10_000] {
        let bench_name = format!("pvec_update/{size}");
        let base_vec = (0..size).collect::<PersistentVector<usize>>();
        group.bench_batched(
            &bench_name,
            || base_vec.clone(),
            |vec| {
                for index in (0..size).step_by(size / 10) {
                    *vec = vec.update(black_box(index), black_box(index * 2));
                }
                black_box(&*vec);
            },
        );
    }

    group.bench_fn("pop_back", || {
        let vec: PersistentVector<usize> = (0..1_000).collect();
        let mut current = vec.clone();
        for _ in 0..100 {
            current = match current.pop_back() {
                Some((next, _)) => next,
                None => unreachable!("benchmark vector is non-empty"),
            };
        }
        black_box(current);
    });

    group.bench_fn("pvec_sharing", || {
        let base: PersistentVector<usize> = (0..1_000).collect();
        let versions: Vec<_> = (0..10)
            .map(|index| base.update(index * 100, black_box(index * 1_000)))
            .collect();
        black_box(versions);
    });

    group.bench_fn("std_vec_copying", || {
        let base: Vec<usize> = (0..1_000).collect();
        let versions: Vec<_> = (0..10)
            .map(|index| {
                let mut copy = base.clone();
                copy[index * 100] = black_box(index * 1_000);
                copy
            })
            .collect();
        black_box(versions);
    });
}
