use crate::harness::{Harness, Throughput};
use rustica::pvec::PersistentVector;
use std::hint::black_box;

pub fn pvec_benchmarks(harness: &Harness) {
    let mut group = harness.benchmark_group("PersistentVector");

    group.bench_fn("creation", || {
        black_box(PersistentVector::<i32>::new());
    });

    // 32 is the inline/tree boundary; 64 is the height 0 tree boundary (root leaf 32 + tail buffer 32).
    for size in [32usize, 33, 64, 65, 10_000, 100_000, 1_000_000] {
        if size >= 100_000 {
            group.batch_iters(1).measure_iters(10);
        } else {
            group.batch_iters(10).measure_iters(100);
        }
        group.throughput(Throughput::Elements(size as u64));
        group.bench_with_input("pvec_push_back", &size, |&size| {
            let mut vec = PersistentVector::new();
            for value in 0..size {
                vec = vec.push_back(black_box(value));
            }
            black_box(vec);
        });
    }

    // Benchmark in-place mutation (fast path when unshared)
    for size in [32usize, 33, 10_000] {
        group.batch_iters(10).measure_iters(100);
        group.throughput(Throughput::Elements(size as u64));
        group.bench_with_input("pvec_push_back_mut", &size, |&size| {
            let mut vec = PersistentVector::new();
            for value in 0..size {
                vec.push_back_mut(black_box(value));
            }
            black_box(vec);
        });
    }

    // Benchmark extend (uses push_back_mut under the hood)
    group.batch_iters(10).measure_iters(100);
    group.throughput(Throughput::Elements(10_000));
    group.bench_fn("pvec_extend/10000", || {
        let mut vec = PersistentVector::new();
        vec.extend(0..10_000);
        black_box(vec);
    });

    // Benchmark collect vs std::vec::Vec
    group.throughput(Throughput::Elements(10_000));
    group.bench_fn("pvec_collect/10000", || {
        black_box((0..10_000).collect::<PersistentVector<usize>>());
    });
    group.bench_fn("std_vec_collect/10000", || {
        black_box((0..10_000).collect::<Vec<usize>>());
    });

    for size in [1_000usize, 100_000, 1_000_000] {
        if size >= 1_000_000 {
            group.batch_iters(1).measure_iters(10);
        } else {
            group.batch_iters(5).measure_iters(50);
        }
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

    // Benchmark random access
    for size in [1_000usize, 100_000, 1_000_000] {
        let sample_count = 10_000.min(size);
        let mut rng = 0x853c49e6748fea9bu64;
        let random_indices: Vec<usize> = (0..sample_count)
            .map(|_| {
                rng = rng
                    .wrapping_mul(6364136223846793005)
                    .wrapping_add(1442695040888963407);
                ((rng >> 32) as usize) % size
            })
            .collect();

        if size >= 1_000_000 {
            group.batch_iters(1).measure_iters(15);
        } else {
            group.batch_iters(5).measure_iters(50);
        }
        group.throughput(Throughput::Elements(sample_count as u64));
        let bench_name = format!("pvec_random_access/{size}");
        group.bench_batched(
            &bench_name,
            || (0..size).collect::<PersistentVector<usize>>(),
            |vec| {
                black_box(
                    random_indices
                        .iter()
                        .fold(0usize, |sum, &idx| sum + *vec.get(idx).unwrap()),
                );
            },
        );
    }

    // Benchmark memory usage footprint
    for size in [1_000usize, 100_000, 1_000_000] {
        let before = crate::harness::current_allocated_bytes();
        let sample = (0..size).collect::<PersistentVector<usize>>();
        let after = crate::harness::current_allocated_bytes();
        let allocated_bytes = after.saturating_sub(before);
        drop(sample);

        let bench_name = format!("pvec_memory/{size}");
        group.batch_iters(1).measure_iters(10);
        group.throughput(Throughput::Memory(allocated_bytes as u64));
        group.bench_fn(&bench_name, || {
            let v = black_box((0..size).collect::<PersistentVector<usize>>());
            black_box(v);
        });
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

        let bench_name_mut = format!("pvec_update_mut/{size}");
        group.bench_batched(
            &bench_name_mut,
            || (0..size).collect::<PersistentVector<usize>>(),
            |vec| {
                for index in (0..size).step_by(size / 10) {
                    vec.update_mut(black_box(index), black_box(index * 2));
                }
                black_box(&*vec);
            },
        );
    }

    group.reset_sampling();

    group.bench_fn("pop_back", || {
        let vec: PersistentVector<usize> = (0..1_000).collect();
        let mut current = vec;
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
