use criterion::{BenchmarkId, Criterion, Throughput};
use rustica::pvec::PersistentVector;
use std::hint::black_box;
use std::sync::Arc;
use std::thread;

pub fn pvec_benchmarks(c: &mut Criterion) {
    let mut group = c.benchmark_group("PersistentVector");

    // Creation operations
    group.bench_function("creation", |b| {
        b.iter(|| {
            black_box(PersistentVector::<i32>::new());
        });
    });

    // Push operations with different sizes
    for size in [10, 100, 1000, 10000].iter() {
        group.throughput(Throughput::Elements(*size as u64));
        group.bench_with_input(BenchmarkId::new("push_back", size), size, |b, &size| {
            b.iter(|| {
                let mut vec = PersistentVector::new();
                for i in 0..size {
                    vec = vec.push_back(black_box(i));
                }
                black_box(vec)
            });
        });
    }

    // Access operations
    group.bench_function("random_access", |b| {
        let vec = (0..10000).fold(PersistentVector::new(), |v, i| v.push_back(i));
        b.iter(|| {
            for i in 0..1000 {
                let idx = (i * 17) % 10000;
                black_box(vec.get(black_box(idx)));
            }
        });
    });

    group.bench_function("sequential_access", |b| {
        let vec = (0..10000).fold(PersistentVector::new(), |v, i| v.push_back(i));
        b.iter(|| {
            for i in 0..1000 {
                black_box(vec.get(black_box(i)));
            }
        });
    });

    // Update operations
    group.bench_function("update_random", |b| {
        let vec = (0..1000).fold(PersistentVector::new(), |v, i| v.push_back(i));
        b.iter(|| {
            let mut v = vec.clone();
            for i in 0..100 {
                let idx = (i * 17) % 1000;
                v = v.update(black_box(idx), black_box(i * 2));
            }
            black_box(v)
        });
    });

    group.bench_function("update_sequential", |b| {
        let vec = (0..1000).fold(PersistentVector::new(), |v, i| v.push_back(i));
        b.iter(|| {
            let mut v = vec.clone();
            for i in 0..100 {
                v = v.update(black_box(i), black_box(i * 2));
            }
            black_box(v)
        });
    });

    // Pop operations
    group.bench_function("pop_back", |b| {
        let vec = (0..1000).fold(PersistentVector::new(), |v, i| v.push_back(i));
        b.iter(|| {
            let mut v = vec.clone();
            for _ in 0..100 {
                if let Some((new_v, _)) = v.pop_back() {
                    v = new_v;
                }
            }
            black_box(v)
        });
    });

    // Memory efficiency (structural sharing)
    group.bench_function("clone_large", |b| {
        let vec = (0..10000).fold(PersistentVector::new(), |v, i| v.push_back(i));
        b.iter(|| {
            black_box(vec.clone());
        });
    });

    group.bench_function("update_after_clone", |b| {
        let vec = (0..10000).fold(PersistentVector::new(), |v, i| v.push_back(i));
        b.iter(|| {
            let mut cloned = vec.clone();
            cloned = cloned.update(5000, black_box(42));
            black_box(cloned)
        });
    });

    group.bench_function("structural_sharing", |b| {
        let base = (0..1000).fold(PersistentVector::new(), |v, i| v.push_back(i));
        b.iter(|| {
            let mut versions = Vec::new();
            for i in 0..10 {
                let version = base.update(i * 100, black_box(i * 1000));
                versions.push(version);
            }
            black_box(versions)
        });
    });

    // Comparison with std::Vec
    let size = 10000;
    let access_count = 1000;

    group.bench_function("vs_std_vec_access", |b| {
        let vec = (0..size).fold(PersistentVector::new(), |v, i| v.push_back(i));
        b.iter(|| {
            for i in 0..access_count {
                let idx = (i * 17) % size;
                black_box(vec.get(black_box(idx)));
            }
        });
    });

    group.bench_function("vs_std_vec_build", |b| {
        b.iter(|| {
            let mut vec = PersistentVector::new();
            for i in 0..size {
                vec = vec.push_back(black_box(i));
            }
            black_box(vec)
        });
    });

    // Concurrency
    group.bench_function("concurrent_read", |b| {
        let vec = (0..10000).fold(PersistentVector::new(), |v, i| v.push_back(i));
        let arc_vec = Arc::new(vec);

        b.iter(|| {
            let handles: Vec<_> = (0..4)
                .map(|_| {
                    let vec_clone = arc_vec.clone();
                    thread::spawn(move || {
                        for i in 0..250 {
                            let idx = (i * 17) % 10000;
                            black_box(vec_clone.get(idx));
                        }
                    })
                })
                .collect();

            for handle in handles {
                handle.join().unwrap();
            }
        });
    });

    group.bench_function("concurrent_modifications", |b| {
        let vec = (0..1000).fold(PersistentVector::new(), |v, i| v.push_back(i));
        let arc_vec = Arc::new(vec);

        b.iter(|| {
            let handles: Vec<_> = (0..4)
                .map(|thread_id| {
                    let vec_clone = arc_vec.clone();
                    thread::spawn(move || {
                        let mut local_vec = (*vec_clone).clone();
                        for i in 0..25 {
                            let idx = (thread_id * 250 + i) % 1000;
                            local_vec = local_vec.update(idx, black_box(thread_id * 1000 + i));
                        }
                        local_vec
                    })
                })
                .collect();

            let results: Vec<_> = handles.into_iter().map(|h| h.join().unwrap()).collect();
            black_box(results)
        });
    });

    group.finish();
}
