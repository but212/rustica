use criterion::{BenchmarkId, Criterion, Throughput};
#[cfg(feature = "pvec")]
use rustica::pvec::{AlwaysCache, EvenIndexCache, NeverCache, PersistentVector};
use std::hint::black_box;
use std::sync::Arc;
use std::thread;

#[cfg(feature = "pvec")]
pub fn pvec_benchmarks(c: &mut Criterion) {
    // Basic operations benchmarks
    basic_operations_benchmarks(c);

    // Size-based performance benchmarks
    size_based_benchmarks(c);

    // Cache policy comparison benchmarks
    cache_policy_benchmarks(c);

    // Memory efficiency benchmarks
    memory_efficiency_benchmarks(c);

    // Comparison with std::Vec benchmarks
    vec_comparison_benchmarks(c);

    // Concurrency benchmarks
    concurrency_benchmarks(c);

    // Structural sharing benchmarks
    structural_sharing_benchmarks(c);
}

#[cfg(feature = "pvec")]
fn basic_operations_benchmarks(c: &mut Criterion) {
    let mut group = c.benchmark_group("pvec_basic");

    // Creation benchmark
    group.bench_function("create", |b| {
        b.iter(|| {
            let vec: PersistentVector<i32> = PersistentVector::new();
            black_box(vec)
        })
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
            })
        });
    }

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
        })
    });

    // Random access with different vector sizes
    for size in [100, 1000, 10000, 100000].iter() {
        group.bench_with_input(BenchmarkId::new("random_access", size), size, |b, &size| {
            let vec = (0..size).fold(PersistentVector::new(), |v, i| v.push_back(i));
            b.iter(|| {
                for i in (0..100).map(|i| (i * size / 100) % size) {
                    black_box(vec.get(black_box(i)));
                }
            })
        });
    }

    // Sequential access
    group.bench_function("sequential_access", |b| {
        let vec = (0..10000).fold(PersistentVector::new(), |v, i| v.push_back(i));
        b.iter(|| {
            for i in 0..1000 {
                black_box(vec.get(black_box(i)));
            }
        })
    });

    // Update operations with different patterns
    group.bench_function("update_random", |b| {
        let vec = (0..1000).fold(PersistentVector::new(), |v, i| v.push_back(i));
        b.iter(|| {
            let mut v = vec.clone();
            for i in 0..100 {
                let idx = (i * 17) % 1000; // pseudo-random pattern
                v = v.update(black_box(idx), black_box(i * 2));
            }
            black_box(v)
        })
    });

    group.bench_function("update_sequential", |b| {
        let vec = (0..1000).fold(PersistentVector::new(), |v, i| v.push_back(i));
        b.iter(|| {
            let mut v = vec.clone();
            for i in 0..100 {
                v = v.update(black_box(i), black_box(i * 2));
            }
            black_box(v)
        })
    });

    group.finish();
}

#[cfg(feature = "pvec")]
fn size_based_benchmarks(c: &mut Criterion) {
    let mut group = c.benchmark_group("pvec_size_based");

    let sizes = [32, 64, 128, 512, 1024, 4096, 16384];

    for &size in &sizes {
        group.throughput(Throughput::Elements(size as u64));

        // Build benchmark
        group.bench_with_input(BenchmarkId::new("build", size), &size, |b, &size| {
            b.iter(|| {
                let mut vec = PersistentVector::new();
                for i in 0..size {
                    vec = vec.push_back(black_box(i));
                }
                black_box(vec)
            })
        });

        // Access benchmark
        group.bench_with_input(BenchmarkId::new("access", size), &size, |b, &size| {
            let vec = (0..size).fold(PersistentVector::new(), |v, i| v.push_back(i));
            b.iter(|| {
                let idx = size / 2;
                black_box(vec.get(black_box(idx)))
            })
        });
    }

    group.finish();
}

#[cfg(feature = "pvec")]
fn cache_policy_benchmarks(c: &mut Criterion) {
    let mut group = c.benchmark_group("pvec_cache_policy");

    let size = 10000;
    let access_count = 1000;

    // AlwaysCache policy
    group.bench_function("always_cache", |b| {
        let vec: PersistentVector<i32> = PersistentVector::with_cache_policy(Box::new(AlwaysCache));
        let vec = (0..size).fold(vec, |v, i| v.push_back(i));
        b.iter(|| {
            for i in 0..access_count {
                let idx = (i * 17) % size; // pseudo-random access
                black_box(vec.get(black_box(idx.try_into().unwrap())));
            }
        })
    });

    // NeverCache policy
    group.bench_function("never_cache", |b| {
        let vec: PersistentVector<i32> = PersistentVector::with_cache_policy(Box::new(NeverCache));
        let vec = (0..size).fold(vec, |v, i| v.push_back(i));
        b.iter(|| {
            for i in 0..access_count {
                let idx = (i * 17) % size; // pseudo-random access
                black_box(vec.get(black_box(idx.try_into().unwrap())));
            }
        })
    });

    // EvenIndexCache policy
    group.bench_function("even_index_cache", |b| {
        let vec: PersistentVector<i32> =
            PersistentVector::with_cache_policy(Box::new(EvenIndexCache));
        let vec = (0..size).fold(vec, |v, i| v.push_back(i));
        b.iter(|| {
            for i in 0..access_count {
                let idx = (i * 17) % size; // pseudo-random access
                black_box(vec.get(black_box(idx.try_into().unwrap())));
            }
        })
    });

    group.finish();
}

#[cfg(feature = "pvec")]
fn memory_efficiency_benchmarks(c: &mut Criterion) {
    let mut group = c.benchmark_group("pvec_memory");

    // Clone efficiency (structural sharing)
    group.bench_function("clone_large", |b| {
        let vec = (0..10000).fold(PersistentVector::new(), |v, i| v.push_back(i));
        b.iter(|| {
            let cloned = vec.clone();
            black_box(cloned)
        })
    });

    // Update after clone (copy-on-write)
    group.bench_function("update_after_clone", |b| {
        let vec = (0..10000).fold(PersistentVector::new(), |v, i| v.push_back(i));
        b.iter(|| {
            let mut cloned = vec.clone();
            cloned = cloned.update(5000, black_box(42));
            black_box(cloned)
        })
    });

    // Multiple versions
    group.bench_function("multiple_versions", |b| {
        let base = (0..1000).fold(PersistentVector::new(), |v, i| v.push_back(i));
        b.iter(|| {
            let mut versions = Vec::new();
            for i in 0..10 {
                let version = base.update(i * 100, black_box(i));
                versions.push(version);
            }
            black_box(versions)
        })
    });

    group.finish();
}

#[cfg(feature = "pvec")]
fn vec_comparison_benchmarks(c: &mut Criterion) {
    let mut group = c.benchmark_group("pvec_vs_vec");

    let size = 10000;
    let access_count = 1000;

    // PersistentVector access
    group.bench_function("pvec_access", |b| {
        let vec = (0..size).fold(PersistentVector::new(), |v, i| v.push_back(i));
        b.iter(|| {
            for i in 0..access_count {
                let idx = (i * 17) % size;
                black_box(vec.get(black_box(idx)));
            }
        })
    });

    // std::Vec access
    group.bench_function("std_vec_access", |b| {
        let vec: Vec<i32> = (0..size).map(|i| i.try_into().unwrap()).collect();
        b.iter(|| {
            for i in 0..access_count {
                let idx = (i * 17) % size;
                black_box(vec.get(black_box(idx)));
            }
        })
    });

    // PersistentVector build
    group.bench_function("pvec_build", |b| {
        b.iter(|| {
            let mut vec = PersistentVector::new();
            for i in 0..size {
                vec = vec.push_back(black_box(i));
            }
            black_box(vec)
        })
    });

    // std::Vec build
    group.bench_function("std_vec_build", |b| {
        b.iter(|| {
            let mut vec = Vec::new();
            for i in 0..size {
                vec.push(black_box(i));
            }
            black_box(vec)
        })
    });

    group.finish();
}

#[cfg(feature = "pvec")]
fn concurrency_benchmarks(c: &mut Criterion) {
    let mut group = c.benchmark_group("pvec_concurrency");

    // Shared read access
    group.bench_function("shared_read", |b| {
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
        })
    });

    // Independent modifications
    group.bench_function("independent_modifications", |b| {
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
        })
    });

    group.finish();
}

#[cfg(feature = "pvec")]
fn structural_sharing_benchmarks(c: &mut Criterion) {
    let mut group = c.benchmark_group("pvec_structural_sharing");

    // Measure efficiency of structural sharing
    group.bench_function("sharing_efficiency", |b| {
        let base = (0..10000).fold(PersistentVector::new(), |v, i| v.push_back(i));
        b.iter(|| {
            // Create multiple versions with small changes
            let mut versions = Vec::new();
            for i in 0..100 {
                let modified = base.update(i * 100, black_box(i + 1000));
                versions.push(modified);
            }

            // Access elements from all versions to ensure they're properly shared
            for (idx, version) in versions.iter().enumerate() {
                black_box(version.get(idx * 100));
            }

            black_box(versions)
        })
    });

    // Measure cost of breaking sharing
    group.bench_function("sharing_break_cost", |b| {
        let base = (0..1000).fold(PersistentVector::new(), |v, i| v.push_back(i));
        b.iter(|| {
            let mut modified = base.clone();
            // Modify every element to break all sharing
            for i in 0..1000 {
                modified = modified.update(i, black_box(i + 1000));
            }
            black_box(modified)
        })
    });

    group.finish();
}
