use criterion::Criterion;
#[cfg(feature = "pvec")]
use rustica::pvec::{PersistentVector, pvec};
use std::hint::black_box;

#[cfg(feature = "pvec")]
pub fn pvec_benchmarks(c: &mut Criterion) {
    // Creation benchmark
    c.bench_function("pvec_create", |b| {
        b.iter(|| {
            let vec: PersistentVector<i32> = PersistentVector::new();
            black_box(vec)
        })
    });

    // Push operations
    c.bench_function("pvec_push_back", |b| {
        b.iter(|| {
            let mut vec = PersistentVector::new();
            for i in 0..1000 {
                vec = vec.push_back(black_box(i));
            }
            black_box(vec)
        })
    });

    // Random access
    c.bench_function("pvec_random_access", |b| {
        let vec = (0..10000).fold(PersistentVector::new(), |v, i| v.push_back(i));
        b.iter(|| {
            for i in (0..100).map(|i| i * 100) {
                black_box(vec.get(black_box(i)));
            }
        })
    });

    // --- Cache Policy Benchmarks ---
    use rustica::pvec::{AlwaysCache, BoxedCachePolicy, EvenIndexCache, NeverCache};
    use std::boxed::Box;

    // Helper: create vector with cache policy
    fn make_pvec_with_policy(size: usize, policy: BoxedCachePolicy) -> PersistentVector<usize> {
        let mut vec = PersistentVector::with_cache_policy(policy);
        for i in 0..size {
            vec = vec.push_back(i);
        }
        vec
    }

    // Benchmark: get_with_cache with AlwaysCache
    c.bench_function("pvec_get_with_cache_always", |b| {
        let mut vec: PersistentVector<usize> = make_pvec_with_policy(10000, Box::new(AlwaysCache));
        b.iter(|| {
            for i in (0..100).map(|i| i * 100) {
                black_box(vec.get_with_cache(black_box(i)));
            }
        })
    });

    // Benchmark: get_with_cache with NeverCache
    c.bench_function("pvec_get_with_cache_never", |b| {
        let mut vec: PersistentVector<usize> = make_pvec_with_policy(10000, Box::new(NeverCache));
        b.iter(|| {
            for i in (0..100).map(|i| i * 100) {
                black_box(vec.get_with_cache(black_box(i)));
            }
        })
    });

    // Benchmark: get_with_cache with EvenIndexCache
    c.bench_function("pvec_get_with_cache_even_index", |b| {
        let mut vec: PersistentVector<usize> =
            make_pvec_with_policy(10000, Box::new(EvenIndexCache));
        b.iter(|| {
            for i in (0..100).map(|i| i * 100) {
                black_box(vec.get_with_cache(black_box(i)));
            }
        })
    });

    // Update operations
    c.bench_function("pvec_update", |b| {
        let vec = (0..1000).fold(PersistentVector::new(), |v, i| v.push_back(i));
        b.iter(|| {
            let mut v = vec.clone();
            for i in 0..100 {
                v = v.update(black_box(i * 10), black_box(i * 2));
            }
            black_box(v)
        })
    });

    // Benchmark: update with different cache policies
    c.bench_function("pvec_update_with_always_cache", |b| {
        let vec = make_pvec_with_policy(1000, Box::new(AlwaysCache));
        b.iter(|| {
            let mut v = vec.clone();
            for i in 0..100 {
                v = v.update_with_cache_policy(black_box(i * 10), black_box(i * 2));
            }
            black_box(v)
        })
    });

    c.bench_function("pvec_update_with_never_cache", |b| {
        let vec = make_pvec_with_policy(1000, Box::new(NeverCache));
        b.iter(|| {
            let mut v = vec.clone();
            for i in 0..100 {
                v = v.update_with_cache_policy(black_box(i * 10), black_box(i * 2));
            }
            black_box(v)
        })
    });

    c.bench_function("pvec_update_with_even_cache", |b| {
        let vec = make_pvec_with_policy(1000, Box::new(EvenIndexCache));
        b.iter(|| {
            let mut v = vec.clone();
            for i in 0..100 {
                v = v.update_with_cache_policy(black_box(i * 10), black_box(i * 2));
            }
            black_box(v)
        })
    });

    // Macro creation
    c.bench_function("pvec_macro", |b| {
        b.iter(|| black_box(pvec![1, 2, 3, 4, 5, 6, 7, 8, 9, 10]))
    });

    // --- Node/Chunk Management Stress Benchmark ---
    c.bench_function("pvec_split_merge_stress", |b| {
        b.iter(|| {
            let mut vec = PersistentVector::new();
            // Alternate push and pop to trigger splits/merges
            for i in 0..10_000 {
                vec = vec.push_back(i);
                if i % 8 == 0 && !vec.is_empty() {
                    let _ = vec.pop_back();
                }
            }
            black_box(vec)
        })
    });

    // --- In-place Branch Modification Benchmark ---
    c.bench_function("pvec_inplace_branch_modification", |b| {
        b.iter(|| {
            let mut vec = PersistentVector::new();
            for i in 0..10_000 {
                vec = vec.push_back(i);
            }
            // Perform updates that maximize structural sharing
            for i in (0..10_000).step_by(7) {
                let _ = vec.update(i, i + 1);
            }
            black_box(vec)
        })
    });

    // --- AllocationStrategy/MemoryManager Benchmarks ---
    use rustica::pvec::{AllocationStrategy, MemoryManager};

    // Benchmark switching strategies at runtime
    c.bench_function("pvec_memory_manager_switch_strategy", |b| {
        b.iter(|| {
            let mut manager: MemoryManager<i32> = MemoryManager::new(AllocationStrategy::Direct);
            manager.set_strategy(AllocationStrategy::Pooled);
            manager.set_strategy(AllocationStrategy::Adaptive);
            manager.set_strategy(AllocationStrategy::Direct);
            black_box(manager)
        })
    });

    // Benchmark stats collection
    c.bench_function("pvec_memory_manager_stats", |b| {
        let manager: MemoryManager<i32> = MemoryManager::new(AllocationStrategy::Pooled);
        b.iter(|| {
            let stats = manager.stats();
            black_box(stats)
        })
    });

    // --- Pop Back Benchmark ---
    c.bench_function("pvec_pop_back", |b| {
        let mut vec = PersistentVector::new();
        for i in 0..1000 {
            vec = vec.push_back(i);
        }
        b.iter(|| {
            let mut v = vec.clone();
            for _ in 0..1000 {
                v = v.pop_back().unwrap_or((v, 0)).0;
            }
            black_box(v)
        })
    });

    // --- Concat Benchmark ---
    c.bench_function("pvec_concat", |b| {
        let v1 = (0..500).fold(PersistentVector::new(), |v, i| v.push_back(i));
        let v2 = (500..1000).fold(PersistentVector::new(), |v, i| v.push_back(i));
        b.iter(|| {
            let merged = v1.concat(&v2);
            black_box(merged)
        })
    });

    // --- Split Benchmark ---
    c.bench_function("pvec_split_at", |b| {
        let vec = (0..1000).fold(PersistentVector::new(), |v, i| v.push_back(i));
        b.iter(|| {
            let (left, right) = vec.split_at(500);
            black_box((left, right))
        })
    });
}
