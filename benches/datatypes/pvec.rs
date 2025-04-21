use criterion::{black_box, Criterion};
#[cfg(feature = "pvec")]
use rustica::pvec::{pvec, PersistentVector};

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
}
