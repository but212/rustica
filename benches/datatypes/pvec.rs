use criterion::Criterion;
#[cfg(feature = "pvec")]
use rustica::pvec::PersistentVector;
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
}
