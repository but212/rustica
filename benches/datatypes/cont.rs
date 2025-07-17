use criterion::Criterion;
use rustica::datatypes::cont::Cont;
use std::hint::black_box;
use std::sync::Arc;

pub fn cont_benchmarks(c: &mut Criterion) {
    let mut group = c.benchmark_group("Cont");

    // Creation benchmarks
    group.bench_function("cont_return_cont", |b| {
        b.iter(|| {
            let cont: Cont<i32, i32> = Cont::return_cont(black_box(42));
            black_box(cont)
        })
    });

    group.bench_function("cont_new", |b| {
        b.iter(|| {
            let cont = Cont::new(|k: Arc<dyn Fn(i32) -> i32 + Send + Sync>| k(black_box(42)));
            black_box(cont)
        })
    });

    group.bench_function("cont_pure", |b| {
        b.iter(|| {
            let cont: Cont<i32, i32> = Cont::pure(black_box(42));
            black_box(cont)
        })
    });

    // Functor benchmarks
    group.bench_function("cont_fmap", |b| {
        b.iter(|| {
            let cont: Cont<i32, i32> = Cont::return_cont(black_box(10));
            let result = cont.fmap(|x| x * 2);
            black_box(result)
        })
    });

    // Applicative benchmarks
    group.bench_function("cont_apply", |b| {
        b.iter(|| {
            let cont_val: Cont<i32, i32> = Cont::return_cont(black_box(10));
            let cont_fn: Cont<i32, Arc<dyn Fn(i32) -> i32 + Send + Sync>> = Cont::return_cont(
                Arc::new(|x: i32| x * 2) as Arc<dyn Fn(i32) -> i32 + Send + Sync>,
            );
            let result = cont_val.apply(cont_fn);
            black_box(result)
        })
    });

    // Monad benchmarks
    group.bench_function("cont_bind", |b| {
        b.iter(|| {
            let cont: Cont<i32, i32> = Cont::return_cont(black_box(10));
            let result = cont.bind(|x| Cont::return_cont(x * 2));
            black_box(result)
        })
    });

    // Run benchmarks
    group.bench_function("cont_run", |b| {
        b.iter(|| {
            let cont: Cont<i32, i32> = Cont::return_cont(black_box(42));
            let result = cont.run(|x| x * 2);
            black_box(result)
        })
    });

    group.bench_function("cont_run_complex", |b| {
        b.iter(|| {
            let cont: Cont<i32, i32> = Cont::return_cont(black_box(10))
                .fmap(|x| x + 5)
                .bind(|x| Cont::return_cont(x * 2));
            let result = cont.run(|x| x + 1);
            black_box(result)
        })
    });

    // Call/cc benchmarks
    group.bench_function("cont_call_cc", |b| {
        b.iter(|| {
            let cont: Cont<i32, i32> = Cont::return_cont(black_box(5)).call_cc(|exit| {
                if black_box(true) {
                    exit(10)
                } else {
                    Cont::return_cont(5)
                }
            });
            black_box(cont)
        })
    });

    group.bench_function("cont_call_cc_run", |b| {
        b.iter(|| {
            let cont: Cont<i32, i32> = Cont::return_cont(black_box(5)).call_cc(|exit| {
                if black_box(true) {
                    exit(10)
                } else {
                    Cont::return_cont(5)
                }
            });
            let result = cont.run(|x| x);
            black_box(result)
        })
    });

    // Chaining benchmarks
    group.bench_function("cont_chain_operations", |b| {
        b.iter(|| {
            let cont: Cont<i32, i32> = Cont::return_cont(black_box(1))
                .fmap(|x| x + 1)
                .bind(|x| Cont::return_cont(x * 2))
                .fmap(|x| x + 3);
            black_box(cont)
        })
    });

    group.bench_function("cont_chain_and_run", |b| {
        b.iter(|| {
            let cont: Cont<i32, i32> = Cont::return_cont(black_box(1))
                .fmap(|x| x + 1)
                .bind(|x| Cont::return_cont(x * 2))
                .fmap(|x| x + 3);
            let result = cont.run(|x| x);
            black_box(result)
        })
    });

    group.finish();
}
