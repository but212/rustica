use criterion::Criterion;
use rustica::context;
use rustica::error::with_context_result;
use std::hint::black_box;

pub fn lazy_error_benchmarks(c: &mut Criterion) {
    let mut group = c.benchmark_group("LazyError");

    group.bench_function("happy_path_lazy", |b| {
        b.iter(|| {
            let result: Result<i32, &str> = Ok(42);
            black_box(with_context_result(result, context!("step {} failed", 1)))
        });
    });

    group.bench_function("happy_path_eager", |b| {
        b.iter(|| {
            let result: Result<i32, &str> = Ok(42);
            black_box(with_context_result(result, format!("step {} failed", 1)))
        });
    });

    group.bench_function("error_path_lazy", |b| {
        b.iter(|| {
            let result: Result<i32, &str> = Err("failed");
            black_box(with_context_result(result, context!("step {} failed", 1)))
        });
    });

    group.bench_function("error_path_eager", |b| {
        b.iter(|| {
            let result: Result<i32, &str> = Err("failed");
            black_box(with_context_result(result, format!("step {} failed", 1)))
        });
    });

    group.finish();
}
