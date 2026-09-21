use crate::harness::Harness;
use rustica::context;
use rustica::error::with_context_result;
use std::hint::black_box;

pub fn lazy_error_benchmarks(harness: &Harness) {
    let mut group = harness.benchmark_group("LazyError");

    group.bench_fn("happy_path_lazy", || {
        let result: Result<i32, &str> = Ok(black_box(42));
        let step = black_box(1);
        let _ = black_box(with_context_result(
            result,
            context!("step {} failed", step),
        ));
    });

    group.bench_fn("happy_path_eager", || {
        let result: Result<i32, &str> = Ok(black_box(42));
        let step = black_box(1);
        let _ = black_box(with_context_result(result, format!("step {} failed", step)));
    });

    group.bench_fn("error_path_lazy", || {
        let result: Result<i32, &str> = Err(black_box("failed"));
        let step = black_box(1);
        let _ = black_box(with_context_result(
            result,
            context!("step {} failed", step),
        ));
    });

    group.bench_fn("error_path_eager", || {
        let result: Result<i32, &str> = Err(black_box("failed"));
        let step = black_box(1);
        let _ = black_box(with_context_result(result, format!("step {} failed", step)));
    });
}
