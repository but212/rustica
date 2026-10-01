use crate::harness::{BenchGroup, Harness};
use rustica::context;
use rustica::error::{ContextError, context_accumulator, with_context_result};
use std::hint::black_box;

static DEPTH_COUNTS: [usize; 3] = [5, 20, 50];

fn bench_context_operations(group: &mut BenchGroup) {
    for count in [2, 3, 50] {
        group.bench_with_input("context_accumulation", &count, |&count| {
            let mut error = ContextError::new("core error");
            for index in 0..count {
                error = error.with_context(context!("context {index}"));
            }
            black_box(error);
        });

        group.bench_with_input("context_iteration", &count, |&count| {
            let mut error = ContextError::new("core error");
            for index in 0..count {
                error = error.with_context(context!("context {index}"));
            }
            black_box(error.context_iter().count());
        });
    }

    for count in [3, 50] {
        let mut error = ContextError::new("core error");
        for index in 0..count {
            error = error.with_context(context!("context {index}"));
        }
        group.bench_with_input("error_chain_formatting", &count, move |_| {
            black_box(error.error_chain());
        });
    }
}

fn bench_lazy_context(group: &mut BenchGroup) {
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

fn bench_bottlenecks_timing(group: &mut BenchGroup) {
    // 1. with_contexts batch allocation & reverse overhead
    let sample_contexts = ["layer context"; 50];
    for &count in &DEPTH_COUNTS {
        group.bench_with_input("with_contexts_batch", &count, |&count| {
            let err = ContextError::new("core error")
                .with_contexts(sample_contexts[..count].iter().copied());
            black_box(err);
        });
    }

    // 2. Static &str to_string() allocation overhead vs pre-allocated String
    group.bench_fn("with_context_str_literal", || {
        let err = ContextError::new("core error").with_context(black_box("static error context"));
        black_box(err);
    });

    let pre_allocated = String::from("preallocated error context");
    group.bench_fn("with_context_owned_string", || {
        let err = ContextError::new("core error").with_context(pre_allocated.clone());
        black_box(err);
    });

    // 3. context_accumulator invocation deep-cloning all context strings
    let accumulator = context_accumulator([
        "database connection layer",
        "sql query execution",
        "transaction coordinator",
        "connection pool checkout",
        "network socket transport",
    ]);
    group.bench_fn("context_accumulator_invoke", || {
        let err = accumulator(black_box("query timeout"));
        black_box(err);
    });
}

fn bench_bottlenecks_memory(group: &mut BenchGroup) {
    // Heap churn for with_contexts batch (50 items)
    let contexts: Vec<&'static str> = (0..50).map(|_| "diagnostic context layer").collect();
    group.bench_memory(
        "mem_with_contexts_batch_50",
        || (),
        |_| {
            let err = ContextError::new("core error").with_contexts(contexts.iter().copied());
            black_box(err);
        },
    );

    // Heap churn for context_accumulator reuse
    let accumulator = context_accumulator([
        "database connection layer",
        "sql query execution",
        "transaction coordinator",
        "connection pool checkout",
        "network socket transport",
    ]);
    group.bench_memory(
        "mem_context_accumulator_invoke",
        || (),
        |_| {
            let err = accumulator("query timeout");
            black_box(err);
        },
    );

    // Heap churn for error_chain formatting (50 layers)
    let mut err = ContextError::new("core error");
    for _ in 0..50 {
        err = err.with_context("diagnostic context layer");
    }
    group.bench_memory(
        "mem_error_chain_formatting_50",
        || err.clone(),
        |state| {
            black_box(state.error_chain());
        },
    );
}

pub fn context_error_benchmarks(harness: &Harness) {
    let mut group = harness.benchmark_group("ContextError");
    bench_context_operations(&mut group);
    bench_lazy_context(&mut group);
    bench_bottlenecks_timing(&mut group);
    bench_bottlenecks_memory(&mut group);
}
