use crate::harness::Harness;
use rustica::context;
use rustica::error::ContextError;
use std::hint::black_box;

pub fn composable_error_benchmarks(harness: &Harness) {
    let mut group = harness.benchmark_group("ContextError");

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
        group.bench_with_input("error_chain_formatting", &count, |&count| {
            let mut error = ContextError::new("core error");
            for index in 0..count {
                error = error.with_context(context!("context {index}"));
            }
            black_box(error.error_chain());
        });
    }
}
